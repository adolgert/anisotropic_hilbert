import AnisoHilbert.Step

namespace AnisoHilbert

/-!
Embedding (activation) and full multi-level encode/decode loops.

This mirrors the high-level structure described in `discrete_proof.md`:

* levels `s = mmax, …, 1`
* active axis lists `A_s = activeAxes m s`
* per-level step: `packPlane → T → gcInv → state update`
* activation embedding: embed `(e,d)` from `A_s` to `A_{s-1}`.

For now we represent the Hilbert index as a list of variable-width digits
`Σ k, BV k` (one digit per level).  This keeps the loop computable without
committing yet to a single `Fin (2^M)` or `BitVec M` representation.
-/

namespace Embed

/-! ### Embedding operators -/

/--
Embed a `BV` defined on an older active-axis list `Aold` into a newer list `Anew`.

For each axis in `Anew`, copy the corresponding bit if that axis exists in `Aold`,
otherwise fill `false`.

This is the "copy shared axes, zero newly activated axes" rule from §3.2/3.3. fileciteturn0file0L96-L104
-/
def embedBV {n : Nat} (Aold Anew : List (Axis n)) (x : BV Aold.length) : BV Anew.length :=
  fun j =>
    let ax := Anew.get j
    match pos? Aold ax with
    | none => false
    | some i => x i

/--
Embed a per-level state from `Aold` into `Anew`.

* entry mask `e` is embedded with `embedBV`
* direction is preserved as a *physical axis* by reindexing `st.dirAxis` inside `Anew`.

If the direction axis is not found in `Anew`, return `none`.

Note: we build the resulting state with `State.mk'`, so `dirAxis` is *defined* as
`Anew.get dPos'`. A later lemma will show this equals `st.dirAxis` whenever the
lookup succeeds.
-/
def embedState? {n : Nat} (Aold Anew : List (Axis n)) (st : State n Aold) : Option (State n Anew) :=
  let e' : BV Anew.length := embedBV Aold Anew st.e
  match pos? Anew st.dirAxis with
  | none => none
  | some dPos' =>
      some (State.mk' (A := Anew) (e := e') (dPos := dPos'))

end Embed

/-! ### Variable-width digit representation of the Hilbert index -/

abbrev Digit := Σ k : Nat, BV k
abbrev Digits := List Digit

/-! ### Initialization helpers -/

/--
Initial per-level state for an active-axis list `A`, corresponding to
Hamilton's `(e,d) = (0,0)`.

If `A` is empty we return `none`.
-/
def initState? {n : Nat} (A : List (Axis n)) : Option (State n A) :=
  if h : 0 < A.length then
    let dPos : Fin A.length := ⟨0, h⟩
    some (State.mk' (A := A) (e := BV.zero) (dPos := dPos))
  else
    none

/-- Maximum exponent `mmax = max_j m_j`. -/
def mMax {n : Nat} (m : Exponents n) : Nat :=
  (allAxes n).foldl (fun acc j => Nat.max acc (m j)) 0

/-! ### State update from a digit `w` (shared by encode/decode) -/

def stateUpdate {n : Nat} (A : List (Axis n)) (st : State n A) (w : BV A.length) : State n A :=
  let wNat : Nat := BV.toNat w
  let e' : BV A.length :=
    BV.xor st.e (BV.rotL (st.dPos.val.succ) (childEntry A.length wNat))
  let dVal : Nat := (st.dPos.val + childDir A.length wNat + 1) % A.length
  let dPos' : Fin A.length := ⟨dVal, Nat.mod_lt _ (State.length_pos st)⟩
  State.mk' (A := A) e' dPos'

/-! ### Encoding loop -/

/--
Encode starting from level `s` down to level `1`.

This returns `some` list of digits on success, otherwise `none`.
-/
def encodeFromLevel {n : Nat} {m : Exponents n} (p : PointBV m) :
    (s : Nat) → State n (activeAxes m s) → Option Digits
  | 0, _ => some []
  | Nat.succ s', st =>
      let A : List (Axis n) := activeAxes m (Nat.succ s')
      -- `st` is already a `State n A` by definitional equality.
      let step : StepOut n A := hilbertStep (A := A) st p s'
      let digit : Digit := ⟨A.length, step.w⟩
      match s' with
      | 0 => some [digit]
      | Nat.succ s'' =>
          match Embed.embedState? (Aold := A) (Anew := activeAxes m (Nat.succ s'')) step.stNext with
          | none => none
          | some st' =>
              match encodeFromLevel p (Nat.succ s'') st' with
              | none => none
              | some rest => some (digit :: rest)

/-- Top-level encoder returning a variable-width digit list. -/
def encodeDigits? {n : Nat} {m : Exponents n} (p : PointBV m) : Option Digits :=
  let s0 := mMax m
  match s0 with
  | 0 => some []
  | Nat.succ _ =>
      let A0 : List (Axis n) := activeAxes m s0
      match initState? (n := n) A0 with
      | none => none
      | some st0 => encodeFromLevel (m := m) p s0 st0

/-! ### Decoding loop -/

/-- All-zeros point in `P(m)`. -/
def pointZero {n : Nat} {m : Exponents n} : PointBV m :=
  fun _ => BV.zero

/--
Decode starting from level `s` down to level `1`, consuming one digit per level.

The digit widths are checked against the current active-axis list length.
-/
def decodeFromLevel {n : Nat} {m : Exponents n} :
    (s : Nat) → State n (activeAxes m s) → Digits → PointBV m → Option (PointBV m)
  | 0, _, ds, p =>
      -- no more levels; require no remaining digits
      match ds with
      | [] => some p
      | _ => none
  | Nat.succ s', st, ds, p =>
      let A : List (Axis n) := activeAxes m (Nat.succ s')
      match ds with
      | [] => none
      | ⟨kW, w⟩ :: rest =>
          if hk : kW = A.length then
            let w' : BV A.length := by
              cases hk
              exact w
            let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w')
            let p' : PointBV m := writePlane A l p s'
            let stNext : State n A := stateUpdate A st w'
            match s' with
            | 0 =>
                -- last level: require digits exhausted
                match rest with
                | [] => some p'
                | _ => none
            | Nat.succ s'' =>
                match Embed.embedState? (Aold := A) (Anew := activeAxes m (Nat.succ s'')) stNext with
                | none => none
                | some st' => decodeFromLevel (Nat.succ s'') st' rest p'
          else
            none

/-- Top-level decoder from variable-width digits. -/
def decodeDigits? {n : Nat} {m : Exponents n} (ds : Digits) : Option (PointBV m) :=
  let s0 := mMax m
  match s0 with
  | 0 =>
      -- Zero total precision: only the origin exists. Require `ds = []`.
      match ds with
      | [] => some (pointZero (m := m))
      | _ => none
  | Nat.succ _ =>
      let A0 : List (Axis n) := activeAxes m s0
      match initState? (n := n) A0 with
      | none => none
      | some st0 => decodeFromLevel (m := m) s0 st0 ds (pointZero (m := m))

end AnisoHilbert
