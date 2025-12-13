import AnisoHilbert.Representation

namespace AnisoHilbert

/-!
Per-level state + a single Algorithm-2 style step.

This file adds just enough structure to mirror Hamilton's HilbertIndex loop:

  packPlane → T(e,d) → gc⁻¹ → state update (e,d)

See Algorithm 2 in Hamilton (2006), lines 3–7. fileciteturn0file0

We intentionally stop at “one step”; the full encoder/decoder and activation
embedding will be layered on top once this compiles cleanly.
-/

namespace BV

/-- All-zeros bitvector. -/
def zero {k : Nat} : BV k :=
  fun _ => false

/-- Interpret the low `k` bits of a natural number as a `BV k` (LSB = bit 0). -/
def ofNat {k : Nat} (x : Nat) : BV k :=
  fun i => Nat.testBit x i.val

/-- Convert a `BV k` to a natural number, interpreting index `i` as bit `i` (LSB-first). -/
def toNat {k : Nat} (x : BV k) : Nat :=
  (List.finRange k).foldl
    (fun acc i => if x i then acc + Nat.shiftLeft 1 i.val else acc)
    0

/-- Logical shift-right by 1: bit `i` becomes prior bit `i+1`. -/
def shr1 {k : Nat} (x : BV k) : BV k :=
  fun i => getBit x (i.val + 1)

/-- Binary reflected Gray code, acting on bitvectors:
`gc(x) = x XOR (x >> 1)` (Theorem 2.1). fileciteturn0file0L1-L7 -/
def gc {k : Nat} (x : BV k) : BV k :=
  xor x (shr1 x)

/-- XOR of bits `start .. k-1` (inclusive), treating out-of-range as `false`.

This is the boolean form of Hamilton's Gray inverse relation
`bit(i,j) = Σ_{k=j}^{m-1} bit(gc(i),k) mod 2` (Theorem 2.2). fileciteturn0file0L1-L7 -/
def suffixXor {k : Nat} (g : BV k) (start : Nat) : Bool :=
  if h : start < k then
    bxor (getBit g start) (suffixXor g (start + 1))
  else
    false
termination_by k - start
decreasing_by
  -- if `start < k` then `k - (start+1) < k - start`
  have hpos : 0 < k - start := Nat.sub_pos_of_lt h
  have hlt : (k - start) - 1 < (k - start) :=
    Nat.sub_lt_self (Nat.succ_pos 0) hpos
  -- rewrite `k - (start + 1)` as `(k - start) - 1`
  have hrew : k - (start + 1) = (k - start) - 1 := by
    simpa [Nat.succ_eq_add_one] using (Nat.sub_succ k start)
  simpa [hrew] using hlt

/-- Inverse of the binary reflected Gray code on `BV k`.
Returns the (binary) bitvector whose Gray encoding is `g`. (Theorem 2.2). fileciteturn0file0L1-L7 -/
def gcInv {k : Nat} (g : BV k) : BV k :=
  fun i => suffixXor g i.val

end BV

/-- Trailing set bits: number of trailing `1` bits in the binary representation.

Hamilton uses this as `tsb` and proves `g(i) = tsb(i)` for Gray-code change axis (Lemma 2.3). fileciteturn0file0L1-L9 -/
def tsb (x : Nat) : Nat :=
  if x % 2 = 1 then
    Nat.succ (tsb (x / 2))
  else
    0
termination_by x
decreasing_by
  -- In the recursive branch we have `x % 2 = 1`, hence `x ≠ 0`, hence `0 < x`.
  have hx0 : x ≠ 0 := by
    intro h0
    subst h0
    simp at *
  have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
  -- Therefore `x / 2 < x`.
  simpa using Nat.div_lt_self hxpos (by decide : 1 < 2)

/-- Child entry point `e(w)` for a `k`-dimensional Hilbert cube (Theorem 2.10).
Returns a `k`-bit word in the *standard* orientation. fileciteturn0file0L1-L12 -/
def childEntry (k : Nat) (w : Nat) : BV k :=
  if w = 0 then
    BV.zero
  else
    let j := 2 * ((w - 1) / 2)
    BV.gc (BV.ofNat (k := k) j)

/-- Child intra-direction `d(w)` for a `k`-dimensional Hilbert cube (Theorem 2.9).
Returns a natural number intended to be interpreted modulo `k`. fileciteturn0file0L1-L9 -/
def childDir (k : Nat) (w : Nat) : Nat :=
  if w = 0 then
    0
  else if w % 2 = 0 then
    (tsb (w - 1)) % k
  else
    (tsb w) % k

/-- Per-level orientation state for a chosen ordered active-axis list `A`.

We store both:
* `dPos : Fin A.length` (the local direction index, used for rotation counts), and
* `dirAxis : Axis n` with a proof it matches the axis at `dPos`.

Later, when the active-axis list changes (activation), `dirAxis` is the quantity
that should be preserved; `dPos` is recomputed relative to the new list.
-/
structure State (n : Nat) (A : List (Axis n)) where
  e : BV A.length
  dPos : Fin A.length
  dirAxis : Axis n
  dir_ok : A.get dPos = dirAxis

namespace State

/-- Convenience constructor: choose `dirAxis` to be the axis at `dPos`. -/
def mk' {n : Nat} {A : List (Axis n)} (e : BV A.length) (dPos : Fin A.length) : State n A :=
  { e := e
  , dPos := dPos
  , dirAxis := A.get dPos
  , dir_ok := rfl }

/-- `A.length > 0` follows from the existence of a `Fin A.length` value. -/
theorem length_pos {n : Nat} {A : List (Axis n)} (st : State n A) : 0 < A.length := by
  have hlt : st.dPos.val < A.length := st.dPos.isLt
  have hne : A.length ≠ 0 := by
    intro h0
    -- If `A.length = 0` then `hlt` becomes `st.dPos.val < 0`, contradiction.
    simp only [h0] at hlt
    exact Nat.not_lt_zero _ hlt
  exact Nat.pos_of_ne_zero hne

end State

/-- Output of a single HilbertIndex iteration (Algorithm 2, lines 3–7).

This record keeps the *observable* intermediate words separate from the
state update:

* `l`   : the packed bit-plane word (what we "saw" in `p` at plane `i`)
* `lT`  : the transformed word `T(e,d)(l)`
* `w`   : the child index at this level, `gc⁻¹(lT)`
* `stNext` : the updated orientation state after descending into child `w`

Keeping `l`/`lT` around is useful in later lemmas, e.g. to relate plane
extraction to Gray-code adjacency independently of the state transition.
-/
structure StepOut (n : Nat) (A : List (Axis n)) where
  l : BV A.length
  lT : BV A.length
  w : BV A.length
  stNext : State n A

namespace StepOut

/-- Convenience: interpret the `w` field as a natural number. -/
def wNat {n : Nat} {A : List (Axis n)} (s : StepOut n A) : Nat :=
  BV.toNat s.w

end StepOut

/-- One iteration of Hamilton's HilbertIndex update (Algorithm 2, lines 3–7),
generalized to a chosen ordered active-axis list `A`.

Input:
* `A` : active axes at this level (ordered)
* `st` : current (e,d) orientation state for this level
* `p` : the point whose bit-plane we are extracting
* `i` : bit-plane index

Output:
* `w` : the (binary) child index at this level
* `st'` : updated orientation state after descending into child `w`
-/
def hilbertStep {n : Nat} {m : Exponents n}
    (A : List (Axis n)) (st : State n A) (p : PointBV m) (i : Nat)
    : StepOut n A :=
  let l : BV A.length := packPlane A p i
  let lT : BV A.length := T st.e st.dPos.val l
  let w : BV A.length := BV.gcInv lT
  let wNat : Nat := BV.toNat w
  let e' : BV A.length :=
    BV.xor st.e (BV.rotL (st.dPos.val.succ) (childEntry A.length wNat))
  let dVal : Nat := (st.dPos.val + childDir A.length wNat + 1) % A.length
  let dPos' : Fin A.length := ⟨dVal, Nat.mod_lt _ (State.length_pos st)⟩
  { l := l
  , lT := lT
  , w := w
  , stNext := State.mk' (A := A) e' dPos' }

end AnisoHilbert
