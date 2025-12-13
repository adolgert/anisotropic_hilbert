import AnisoHilbert.Loops
import AnisoHilbert.Lemma41

namespace AnisoHilbert

/-!
Level-indexed statements that mirror the structure of Theorem 4.4 in `discrete_proof.md`.

This file is intended to be the next “bridge” layer:

* prove the one-step decoding identity at a fixed level (uses Lemma 4.1), and
* state the full level-indexed encode/decode inversion lemma for later induction.

We keep the main induction proof as a skeleton for now; the hard sub-lemmas
needed are:

1. correctness of `writePlane` against `packPlane` (requires `pos?`/`get` facts and
   `Nodup` of active axis lists), and
2. totality of activation embedding for consecutive `activeAxes` lists.
-/

namespace Level

/--
Overwrite bits strictly below level `s` (i.e. bit indices `< s`) from `src` into `dst`.

This is the natural “accumulator invariant” for level-indexed decoding:
`decodeFromLevel s …` should overwrite exactly planes `0 .. s-1`.
-/
def overwriteBelow {n : Nat} {m : Exponents n} (dst src : PointBV m) (s : Nat) : PointBV m :=
  fun j =>
    fun t => if t.val < s then src j t else dst j t

/-- One-step plane reconstruction lemma (Lemma 4.1 instantiated to `hilbertStep`). -/
theorem decodePlane_of_hilbertStep
    {n : Nat} {m : Exponents n}
    (A : List (Axis n)) (st : State n A) (p : PointBV m) (i : Nat) :
    Tinv st.e st.dPos.val (BV.gc (hilbertStep (A := A) st p i).w) =
      (hilbertStep (A := A) st p i).l := by
  -- Lemma 4.1 says: Tinv e d (gc (gcInv (T e d l))) = l.
  have h := BV.PhiInv_Phi (k := A.length) (e := st.e) (d := st.dPos.val) (l := packPlane A p i)
  -- `hilbertStep` defines `.l = packPlane …` and `.w = gcInv (T … (.l))`.
  simpa [BV.Phi, BV.PhiInv, hilbertStep] using h

/--
The state update computed by `hilbertStep` matches the shared `stateUpdate` helper
used by the full encode/decode loops.
-/
theorem hilbertStep_stateUpdate
    {n : Nat} {m : Exponents n}
    (A : List (Axis n)) (st : State n A) (p : PointBV m) (i : Nat) :
    (hilbertStep (A := A) st p i).stNext =
      stateUpdate (A := A) st (hilbertStep (A := A) st p i).w := by
  -- This is definitional: both sides compute the same expressions.
  simp [hilbertStep, stateUpdate]

/--
Level-indexed inversion statement (Theorem 4.4 “by induction on levels”, but with
an explicit accumulator via `overwriteBelow`).

This is the next target lemma; proof will be by induction on `s`.
-/
theorem decodeFromLevel_encodeFromLevel
    {n : Nat} {m : Exponents n} (pAcc p : PointBV m) :
    ∀ s : Nat, ∀ st : State n (activeAxes m s), ∀ ds : Digits,
      encodeFromLevel (m := m) p s st = some ds →
      decodeFromLevel (m := m) s st ds pAcc = some (overwriteBelow pAcc p s) := by
  intro s
  induction s with
  | zero =>
      intro st ds hEnc
      -- `encodeFromLevel p 0 _ = some []` and `decodeFromLevel 0 _ [] pAcc = some pAcc`.
      -- Also `overwriteBelow pAcc p 0 = pAcc` (nothing is below level 0).
      simp only [encodeFromLevel] at hEnc
      cases hEnc
      simp only [decodeFromLevel]
      congr 1
  | succ s ih =>
      intro st ds hEnc
      -- Next steps for this branch:
      -- 1. unfold `encodeFromLevel` at `Nat.succ s` to expose the head digit `w` and recursive digits
      -- 2. unfold `decodeFromLevel` similarly
      -- 3. use `decodePlane_of_hilbertStep` to identify the reconstructed plane
      -- 4. relate `writePlane` + `packPlane` to `overwriteBelow` (needs list/pos lemmas)
      -- 5. show activation embedding succeeds for `activeAxes m (s+1) ⊆ activeAxes m s`
      -- 6. apply the induction hypothesis `ih`.
      sorry

end Level

end AnisoHilbert
