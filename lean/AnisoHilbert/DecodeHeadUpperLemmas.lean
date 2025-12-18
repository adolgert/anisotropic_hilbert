import AnisoHilbert.Loops
import AnisoHilbert.DecodeHigherPlaneLemmas

namespace AnisoHilbert

/-!
Lemmas saying that, at a fixed level, the **head digit** determines the
decoder's output on all planes **at or above** that level.

This is the bookkeeping fact used in the lattice-continuity proof sketch:

* the suffix digits only refine *inside* the chosen child subbox, so
  already-fixed higher planes are preserved.

Technically, the decoder performs

`writePlane` at plane `s` and then recurses, and the recursion is proven
(in `DecodeHigherPlaneLemmas`) to preserve all planes `≥ s`.
-/

namespace DecodeHeadUpper

open DecodePlanes

/--
If decoding from level `succ s` succeeds on a digit stream whose head digit has
the correct width, then the resulting output point `pOut` agrees with the
one-step accumulator point `p1` on all planes at indices `t.val ≥ s`.

In other words: the suffix digits can only affect planes strictly below `s`.
-/
theorem decodeFromLevel_eq_writePlane_on_ge
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (w : BV (activeAxes m (Nat.succ s)).length)
    (rest : Digits)
    (pAcc pOut : PointBV m)
    (hDec :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w⟩ :: rest) pAcc = some pOut) :
    let A : List (Axis n) := activeAxes m (Nat.succ s)
    let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w)
    let p1 : PointBV m := writePlane A l pAcc s
    ∀ (j : Axis n) (t : Fin (m j)), s ≤ t.val → pOut j t = p1 j t := by
  intro A l p1
  cases s with
  | zero =>
      -- Level = 1: successful decoding forces `rest = []`, and then `pOut = p1`.
      cases rest with
      | nil =>
          simp [decodeFromLevel, A, l, p1] at hDec
          cases hDec
          intro j t ht
          rfl
      | cons d rest' =>
          -- With leftover digits at the last level, the decoder returns `none`.
          simp [decodeFromLevel, A, l, p1] at hDec
  | succ s' =>
      -- Recursive case: after writing plane `succ s'`, the recursive decoder
      -- preserves all planes `≥ succ s'` from the accumulator `p1`.
      let stNext : State n A := stateUpdate (A := A) st w
      simp [decodeFromLevel, A, l, p1, stNext] at hDec
      split at hDec
      · -- embedding failure would make the result `none`
        exact Option.noConfusion hDec
      · rename_i st' hEmb
        -- In this branch, `hDec` is exactly the recursive decoding equality.
        have hRec :
            decodeFromLevel (m := m) (Nat.succ s') st' rest p1 = some pOut := hDec
        -- Apply the "preserves higher planes" lemma to the recursive call.
        intro j t ht
        exact
          DecodePlanes.decodeFromLevel_preserves_ge (m := m)
            (s := Nat.succ s') (st := st') (ds := rest)
            (pAcc := p1) (pOut := pOut) hRec j t ht

/--
Two successful decodes from level `succ s` with the same head digit `w` and the
same accumulator agree on all planes at indices `t.val ≥ s`.
-/
theorem decodeFromLevel_same_head_eq_on_ge
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (w : BV (activeAxes m (Nat.succ s)).length)
    (rest₁ rest₂ : Digits)
    (pAcc pOut₁ pOut₂ : PointBV m)
    (hDec₁ :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w⟩ :: rest₁) pAcc = some pOut₁)
    (hDec₂ :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w⟩ :: rest₂) pAcc = some pOut₂) :
    ∀ (j : Axis n) (t : Fin (m j)), s ≤ t.val → pOut₁ j t = pOut₂ j t := by
  -- Both points agree with the same `p1` on planes `≥ s`.
  let A : List (Axis n) := activeAxes m (Nat.succ s)
  let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w)
  let p1 : PointBV m := writePlane A l pAcc s
  intro j t ht
  have h₁ : pOut₁ j t = p1 j t :=
    (decodeFromLevel_eq_writePlane_on_ge (m := m) (s := s) (st := st)
      (w := w) (rest := rest₁) (pAcc := pAcc) (pOut := pOut₁) hDec₁) j t ht
  have h₂ : pOut₂ j t = p1 j t :=
    (decodeFromLevel_eq_writePlane_on_ge (m := m) (s := s) (st := st)
      (w := w) (rest := rest₂) (pAcc := pAcc) (pOut := pOut₂) hDec₂) j t ht
  exact h₁.trans h₂.symm

end DecodeHeadUpper

end AnisoHilbert
