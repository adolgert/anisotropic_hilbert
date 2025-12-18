import AnisoHilbert.Loops
import AnisoHilbert.PlaneReadWriteLemmas

namespace AnisoHilbert

/-!
Lemmas stating that the decoder only overwrites the *lower* bit-planes.

Informally:
* `decodeFromLevel s …` writes planes `0,1,…,s-1` and **preserves** all planes `≥ s`.

This is the bookkeeping fact typically used in the encode-after-decode direction:
when decoding continues to lower levels, it does not disturb planes already fixed
at higher levels.
-/

namespace DecodePlanes

/--
`decodeFromLevel` does not modify any plane at bit-index `t.val ≥ s`.

Equivalently: decoding from level `s` only overwrites planes strictly below `s`.
-/
theorem decodeFromLevel_preserves_ge
    {n : Nat} {m : Exponents n} :
    ∀ (s : Nat) (st : State n (activeAxes m s)) (ds : Digits)
      (pAcc pOut : PointBV m),
      decodeFromLevel (m := m) s st ds pAcc = some pOut →
      ∀ (j : Axis n) (t : Fin (m j)), s ≤ t.val → pOut j t = pAcc j t := by
  intro s
  induction s with
  | zero =>
      intro st ds pAcc pOut hDec j t ht
      cases ds with
      | nil =>
          -- `decodeFromLevel 0 _ [] pAcc = some pAcc`.
          simp [decodeFromLevel] at hDec
          cases hDec
          rfl
      | cons d rest =>
          -- `decodeFromLevel 0 _ (_::_) _ = none`.
          simp [decodeFromLevel] at hDec
  | succ s ih =>
      intro st ds pAcc pOut hDec j t ht
      cases ds with
      | nil =>
          -- `decodeFromLevel (succ _) _ [] _ = none`.
          simp [decodeFromLevel] at hDec
      | cons d rest =>
          rcases d with ⟨kW, w⟩
          let A : List (Axis n) := activeAxes m (Nat.succ s)
          by_cases hk : kW = A.length
          ·
            -- Follow the successful (width-matching) branch.
            let w' : BV A.length := by
              cases hk
              exact w
            let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w')
            let p1 : PointBV m := writePlane A l pAcc s
            let stNext : State n A := stateUpdate (A := A) st w'

            -- Split on whether this is the last level (`s = 0`) or a recursive level (`s = succ _`).
            cases s with
            | zero =>
                -- Level `1`: decoder returns `some p1` iff `rest = []`.
                cases hk
                cases rest with
                | nil =>
                    -- Simplify: decodeFromLevel 1 st [⟨A.length, w⟩] pAcc = some p1
                    simp [decodeFromLevel, A, w', l, p1, stNext] at hDec
                    -- hDec is now p1 = pOut
                    rw [← hDec]
                    -- Goal: p1 j t = pAcc j t
                    have hne : t.val ≠ 0 := Nat.one_le_iff_ne_zero.mp ht
                    exact PlaneRW.writePlane_ne A l pAcc 0 j t hne
                | cons d2 rest2 =>
                    simp [decodeFromLevel, A, w', l, p1, stNext] at hDec
            | succ s' =>
                -- Recursive level: embed must succeed and then we recurse.
                cases hk
                simp [decodeFromLevel, A, w', l, p1, stNext] at hDec
                -- hDec is now about the match on embedState?
                -- Split on the embedState? match.
                split at hDec
                · -- embedState? = none: contradicts hDec = some pOut
                  exact Option.noConfusion hDec
                · -- embedState? = some stRec
                  rename_i stRec hEmb
                  -- hDec : decodeFromLevel (succ s') stRec rest p1 = some pOut
                  -- Apply IH: preservation at planes ≥ succ s'.
                  have hIH : pOut j t = p1 j t := ih stRec rest p1 pOut hDec j t (Nat.le_of_succ_le ht)
                  -- Apply writePlane_ne: p1 j t = pAcc j t since t.val ≠ succ s'.
                  have hne : t.val ≠ Nat.succ s' := Nat.ne_of_gt (Nat.lt_of_succ_le ht)
                  have hWP : p1 j t = pAcc j t := PlaneRW.writePlane_ne A l pAcc (Nat.succ s') j t hne
                  exact hIH.trans hWP
          ·
            -- Width mismatch implies the decoder returns `none`.
            simp [decodeFromLevel, A, hk] at hDec

/--
Corollary: if `decodeFromLevel s …` succeeds, then *packing* any plane `i ≥ s`
from the output equals packing it from the accumulator.
-/
theorem packPlane_decodeFromLevel_preserves_ge
    {n : Nat} {m : Exponents n}
    (A : List (Axis n)) :
    ∀ (s : Nat) (st : State n (activeAxes m s)) (ds : Digits)
      (pAcc pOut : PointBV m) (i : Nat),
      s ≤ i →
      decodeFromLevel (m := m) s st ds pAcc = some pOut →
      packPlane A pOut i = packPlane A pAcc i := by
  intro s st ds pAcc pOut i hi hDec
  funext t
  let j : Axis n := A.get t
  by_cases hij : i < m j
  ·
    have hbit : pOut j ⟨i, hij⟩ = pAcc j ⟨i, hij⟩ :=
      decodeFromLevel_preserves_ge (m := m)
        (s := s) (st := st) (ds := ds) (pAcc := pAcc) (pOut := pOut) hDec
        (j := j) (t := ⟨i, hij⟩) hi
    simp only [packPlane, j, getBit, dif_pos hij]
    exact hbit
  ·
    -- Out of range: both sides read as `false`.
    simp only [packPlane, j, getBit, dif_neg hij]

end DecodePlanes

end AnisoHilbert
