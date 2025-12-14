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
          cases hDec
  | succ s ih =>
      intro st ds pAcc pOut hDec j t ht
      cases ds with
      | nil =>
          -- `decodeFromLevel (succ _) _ [] _ = none`.
          simp [decodeFromLevel] at hDec
          cases hDec
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
                -- Our preservation threshold is `1 ≤ t.val`.
                simp [decodeFromLevel, A, hk, w', l, p1, stNext] at hDec
                cases rest with
                | nil =>
                    simp at hDec
                    cases hDec
                    -- Since `1 ≤ t.val`, we have `t.val ≠ 0`, so plane-0 write doesn't affect `t`.
                    have hne : t.val ≠ 0 := by
                      -- `0 < t.val` follows from `0 < 1 ≤ t.val`.
                      exact (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) ht)).symm
                    -- `writePlane` only changes plane `0`.
                    simpa [p1] using
                      (PlaneRW.writePlane_ne (A := A) (l := l) (p := pAcc) (i := 0) (j := j) (t := t) hne)
                | cons d2 rest2 =>
                    -- If there are leftover digits, the decoder would be `none`.
                    simp at hDec
                    cases hDec
            | succ s' =>
                -- Recursive level: embed must succeed and then we recurse.
                simp [decodeFromLevel, A, hk, w', l, p1, stNext] at hDec
                split at hDec
                · -- embedState? = none: impossible under `= some pOut`.
                  cases hDec
                · rename_i st' hEmb
                  -- Successful recursive call.
                  have hRec : decodeFromLevel (m := m) (Nat.succ s') st' rest p1 = some pOut := by
                    exact hDec
                  -- Weaken the threshold from `succ (succ s')` to `succ s'` to use the IH.
                  have ht' : Nat.succ s' ≤ t.val := by
                    exact Nat.le_trans (Nat.le_succ (Nat.succ s')) ht
                  have hPres : pOut j t = p1 j t :=
                    ih (st := st') (ds := rest) (pAcc := p1) (pOut := pOut) hRec j t ht'
                  -- Show `p1` agrees with `pAcc` at `t` (since `t.val ≥ succ (succ s')` so `t.val ≠ succ s'`).
                  have hne : t.val ≠ Nat.succ s' := by
                    have hlt : Nat.succ s' < t.val :=
                      Nat.lt_of_lt_of_le (Nat.lt_succ_self (Nat.succ s')) ht
                    exact (Nat.ne_of_gt hlt).symm
                  have hWrite : p1 j t = pAcc j t := by
                    simpa [p1] using
                      (PlaneRW.writePlane_ne (A := A) (l := l) (p := pAcc) (i := Nat.succ s') (j := j) (t := t) hne)
                  exact hPres.trans hWrite
          ·
            -- Width mismatch implies the decoder returns `none`.
            simp [decodeFromLevel, A, hk] at hDec
            cases hDec

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
    simpa [packPlane, j, getBit, hij] using hbit
  ·
    -- Out of range: both sides read as `false`.
    simp [packPlane, j, getBit, hij]

end DecodePlanes

end AnisoHilbert
