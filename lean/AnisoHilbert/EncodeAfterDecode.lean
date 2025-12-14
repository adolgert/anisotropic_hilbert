
import AnisoHilbert.Loops
import AnisoHilbert.Lemma41
import AnisoHilbert.PlaneReadWriteLemmas
import AnisoHilbert.DecodeHigherPlaneLemmas

namespace AnisoHilbert

/-!
Right-inverse direction (“encode after decode”) for the variable-width digit loop.

At the per-level core, decoding writes plane `i` from the digit `w` via

  l := Φ⁻¹(e,d)(w) = Tinv(e,d)(gc(w))
  p' := writePlane A l pAcc i

and then recurses to lower levels.  The key is:

1) recursion preserves the just-written higher plane (DecodeHigherPlaneLemmas), and
2) reading that plane back out yields the same packed word `l` (PlaneReadWriteLemmas),
3) applying Φ(e,d) to `l` returns `w` (Lemma 4.1 / `Phi_PhiInv`).

We package this as a level-indexed lemma and then lift it to the top-level wrappers
`encodeDigits?` / `decodeDigits?`.
-/

namespace LevelRight

open PlaneRW
open DecodePlanes

/--
A definitional convenience: `hilbertStep`'s `stNext` agrees with `stateUpdate`
from `Loops.lean` (both are Hamilton Algorithm-2 lines 5–7).
-/
theorem hilbertStep_stateUpdate
    {n : Nat} {m : Exponents n}
    (A : List (Axis n)) (st : State n A) (p : PointBV m) (i : Nat) :
    (hilbertStep (A := A) st p i).stNext =
      stateUpdate (A := A) st (hilbertStep (A := A) st p i).w := by
  simp [hilbertStep, stateUpdate]

/--
If decoding from level `s` succeeds, then re-encoding from the same level and state
recovers exactly the same digit list.
-/
theorem encodeFromLevel_of_decodeFromLevel
    {n : Nat} {m : Exponents n} :
    ∀ (s : Nat) (st : State n (activeAxes m s)) (ds : Digits)
      (pAcc pOut : PointBV m),
      decodeFromLevel (m := m) s st ds pAcc = some pOut →
      encodeFromLevel (m := m) pOut s st = some ds := by
  intro s
  induction s with
  | zero =>
      intro st ds pAcc pOut hDec
      cases ds with
      | nil =>
          simp [decodeFromLevel] at hDec
          cases hDec
          simp [encodeFromLevel]
      | cons d rest =>
          -- `decodeFromLevel 0 _ (d::rest) _ = none`
          simp [decodeFromLevel] at hDec
          cases hDec
  | succ s ih =>
      intro st ds pAcc pOut hDec
      cases ds with
      | nil =>
          -- `decodeFromLevel (succ _) _ [] _ = none`
          simp [decodeFromLevel] at hDec
          cases hDec
      | cons d rest =>
          rcases d with ⟨kW, w⟩
          let A : List (Axis n) := activeAxes m (Nat.succ s)

          by_cases hk : kW = A.length
          ·
            -- Successful width branch: cast `w` to `BV A.length`.
            cases hk
            have hk' : kW = A.length := rfl

            let w' : BV A.length := w
            let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w')
            let p1 : PointBV m := writePlane A l pAcc s
            let stNext : State n A := stateUpdate (A := A) st w'

            cases s with
            | zero =>
                -- Last level: decoder succeeds iff `rest = []` and output is `p1`.
                simp [decodeFromLevel, A, w', l, p1, stNext] at hDec
                cases rest with
                | nil =>
                    simp at hDec
                    cases hDec

                    -- Read-after-write: packed plane at `0` is exactly `l`.
                    have hPack : packPlane A p1 0 = l := by
                      simpa [A, p1] using
                        (PlaneRW.packPlane_writePlane_activeAxes (m := m) (p := pAcc) (i := 0) (l := l))

                    -- Therefore Φ(e,d)(packPlane …) = w'.
                    have hw : (hilbertStep (A := A) st p1 0).w = w' := by
                      -- `Phi_PhiInv` : Φ(Φ⁻¹(w)) = w
                      have hΦ : BV.Phi st.e st.dPos.val (BV.PhiInv st.e st.dPos.val w') = w' :=
                        BV.Phi_PhiInv (e := st.e) (d := st.dPos.val) (w := w')
                      -- Rewrite `packPlane` as `PhiInv … w'` via `hPack`.
                      have hPlane : packPlane A p1 0 = BV.PhiInv st.e st.dPos.val w' := by
                        simpa [BV.PhiInv, l] using hPack
                      -- Unfold `hilbertStep` and finish.
                      simpa [hilbertStep, BV.Phi, hPlane] using hΦ

                    -- Encode at level `1` produces exactly `[⟨A.length, w'⟩]`.
                    simp [encodeFromLevel, A, hw]
                | cons d2 rest2 =>
                    -- With leftover digits, the decoder branch is `none`.
                    simp at hDec
                    cases hDec
            | succ s' =>
                -- Recursive case: decoder wrote plane `succ s'` and then recursed.
                simp [decodeFromLevel, A, w', l, p1, stNext] at hDec
                split at hDec
                · -- embedState? = none contradicts success
                  cases hDec
                · rename_i st' hEmb
                  have hRec : decodeFromLevel (m := m) (Nat.succ s') st' rest p1 = some pOut := by
                    exact hDec

                  -- IH: encoding from the recursive level recovers `rest`.
                  have hEncRec :
                      encodeFromLevel (m := m) pOut (Nat.succ s') st' = some rest :=
                    ih (st := st') (ds := rest) (pAcc := p1) (pOut := pOut) hRec

                  -- Recursion preserves the just-written plane `succ s'` (i.e. plane index `s`).
                  have hPackEq :
                      packPlane A pOut (Nat.succ s') = packPlane A p1 (Nat.succ s') :=
                    DecodePlanes.packPlane_decodeFromLevel_preserves_ge (m := m) (A := A)
                      (s := Nat.succ s') (st := st') (ds := rest)
                      (pAcc := p1) (pOut := pOut) (i := Nat.succ s') (Nat.le_rfl) hRec

                  -- Read-after-write on `p1`.
                  have hPackP1 : packPlane A p1 (Nat.succ s') = l := by
                    simpa [A, p1] using
                      (PlaneRW.packPlane_writePlane_activeAxes (m := m) (p := pAcc) (i := Nat.succ s') (l := l))

                  have hPack : packPlane A pOut (Nat.succ s') = l := by
                    exact hPackEq.trans hPackP1

                  -- Therefore Φ(e,d)(packPlane …) = w'.
                  have hw : (hilbertStep (A := A) st pOut (Nat.succ s')).w = w' := by
                    have hΦ : BV.Phi st.e st.dPos.val (BV.PhiInv st.e st.dPos.val w') = w' :=
                      BV.Phi_PhiInv (e := st.e) (d := st.dPos.val) (w := w')
                    have hPlane : packPlane A pOut (Nat.succ s') = BV.PhiInv st.e st.dPos.val w' := by
                      simpa [BV.PhiInv, l] using hPack
                    simpa [hilbertStep, BV.Phi, hPlane] using hΦ

                  -- Align the embedded state with the decoder's embedded state.
                  have hStepNext : (hilbertStep (A := A) st pOut (Nat.succ s')).stNext = stNext := by
                    have hDef :
                        (hilbertStep (A := A) st pOut (Nat.succ s')).stNext =
                          stateUpdate (A := A) st (hilbertStep (A := A) st pOut (Nat.succ s')).w :=
                      hilbertStep_stateUpdate (m := m) (A := A) (st := st) (p := pOut) (i := Nat.succ s')
                    -- rewrite the digit equality
                    simpa [stNext, hw] using hDef

                  have hEmb' :
                      Embed.embedState? (Aold := A) (Anew := activeAxes m (Nat.succ s'))
                        (hilbertStep (A := A) st pOut (Nat.succ s')).stNext = some st' := by
                    simpa [hStepNext] using hEmb

                  -- Finish by unfolding `encodeFromLevel`.
                  simp [encodeFromLevel, A, hw, hEmb', hEncRec]
          ·
            -- Width mismatch would make the decoder `none`.
            simp [decodeFromLevel, A, hk] at hDec
            cases hDec

end LevelRight

namespace Mutual

open LevelRight

/--
Top-level right-inverse: if `decodeDigits? ds = some p`, then `encodeDigits? p = some ds`.
-/
theorem encodeDigits?_of_decodeDigits?
    {n : Nat} {m : Exponents n} (ds : Digits) (p : PointBV m) :
    decodeDigits? (m := m) ds = some p →
    encodeDigits? (m := m) p = some ds := by
  unfold decodeDigits? encodeDigits?
  cases hS : mMax m with
  | zero =>
      intro hDec
      cases ds with
      | nil =>
          -- decode succeeds only at the origin; encoder at `mMax = 0` is `[]`
          simp [hS] at hDec
          simp [hS]
      | cons d rest =>
          -- decoder is `none`, contradicting `= some p`
          simp [hS] at hDec
          cases hDec
  | succ s0 =>
      intro hDec
      let A0 : List (Axis n) := activeAxes m (Nat.succ s0)
      cases hInit : initState? (n := n) A0 with
      | none =>
          -- decoder would be `none`
          simp [hS, A0, hInit] at hDec
          cases hDec
      | some st0 =>
          -- Extract the level-decoding equation and apply the level lemma.
          have hDecLevel :
              decodeFromLevel (m := m) (Nat.succ s0) st0 ds (pointZero (m := m)) = some p := by
            simpa [hS, A0, hInit] using hDec
          have hEncLevel :
              encodeFromLevel (m := m) p (Nat.succ s0) st0 = some ds :=
            LevelRight.encodeFromLevel_of_decodeFromLevel (m := m)
              (s := Nat.succ s0) (st := st0) (ds := ds)
              (pAcc := pointZero (m := m)) (pOut := p) hDecLevel
          simpa [hS, A0, hInit] using hEncLevel
end Mutual

end AnisoHilbert
