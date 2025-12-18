import AnisoHilbert.Loops
import AnisoHilbert.PlaneReadWriteLemmas
import AnisoHilbert.DecodeHigherPlaneLemmas

namespace AnisoHilbert

/-!
Facts about what the decoder "writes" at a given level.

These lemmas are the continuity-side counterpart of the extraction steps used in
`EncodeAfterDecode.lean`.

The main reusable fact is: if `decodeFromLevel (succ s)` succeeds on a digit stream
whose head digit is width-correct, then in the final output point the packed plane
`s` (with respect to the active axes `activeAxes m (succ s)`) equals

    `Tinv st.e st.dPos.val (gc w)`

for that head digit `w`.

The proof pattern is:

* define `p1 := writePlane …` for the head level,
* use `DecodePlanes.packPlane_decodeFromLevel_preserves_ge` to show recursion
  does not change plane `s`, and
* finish with the read-after-write lemma `PlaneRW.packPlane_writePlane_activeAxes`.
-/

namespace DecodeHead

open PlaneRW
open DecodePlanes

/-
At level `succ s`, the axis list used by the decoder for this level is
`A := activeAxes m (succ s)`.

We state the lemma with an explicit `w : BV A.length` so we do not have to
thread the width-cast case split through later proofs.
-/

/--
If decoding from level `succ s` succeeds on a width-correct head digit `w`, then
the resulting point's packed plane `s` (over the active axes at that level)
is exactly the reconstructed word `Tinv … (gc w)`.
-/
theorem packPlane_decodeFromLevel_head
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (w : BV (activeAxes m (Nat.succ s)).length)
    (rest : Digits)
    (pAcc pOut : PointBV m)
    (hDec :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w⟩ :: rest) pAcc = some pOut) :
    packPlane (activeAxes m (Nat.succ s)) pOut s =
      Tinv st.e st.dPos.val (BV.gc w) := by
  -- Split on whether this is the last level (s = 0) or a true recursive level.
  cases s with
  | zero =>
      -- Level = 1. The decoder succeeds only if `rest = []`.
      cases rest with
      | nil =>
          -- Unfold the decoder; the result is exactly the one-step write.
          -- After `simp`, `hDec` becomes `some p' = some pOut`.
          simp [decodeFromLevel] at hDec
          cases hDec
          -- Now `pOut` is definitionally `writePlane …`.
          -- Read-after-write gives the packed plane.
          simpa [decodeFromLevel] using
            (PlaneRW.packPlane_writePlane_activeAxes (m := m)
              (p := pAcc) (i := 0)
              (l := Tinv st.e st.dPos.val (BV.gc w)))
      | cons d rest' =>
          -- With leftover digits at the last level, the decoder returns `none`.
          simp [decodeFromLevel] at hDec
  | succ s' =>
      -- True recursion: after writing plane `succ s'`, the recursive call
      -- writes only planes `< succ s'`, so the just-written plane is preserved.
      let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s'))
      let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w)
      let p1 : PointBV m := writePlane A l pAcc (Nat.succ s')
      let stNext : State n A := stateUpdate (A := A) st w

      -- Unfold one step of the decoder; the only successful branch is the
      -- embedding-success branch.
      simp [decodeFromLevel, A, l, p1, stNext] at hDec
      split at hDec
      · -- `embedState? = none` would make the result `none`.
        exact Option.noConfusion hDec
      · rename_i st' hEmb
        -- In this branch, `hDec` is exactly the recursive decoding equality.
        have hRec :
            decodeFromLevel (m := m) (Nat.succ s') st' rest p1 = some pOut := by
          exact hDec

        -- Recursion preserves plane `succ s'`.
        have hPres :
            packPlane A pOut (Nat.succ s') = packPlane A p1 (Nat.succ s') :=
          DecodePlanes.packPlane_decodeFromLevel_preserves_ge (m := m) (A := A)
            (s := Nat.succ s') (st := st') (ds := rest)
            (pAcc := p1) (pOut := pOut)
            (i := Nat.succ s') (Nat.le_refl _) hRec

        -- Read-after-write on `p1`.
        have hPackP1 : packPlane A p1 (Nat.succ s') = l := by
          simpa [A, p1] using
            (PlaneRW.packPlane_writePlane_activeAxes (m := m)
              (p := pAcc) (i := Nat.succ s') (l := l))

        -- Combine preservation with read-after-write.
        have hPack : packPlane A pOut (Nat.succ s') = l := hPres.trans hPackP1
        -- Discharge the goal by unfolding the local names.
        simpa [A, l] using hPack

end DecodeHead

end AnisoHilbert
