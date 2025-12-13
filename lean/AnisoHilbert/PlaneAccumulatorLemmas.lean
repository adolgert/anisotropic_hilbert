import AnisoHilbert.EmbedLemmas

namespace AnisoHilbert

/-!
Lemmas relating `writePlane (packPlane …)` to the accumulator-style invariant
used in the level-indexed proof.

We avoid importing `LevelIndexed.lean` here to prevent module cycles.
So we state the main lemma as an equality of the underlying point-functions
(the two sides are exactly `overwriteBelow` with different thresholds).
-/

namespace Plane

open ListLemmas
open ActiveAxes
open Pos

/-- Every axis appears in `allAxes n`. -/
theorem mem_allAxes {n : Nat} (j : Axis n) : j ∈ allAxes n := by
  -- `allAxes n` is `List.finRange n`.
  -- Std provides `List.mem_finRange` as the membership characterization.
  simpa [allAxes] using (List.mem_finRange j)

/-- If bit-plane `i` exists on axis `j` (`i < m j`), then `j` is active at level `i+1`. -/
theorem mem_activeAxes_of_lt {n : Nat} (m : Exponents n) (i : Nat) (j : Axis n) (h : i < m j) :
    j ∈ activeAxes m (Nat.succ i) := by
  have hall : j ∈ allAxes n := mem_allAxes (n := n) j
  have hs : Nat.succ i ≤ m j := Nat.succ_le_of_lt h
  exact (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ i) (j := j)).2 ⟨hall, hs⟩

/--
Main accumulator lemma (stated without naming `overwriteBelow`).

Let `A = activeAxes m (i+1)`.

If we first write plane `i` from `p` into an accumulator `pAcc` (but only along
active axes), and then later overwrite all lower planes `< i` from `p`, the net
result is exactly “overwrite all planes `< i+1` from `p`” relative to `pAcc`.

This is the precise seam between the *current* level write and the *recursive*
accumulator invariant in the successor step of the level-indexed induction.
-/
theorem overwriteBelow_writePlane_packPlane_activeAxes
    {n : Nat} {m : Exponents n}
    (pAcc p : PointBV m) (i : Nat) :
    let A : List (Axis n) := activeAxes m (Nat.succ i)
    (fun j => fun t => if t.val < i then p j t else (writePlane A (packPlane A p i) pAcc i j) t)
      =
    (fun j => fun t => if t.val < Nat.succ i then p j t else pAcc j t) := by
  intro A
  funext j
  funext t
  by_cases htlt : t.val < i
  · -- Below plane `i`: both sides are `p`.
    have hltSucc : t.val < Nat.succ i := Nat.lt_trans htlt (Nat.lt_succ_self i)
    simp [htlt, hltSucc]
  · have htge : i ≤ t.val := Nat.le_of_not_gt htlt
    by_cases hteq : t.val = i
    · -- At plane `i`: this bit exists (`i < m j`), hence axis `j` is active and gets written.
      have hi : i < m j := by
        simpa [hteq] using t.isLt
      have hj : j ∈ A := mem_activeAxes_of_lt (m := m) (i := i) (j := j) hi
      rcases Pos.pos?_some_of_mem (xs := A) (a := j) hj with ⟨tj, htj⟩
      have hget : A.get tj = j := Pos.get_of_pos?_some (xs := A) (a := j) (i := tj) htj
      have hwrite : (writePlane A (packPlane A p i) pAcc i j) t = p j t := by
        -- Reduce `writePlane` using the `pos?` witness.
        have hw1 : (writePlane A (packPlane A p i) pAcc i j) t = (packPlane A p i) tj := by
          simp [writePlane, htj, setBit, hteq]
        -- Rewrite `packPlane` using `A.get tj = j`.
        have hp1 : (packPlane A p i) tj = getBit (p j) i := by
          simp only [packPlane]
          -- Goal: getBit (p (A.get tj)) i = getBit (p j) i
          rw [hget]
        -- Identify `getBit (p j) i` with the actual bit at `t`.
        have hFin : (⟨i, hi⟩ : Fin (m j)) = t := by
          apply Fin.ext
          simp [hteq]
        have hgb : getBit (p j) i = (p j) ⟨i, hi⟩ := by
          simp [getBit, hi]
        have hgb' : getBit (p j) i = p j t := by
          simp [hFin, hgb]
        calc
          (writePlane A (packPlane A p i) pAcc i j) t
              = (packPlane A p i) tj := hw1
          _ = getBit (p j) i := hp1
          _ = p j t := hgb'
      have hltSucc : t.val < Nat.succ i := by
        simpa [hteq] using (Nat.lt_succ_self i)
      simp [htlt, hltSucc, hwrite]
    · -- Above plane `i`: the write touches only plane `i`, so this bit is unchanged from `pAcc`.
      have htgt : i < t.val := Nat.lt_of_le_of_ne htge (Ne.symm hteq)
      have hsuccle : Nat.succ i ≤ t.val := Nat.succ_le_of_lt htgt
      have hnotltSucc : ¬ t.val < Nat.succ i := Nat.not_lt_of_ge hsuccle
      have htne : t.val ≠ i := hteq
      have hwrite : (writePlane A (packPlane A p i) pAcc i j) t = pAcc j t := by
        cases hpos : pos? A j with
        | none =>
            simp [writePlane, hpos]
        | some tj =>
            -- `setBit` only changes the bit at index `i`.
            simp [writePlane, hpos, setBit, htne]
      simp [htlt, hnotltSucc, hwrite]

end Plane

end AnisoHilbert
