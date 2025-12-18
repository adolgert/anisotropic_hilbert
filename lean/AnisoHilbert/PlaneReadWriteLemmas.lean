import AnisoHilbert.ActiveAxesLemmas

namespace AnisoHilbert

/-!
Lemmas for the **right-inverse** direction of Theorem 4.4 (encode after decode).

Key concrete fact:

*If you write a packed plane `l` into plane `i` along an axis-list `A`, then
packing that same plane back out along `A` returns `l`.*

This is the “read-after-write” companion to the accumulator seam lemma.
-/

namespace PlaneRW

open ListLemmas
open Pos
open ActiveAxes

/-- Writing a bit at index `i` and then reading bit `i` returns the written bit. -/
theorem getBit_setBit_same {len : Nat} (x : BV len) (i : Nat) (b : Bool) (hi : i < len) :
    getBit (setBit x i b) i = b := by
  -- `getBit` selects the `⟨i,hi⟩` entry, and `setBit` changes exactly that entry.
  simp [getBit, setBit, hi]

/-- Writing a bit at index `i` does not change any other index `j ≠ i`. -/
theorem getBit_setBit_ne {len : Nat} (x : BV len) (i j : Nat) (b : Bool)
    (hj : j < len) (hne : j ≠ i) :
    getBit (setBit x i b) j = getBit x j := by
  simp [getBit, setBit, hj, hne]

/-- `writePlane` changes only plane `i`: at any `t.val ≠ i`, the coordinate is unchanged. -/
theorem writePlane_ne
    {n : Nat} {m : Exponents n}
    (A : List (Axis n)) (l : BV A.length) (p : PointBV m) (i : Nat)
    (j : Axis n) (t : Fin (m j)) (hne : t.val ≠ i) :
    (writePlane A l p i j) t = p j t := by
  cases hpos : pos? A j with
  | none =>
      simp [writePlane, hpos]
  | some tj =>
      -- In this branch: `writePlane` = `setBit`.
      simp [writePlane, hpos, setBit, hne]

/--
General read-after-write for a fixed axis list `A`.

Assumptions:
* `A` is `Nodup`, so `pos? A (A.get t) = some t`.
* plane `i` exists for every active axis (`i < m (A.get t)`).

Conclusion:
* Packing plane `i` after writing `l` into plane `i` yields exactly `l`.
-/
theorem packPlane_writePlane_same
    {n : Nat} {m : Exponents n}
    (A : List (Axis n)) (p : PointBV m) (l : BV A.length) (i : Nat)
    (hnd : A.Nodup)
    (hi : ∀ t : Fin A.length, i < m (A.get t)) :
    packPlane A (writePlane A l p i) i = l := by
  funext t
  let j := A.get t
  have hpos : pos? A j = some t := by
    simpa [j] using (Pos.pos?_get_of_nodup (xs := A) hnd t)
  have hij : i < m j := by
    -- rewrite `j` into the hypothesis `hi`
    simpa [j] using (hi t)

  -- First prove the pointwise read-after-write statement at axis `j`.
  have hbit : getBit (writePlane A l p i j) i = l t := by
    -- Reduce `writePlane` using `pos? A j = some t`, but orient the equality so that
    -- simp can rewrite `setBit …` into `writePlane …`.
    have hw : setBit (p j) i (l t) = writePlane A l p i j := by
      -- `writePlane … j` is definitionally a `match` on `pos? A j`.
      -- With `hpos : pos? A j = some t`, the match reduces to the `setBit` branch.
      simp [writePlane, hpos]
    -- Now it's exactly `getBit (setBit _ i (l t)) i = l t`.
    simpa [hw] using (getBit_setBit_same (x := p j) (i := i) (b := l t) hij)

  -- Finally, `packPlane` at index `t` reads that same bit from axis `j`.
  simpa [packPlane, j] using hbit

theorem packPlane_writePlane_activeAxes
    {n : Nat} {m : Exponents n}
    (p : PointBV m) (i : Nat) (l : BV (activeAxes m (Nat.succ i)).length) :
    let A := activeAxes m (Nat.succ i)
    packPlane A (writePlane A l p i) i = l := by
  intro A
  have hnd : A.Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ i)
  have hi : ∀ t : Fin A.length, i < m (A.get t) := by
    intro t
    -- `A.get t ∈ A` and membership in `activeAxes` gives `Nat.succ i ≤ m (A.get t)`.
    have hjmem : A.get t ∈ A := ListLemmas.get_mem (xs := A) t
    have hs : Nat.succ i ≤ m (A.get t) :=
      (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ i) (j := A.get t)).1 hjmem |>.2
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hs
  exact packPlane_writePlane_same (A := A) (p := p) (l := l) (i := i) hnd hi

end PlaneRW

end AnisoHilbert
