import AnisoHilbert.Loops
import AnisoHilbert.LevelIndexed

namespace AnisoHilbert

/-!
Top-level theorems corresponding to Theorem 4.4 in `discrete_proof.md`:

* `decodeDigits? (encodeDigits? p) = p` (left inverse)

We prove this by lifting the level-indexed lemma from `LevelIndexed.lean` to the
initial-state wrappers `encodeDigits?` / `decodeDigits?`.

The right-inverse direction (encode after decode) will be added next; it needs
additional lemmas about `packPlane` after `writePlane` at the same level.
-/

namespace Mutual

open Level

/-- The fold used in `mMax` is an upper bound for all elements encountered. -/
lemma le_foldl_max {α : Type} (f : α → Nat) :
    ∀ (init : Nat) (xs : List α),
      init ≤ xs.foldl (fun acc x => Nat.max acc (f x)) init := by
  intro init xs
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      -- foldl on cons
      -- foldl g init (x::xs) = foldl g (max init (f x)) xs
      have h₁ : init ≤ Nat.max init (f x) := Nat.le_max_left _ _
      have h₂ : Nat.max init (f x) ≤ xs.foldl (fun acc y => Nat.max acc (f y)) (Nat.max init (f x)) :=
        ih (init := Nat.max init (f x))
      simpa [List.foldl] using Nat.le_trans h₁ h₂

/-- If `a ∈ xs`, then `f a` is bounded by the `foldl max` value over `xs`. -/
lemma foldl_max_ge_of_mem {α : Type} (f : α → Nat) :
    ∀ (init : Nat) (xs : List α) (a : α), a ∈ xs →
      f a ≤ xs.foldl (fun acc x => Nat.max acc (f x)) init := by
  intro init xs a hmem
  induction xs generalizing init with
  | nil => cases hmem
  | cons y ys ih =>
      -- membership split
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · -- a = y
        -- f a ≤ max init (f a) ≤ foldl … (max init (f a)) ys
        have h₁ : f a ≤ Nat.max init (f a) := Nat.le_max_right _ _
        have h₂ : Nat.max init (f a) ≤ ys.foldl (fun acc z => Nat.max acc (f z)) (Nat.max init (f a)) :=
          le_foldl_max (f := f) (init := Nat.max init (f a)) ys
        simpa [List.foldl] using Nat.le_trans h₁ h₂
      · -- a ∈ ys
        -- foldl on cons reduces to tail foldl with updated init
        simpa [List.foldl] using ih (init := Nat.max init (f y)) hmem'

/-- Each axis precision is bounded above by `mMax m`. -/
theorem le_mMax {n : Nat} (m : Exponents n) (j : Axis n) : m j ≤ mMax m := by
  -- `j ∈ allAxes n = finRange n`
  have hmem : j ∈ allAxes n := by
    simpa [allAxes] using (List.mem_finRange j)
  -- unfold `mMax` and apply the fold bound
  unfold mMax
  simpa using (foldl_max_ge_of_mem (f := fun a : Axis n => m a) (init := 0) (xs := allAxes n) (a := j) hmem)

/-- If `mMax m = 0` then every `PointBV m` is the origin `pointZero`. -/
theorem point_eq_pointZero_of_mMax_zero {n : Nat} {m : Exponents n}
    (h0 : mMax m = 0) (p : PointBV m) : p = pointZero (m := m) := by
  funext j
  have hmj : m j = 0 := by
    have hjle : m j ≤ mMax m := le_mMax (m := m) j
    have : m j ≤ 0 := by simpa [h0] using hjle
    exact Nat.eq_zero_of_le_zero this
  -- p j : BV (m j) and pointZero j : BV (m j)
  -- Since m j = 0, both are BV 0 which has a unique element
  funext t
  -- t : Fin (m j) = Fin 0, which is empty
  exact Fin.elim0 (hmj ▸ t)

/-- If `s` is at least every axis precision, then `overwriteBelow _ p s = p`. -/
theorem overwriteBelow_eq_src_of_ge {n : Nat} {m : Exponents n}
    (dst p : PointBV m) (s : Nat) (hs : ∀ j : Axis n, m j ≤ s) :
    overwriteBelow dst p s = p := by
  funext j
  funext t
  have ht : t.val < s := Nat.lt_of_lt_of_le t.isLt (hs j)
  simp [overwriteBelow, ht]

/-- The top-level decoder is a left inverse of the top-level encoder (Theorem 4.4, first half). -/
theorem decodeDigits?_encodeDigits?
    {n : Nat} {m : Exponents n} (p : PointBV m) (ds : Digits)
    (h : encodeDigits? (m := m) p = some ds) :
    decodeDigits? (m := m) ds = some p := by
  classical
  -- Split on the degenerate case `mMax m = 0`.
  cases hS : mMax m with
  | zero =>
      -- Encoder returns `[]`, decoder returns `pointZero`.
      have hp0 : p = pointZero (m := m) := point_eq_pointZero_of_mMax_zero (m := m) (h0 := hS) p
      -- Extract `ds = []` from `h`.
      have hds : ds = [] := by
        simpa [encodeDigits?, hS] using h
      subst hds
      -- Decode and rewrite by `hp0`.
      simp [decodeDigits?, hS, hp0]
  | succ s0 =>
      -- Work with activeAxes m (mMax m) directly
      let A0 : List (Axis n) := activeAxes m (mMax m)
      have hA0 : A0 = activeAxes m (Nat.succ s0) := by
        show activeAxes m (mMax m) = activeAxes m (Nat.succ s0)
        rw [hS]
      -- Case split on `initState?`.
      cases hInit : initState? (n := n) A0 with
      | none =>
          -- Contradiction: encoder would return `none`, but `h` says it's `some ds`.
          exfalso
          simp only [encodeDigits?] at h
          split at h
          · -- mMax m = 0: contradicts hS
            rename_i hmm0
            omega
          · -- mMax m = succ _
            split at h
            · -- initState? = none: h says none = some ds, contradiction
              exact Option.noConfusion h
            · -- initState? = some _: but hInit says it's none
              rename_i st' hSome
              exact Option.noConfusion (hSome.symm.trans hInit)
      | some st0 =>
          -- Extract the per-level encoding equation.
          have hEncLevel : encodeFromLevel (m := m) p (mMax m) st0 = some ds := by
            simp only [encodeDigits?] at h
            split at h
            · -- mMax m = 0: contradicts hS
              rename_i hmm0
              omega
            · -- mMax m = succ _
              split at h
              · -- initState? = none: contradicts hInit
                rename_i hNone
                exact Option.noConfusion (hNone.symm.trans hInit)
              · -- initState? = some st'
                rename_i st' hSome
                cases Option.some.inj (hSome.symm.trans hInit)
                exact h
          -- Apply the level-indexed lemma with accumulator `pointZero`.
          have hDecLevel :
              decodeFromLevel (m := m) (mMax m) st0 ds (pointZero (m := m)) =
                some (overwriteBelow (pointZero (m := m)) p (mMax m)) :=
            Level.decodeFromLevel_encodeFromLevel (m := m) (p := p)
              (s := mMax m) (pAcc := pointZero (m := m)) (st := st0) (ds := ds) hEncLevel
          -- `overwriteBelow pointZero p (mMax m) = p` because `m j ≤ mMax m` for all axes.
          have hOw : overwriteBelow (pointZero (m := m)) p (mMax m) = p := by
            exact overwriteBelow_eq_src_of_ge (dst := pointZero (m := m)) (p := p) (s := mMax m)
              (hs := fun j => le_mMax (m := m) j)
          -- Finish by unfolding the top-level decoder and using split
          simp only [decodeDigits?]
          split
          · -- mMax m = 0: contradicts hS
            rename_i hmm0
            omega
          · -- mMax m = succ _
            split
            · -- initState? = none: contradicts hInit
              rename_i hNone
              exact Option.noConfusion (hNone.symm.trans hInit)
            · -- initState? = some st'
              rename_i st' hSome
              cases Option.some.inj (hSome.symm.trans hInit)
              simp only [hOw] at hDecLevel
              exact hDecLevel

end Mutual

end AnisoHilbert
