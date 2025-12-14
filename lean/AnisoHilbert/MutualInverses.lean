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
  | cons x xs ih =>
      -- membership split
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · -- a = x
        -- f x ≤ max init (f x) ≤ foldl … (max init (f x)) xs
        have h₁ : f x ≤ Nat.max init (f x) := Nat.le_max_right _ _
        have h₂ : Nat.max init (f x) ≤ xs.foldl (fun acc y => Nat.max acc (f y)) (Nat.max init (f x)) :=
          le_foldl_max (f := f) (init := Nat.max init (f x)) xs
        simpa [List.foldl] using Nat.le_trans h₁ h₂
      · -- a ∈ xs
        -- foldl on cons reduces to tail foldl with updated init
        simpa [List.foldl] using ih (init := Nat.max init (f x)) (a := a) hmem'

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
  cases hmj
  -- now `p j : BV 0`, so extensionality closes (there are no indices)
  funext t
  exact t.elim0

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
      -- Unfold `encodeDigits?` to obtain the initial state and the level-encoding equality.
      have hEnc' :
          match initState? (n := n) (activeAxes m (Nat.succ s0)) with
          | none => none
          | some st0 => encodeFromLevel (m := m) p (Nat.succ s0) st0
          = some ds := by
        simpa [encodeDigits?, hS] using h
      -- Case split on `initState?`.
      cases hInit : initState? (n := n) (activeAxes m (Nat.succ s0)) with
      | none =>
          -- Contradiction: encoder cannot be `none` if it equals `some ds`.
          simp [hInit] at hEnc'
      | some st0 =>
          -- Extract the per-level encoding equation.
          have hEncLevel : encodeFromLevel (m := m) p (Nat.succ s0) st0 = some ds := by
            simpa [hInit] using hEnc'
          -- Apply the level-indexed lemma with accumulator `pointZero`.
          have hDecLevel :
              decodeFromLevel (m := m) (Nat.succ s0) st0 ds (pointZero (m := m)) =
                some (overwriteBelow (pointZero (m := m)) p (Nat.succ s0)) :=
            Level.decodeFromLevel_encodeFromLevel (m := m) (p := p)
              (s := Nat.succ s0) (pAcc := pointZero (m := m)) (st := st0) (ds := ds) hEncLevel
          -- `overwriteBelow pointZero p (mMax m) = p` because `m j ≤ mMax m` for all axes.
          have hOw : overwriteBelow (pointZero (m := m)) p (Nat.succ s0) = p := by
            exact overwriteBelow_eq_src_of_ge (dst := pointZero (m := m)) (p := p) (s := Nat.succ s0)
              (hs := fun j => by
                -- `Nat.succ s0 = mMax m` by `hS`.
                have : m j ≤ mMax m := le_mMax (m := m) j
                simpa [hS] using this)
          -- Finish by unfolding the top-level decoder and rewriting.
          simpa [decodeDigits?, hS, hInit, hOw] using hDecLevel

end Mutual

end AnisoHilbert
