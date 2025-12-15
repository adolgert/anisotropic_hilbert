import AnisoHilbert.Loops
import AnisoHilbert.EmbedLemmas

namespace AnisoHilbert

/-!
Totality wrappers for the encoder.

The computational loops in `Loops.lean` are written using `Option` so that

* the decoder can reject malformed digit streams, and
* intermediate “should never happen” cases (like failed embeddings) are explicit.

For the **mathematical algorithm**, however, the encoder is total:

* For any state `st` aligned with `activeAxes m s`, the activation embedding
  between consecutive levels cannot fail.
* Therefore `encodeFromLevel` and `encodeDigits?` never return `none`.

This file packages that fact into a proof-friendly, total API:

* `encodeFromLevel!` returns a `Digits` value without any `Option` wrappers.
* `encodeDigits` returns a `Digits` value without any `Option` wrappers.

The `!`-variants are `noncomputable` (they use choice), but they are
definitionally tied to the computable `Option` versions via `..._spec` lemmas.
-/

namespace Encode

open Embed

/-! ### A small list lemma: foldl/max attains its maximum on the list (or the initial value). -/

private theorem foldl_max_eq_or_exists {α : Type} (f : α → Nat) :
    ∀ (xs : List α) (init r : Nat),
      xs.foldl (fun acc x => Nat.max acc (f x)) init = r →
        init = r ∨ ∃ a ∈ xs, f a = r := by
  intro xs
  induction xs with
  | nil =>
      intro init r h
      left
      simpa [List.foldl] using h
  | cons x xs ih =>
      intro init r h
      -- foldl on cons
      have h' : xs.foldl (fun acc y => Nat.max acc (f y)) (Nat.max init (f x)) = r := by
        simpa [List.foldl] using h
      rcases ih (init := Nat.max init (f x)) (r := r) h' with hr | ⟨a, ha, hfa⟩
      · -- r = max init (f x)
        -- Either r comes from `init` or from `f x`.
        have : init = r ∨ f x = r := by
          -- `Nat.max init (f x) = r`
          -- If `init ≤ f x`, then max = f x, else max = init.
          by_cases hle : init ≤ f x
          · right
            have : Nat.max init (f x) = f x := Nat.max_eq_right hle
            -- `hr : Nat.max init (f x) = r`, so rewriting by `this` yields `f x = r`.
            exact by simpa [this] using hr
          · left
            have hle' : f x ≤ init := Nat.le_of_not_ge hle
            have : Nat.max init (f x) = init := Nat.max_eq_left hle'
            -- `hr : Nat.max init (f x) = r`, so rewriting by `this` yields `init = r`.
            exact by simpa [this] using hr
        cases this with
        | inl hin =>
            left
            exact hin
        | inr hfx =>
            right
            refine ⟨x, by simp, hfx⟩
      · -- witness in tail
        right
        refine ⟨a, ?_, hfa⟩
        simp [ha]

/-! ### `initState?` is always `some` at the top level when `mMax` is a successor. -/

private theorem activeAxes_length_pos_of_mMax_eq_succ
    {n : Nat} (m : Exponents n) (s0 : Nat) (hS : mMax m = Nat.succ s0) :
    0 < (activeAxes m (Nat.succ s0)).length := by
  -- Show that the max value is attained by some axis in `allAxes n`.
  have hAttain : ∃ j ∈ allAxes n, m j = Nat.succ s0 := by
    -- Apply the generic fold lemma to the specific `mMax` fold.
    have h0 : 0 ≠ Nat.succ s0 := (Nat.succ_ne_zero s0).symm
    -- Either the fold result equals the initial `0` or it is attained on the list.
    have hOr :=
      foldl_max_eq_or_exists (f := fun j : Axis n => m j) (xs := allAxes n) (init := 0)
        (r := Nat.succ s0) (by simpa [mMax, hS])
    rcases hOr with hEq | ⟨j, hjmem, hjEq⟩
    · -- impossible: `0 = succ s0`
      exfalso
      exact h0 (by simpa using hEq)
    · exact ⟨j, hjmem, hjEq⟩
  rcases hAttain with ⟨j, hjAll, hmj⟩
  -- That axis is active at level `succ s0`.
  have hjAct : j ∈ activeAxes m (Nat.succ s0) := by
    -- `mem_activeAxes_iff` characterizes the filter.
    have : j ∈ allAxes n ∧ Nat.succ s0 ≤ m j := by
      refine ⟨hjAll, ?_⟩
      simpa [hmj] using Nat.le_rfl
    exact (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ s0) (j := j)).2 this
  -- Hence the list is nonempty, so its length is positive.
  cases hL : activeAxes m (Nat.succ s0) with
  | nil =>
      simp [hL] at hjAct
  | cons a tail =>
      simp [hL]

/-- The per-level encoder is total: it always returns `some ds` for some `ds`. -/
theorem encodeFromLevel_exists
    {n : Nat} {m : Exponents n} (p : PointBV m) :
    ∀ (s : Nat) (st : State n (activeAxes m s)),
      ∃ ds : Digits, encodeFromLevel (m := m) p s st = some ds := by
  intro s
  induction s with
  | zero =>
      intro st
      refine ⟨[], ?_⟩
      simp [encodeFromLevel]
  | succ s ih =>
      intro st
      -- Split on whether `s = 0` (one digit) or `s = succ _` (recursive).
      cases s with
      | zero =>
          -- `encodeFromLevel p 1 st = some [digit]`.
          let A : List (Axis n) := activeAxes m 1
          let step : StepOut n A := hilbertStep (A := A) st p 0
          let digit : Digit := ⟨A.length, step.w⟩
          refine ⟨[digit], ?_⟩
          simp [encodeFromLevel, A, step, digit]
      | succ s' =>
          -- Recursive case: after producing the head digit, the embedding into the
          -- next active-axis list is guaranteed to succeed.
          let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s'))
          let step : StepOut n A := hilbertStep (A := A) st p (Nat.succ s')
          let digit : Digit := ⟨A.length, step.w⟩
          -- Totality of embedding between consecutive activeAxes lists.
          rcases Embed.embedState?_activeAxes_succ_some (m := m) (s := Nat.succ s') (st := step.stNext)
            with ⟨st', hEmb⟩
          -- IH on the remaining levels.
          rcases ih (st := st') with ⟨rest, hRec⟩
          refine ⟨digit :: rest, ?_⟩
          simp [encodeFromLevel, A, step, digit, hEmb, hRec]

/-- The top-level encoder is total: it always returns `some ds` for some `ds`. -/
theorem encodeDigits?_exists
    {n : Nat} {m : Exponents n} (p : PointBV m) :
    ∃ ds : Digits, encodeDigits? (m := m) p = some ds := by
  classical
  -- Split on `mMax m`.
  cases hS : mMax m with
  | zero =>
      refine ⟨[], ?_⟩
      simp [encodeDigits?, hS]
  | succ s0 =>
      -- Work directly with activeAxes m (mMax m) using the equality hS
      let A0 : List (Axis n) := activeAxes m (mMax m)
      -- A0 = activeAxes m (s0+1) after rewriting with hS
      have hA0 : A0 = activeAxes m (Nat.succ s0) := by
        show activeAxes m (mMax m) = activeAxes m (Nat.succ s0)
        rw [hS]
      have hlen : 0 < A0.length := by
        rw [hA0]
        exact activeAxes_length_pos_of_mMax_eq_succ (m := m) (s0 := s0) hS
      -- With `hlen`, `initState?` reduces to `some st0`.
      let st0 : State n A0 := State.mk' (A := A0) (e := BV.zero) (dPos := ⟨0, hlen⟩)
      have hInit : initState? (n := n) A0 = some st0 := by
        simp [initState?, st0, hlen]
      -- For encodeFromLevel_exists, we need st : State n (activeAxes m (s0+1))
      -- But st0 : State n A0 = State n (activeAxes m (mMax m))
      -- These are definitionally equal after simp [hS]
      have hds := encodeFromLevel_exists (m := m) (p := p) (s := mMax m) (st := st0)
      rcases hds with ⟨ds, hds⟩
      refine ⟨ds, ?_⟩
      simp only [encodeDigits?]
      -- Now split the outer match on mMax m
      split
      · -- mMax m = 0 case: impossible since hS says mMax m = s0 + 1
        rename_i hmm0
        omega
      · -- mMax m = succ _ case
        -- Now split the inner match on initState?
        split
        · -- initState? = none: contradicts hInit
          rename_i hNone
          -- hNone : initState? (activeAxes m (mMax m)) = none
          -- hInit : initState? A0 = some st0 where A0 = activeAxes m (mMax m)
          -- These contradict each other (A0 unfolds to activeAxes m (mMax m))
          exact Option.noConfusion (hNone.symm.trans hInit)
        · -- initState? = some st': use hds
          rename_i st' hSome
          -- hSome : initState? (activeAxes m (mMax m)) = some st'
          -- hInit : initState? A0 = some st0 where A0 = activeAxes m (mMax m)
          -- So st' = st0
          cases Option.some.inj (hSome.symm.trans hInit)
          exact hds

/-- A proof-friendly, total per-level encoder obtained by choice. -/
noncomputable def encodeFromLevel!
    {n : Nat} {m : Exponents n} (p : PointBV m)
    (s : Nat) (st : State n (activeAxes m s)) : Digits :=
  Classical.choose (encodeFromLevel_exists (m := m) (p := p) s st)

/-- Specification: `encodeFromLevel!` agrees with `encodeFromLevel` (as `some`). -/
theorem encodeFromLevel!_spec
    {n : Nat} {m : Exponents n} (p : PointBV m)
    (s : Nat) (st : State n (activeAxes m s)) :
    encodeFromLevel (m := m) p s st = some (encodeFromLevel! (m := m) p s st) := by
  unfold encodeFromLevel!
  simpa using (Classical.choose_spec (encodeFromLevel_exists (m := m) (p := p) s st))

/-- A proof-friendly, total top-level encoder obtained by choice. -/
noncomputable def encodeDigits
    {n : Nat} {m : Exponents n} (p : PointBV m) : Digits :=
  Classical.choose (encodeDigits?_exists (m := m) p)

/-- Specification: `encodeDigits` agrees with `encodeDigits?` (as `some`). -/
theorem encodeDigits_spec
    {n : Nat} {m : Exponents n} (p : PointBV m) :
    encodeDigits? (m := m) p = some (encodeDigits (m := m) p) := by
  unfold encodeDigits
  simpa using (Classical.choose_spec (encodeDigits?_exists (m := m) p))

end Encode

end AnisoHilbert
