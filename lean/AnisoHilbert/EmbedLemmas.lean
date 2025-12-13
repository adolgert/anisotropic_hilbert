import AnisoHilbert.Loops
import AnisoHilbert.ActiveAxesLemmas

namespace AnisoHilbert

/-!
Lemmas about the activation / embedding operators from `Loops.lean`.

The next two proof obligations in `LevelIndexed.lean` need:

1. **Physical-axis preservation**: embedding preserves `dirAxis` (the *axis label*),
   while recomputing `dPos` relative to the new axis list.
2. **Totality for consecutive levels**: when `Aold = activeAxes m (s+1)` and
   `Anew = activeAxes m s`, the embedding lookup can never fail.

We keep the statements phrased in terms of `embedState?` / `embedBV`, so they
can be reused by both the encode and decode loops.
-/

namespace Pos

open ListLemmas

/-- If `a ∈ xs`, then `pos? xs a` is `some i` for some index `i`.

This is the forward direction of “`pos?` detects membership”.  We prove it
by structural recursion so we don't depend on a particular Std lemma name.
-/
theorem pos?_some_of_mem {α : Type} [DecidableEq α] :
    ∀ {xs : List α} {a : α}, a ∈ xs → ∃ i : Fin xs.length, pos? xs a = some i
  | [], a, hmem => by
      cases hmem
  | x :: xs, a, hmem => by
      rcases List.mem_cons.mp hmem with hax | hmem'
      · -- `a = x` and we can witness position `0`.
        subst hax
        refine ⟨⟨0, by simp⟩, ?_⟩
        simp [pos?]
      · -- `a ∈ xs` (the tail). If `a = x` we still witness position `0`.
        by_cases hx : a = x
        · subst hx
          refine ⟨⟨0, by simp⟩, ?_⟩
          simp [pos?]
        · rcases pos?_some_of_mem (xs := xs) (a := a) hmem' with ⟨i, hi⟩
          refine ⟨⟨i.val.succ, Nat.succ_lt_succ i.isLt⟩, ?_⟩
          simp [pos?, hx, hi]

/-- If `pos? xs a = some i`, then `a ∈ xs`. -/
theorem mem_of_pos?_some {α : Type} [DecidableEq α]
    (xs : List α) (a : α) (i : Fin xs.length) (h : pos? xs a = some i) : a ∈ xs := by
  have hget : xs.get i = a := get_of_pos?_some (xs := xs) (a := a) (i := i) h
  have hmem : xs.get i ∈ xs := ListLemmas.get_mem (xs := xs) i
  rw [hget] at hmem
  exact hmem

end Pos

namespace Embed

open ListLemmas
open Pos

/-- `embedBV` copies the old bit when the axis is present in `Aold`. -/
theorem embedBV_of_pos?_some {n : Nat}
    (Aold Anew : List (Axis n))
    (x : BV Aold.length)
    (j : Fin Anew.length)
    (i : Fin Aold.length)
    (h : pos? Aold (Anew.get j) = some i) :
    embedBV Aold Anew x j = x i := by
  simp only [embedBV]
  -- Goal: match pos? Aold Anew[↑j] with | none => false | some i => x i = x i
  -- Anew.get j = Anew[↑j] definitionally
  simp only [h]

/-- `embedBV` yields `false` on a newly-activated axis (absent from `Aold`). -/
theorem embedBV_of_pos?_none {n : Nat}
    (Aold Anew : List (Axis n))
    (x : BV Aold.length)
    (j : Fin Anew.length)
    (h : pos? Aold (Anew.get j) = none) :
    embedBV Aold Anew x j = false := by
  simp only [embedBV]
  simp only [h]

/-- If `embedState?` succeeds, then the *physical axis* `dirAxis` is preserved.

This is the key “treat `d` as an axis label, not a raw index” fix.
-/
theorem embedState?_dirAxis_eq {n : Nat}
    (Aold Anew : List (Axis n))
    (st : State n Aold)
    {st' : State n Anew}
    (h : embedState? (Aold := Aold) (Anew := Anew) st = some st') :
    st'.dirAxis = st.dirAxis := by
  -- Unfold the definition and expose the successful `pos?` lookup.
  unfold embedState? at h
  -- `embedState?` branches on `pos? Anew st.dirAxis`.
  cases hpos : pos? Anew st.dirAxis with
  | none =>
      -- In this branch the result is `none`, contradicting `h`.
      simp [hpos] at h
  | some dPos' =>
      -- In this branch the result is `some (State.mk' ...)`.
      -- First, identify `st'` with that constructor.
      have hst' : st' = State.mk' (A := Anew)
          (e := embedBV Aold Anew st.e)
          (dPos := dPos') := by
        -- Reduce the `match` using `hpos`, then peel `some`.
        have := (Option.some.inj (by simpa [hpos] using h))
        exact this.symm
      -- Now the direction axis of the embedded state is `Anew.get dPos'`.
      -- And `pos? Anew st.dirAxis = some dPos'` implies `Anew.get dPos' = st.dirAxis`.
      have hget : Anew.get dPos' = st.dirAxis :=
        get_of_pos?_some (xs := Anew) (a := st.dirAxis) (i := dPos') hpos
      -- Rewrite by `hst'` and finish.
      subst hst'
      -- `State.mk'` defines `dirAxis := Anew.get dPos'`.
      simpa [State.mk', hget]

/-- If `embedState?` succeeds, the embedded direction *position* points to the same axis.

This lemma is often more convenient than `embedState?_dirAxis_eq` when you want to
avoid rewriting with `State.mk'`.
-/
theorem embedState?_dir_ok {n : Nat}
    (Aold Anew : List (Axis n))
    (st : State n Aold)
    {st' : State n Anew}
    (h : embedState? (Aold := Aold) (Anew := Anew) st = some st') :
    Anew.get st'.dPos = st.dirAxis := by
  have hAxis : st'.dirAxis = st.dirAxis := embedState?_dirAxis_eq (Aold := Aold) (Anew := Anew) st h
  -- `st'.dir_ok : Anew.get st'.dPos = st'.dirAxis`.
  simpa [hAxis] using st'.dir_ok

/-- Totality: embedding between consecutive active-axis lists can never fail.

This is the “activation embedding consistency” existence fact used by the
level-indexed induction.
-/
theorem embedState?_activeAxes_succ_some {n : Nat}
    (m : Exponents n) (s : Nat)
    (st : State n (activeAxes m (Nat.succ s))) :
    ∃ st' : State n (activeAxes m s),
      embedState? (Aold := activeAxes m (Nat.succ s)) (Anew := activeAxes m s) st = some st' := by
  -- `st.dirAxis` is in `Aold` because it is the axis at position `st.dPos`.
  have hmem_old : st.dirAxis ∈ activeAxes m (Nat.succ s) := by
    have hmem : (activeAxes m (Nat.succ s)).get st.dPos ∈ activeAxes m (Nat.succ s) :=
      ListLemmas.get_mem (xs := activeAxes m (Nat.succ s)) st.dPos
    rw [st.dir_ok] at hmem
    exact hmem
  -- Monotone activation gives membership in `Anew`.
  have hmem_new : st.dirAxis ∈ activeAxes m s :=
    ActiveAxes.mem_activeAxes_of_mem_activeAxes_succ (m := m) (s := s) (j := st.dirAxis) hmem_old
  -- Therefore `pos? Anew st.dirAxis` is `some`.
  rcases Pos.pos?_some_of_mem (xs := activeAxes m s) (a := st.dirAxis) hmem_new with ⟨dPos', hdPos'⟩
  refine ⟨State.mk' (A := activeAxes m s) (e := embedBV (activeAxes m (Nat.succ s)) (activeAxes m s) st.e) (dPos := dPos'), ?_⟩
  -- Reduce `embedState?` using `hdPos'`.
  simp [embedState?, hdPos']

end Embed

end AnisoHilbert
