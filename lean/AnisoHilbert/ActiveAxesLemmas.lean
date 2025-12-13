import AnisoHilbert.Representation

namespace AnisoHilbert

/-!
Lemmas about

* membership preservation under `insertByKey` / `sortByKey`,
* the list-position operator `pos?`, and
* the ordered active-axis lists `A_s = activeAxes m s`.

These are the bookkeeping facts needed to formalize the “ordered active axes”
layer of the discrete proof. fileciteturn1file2L45-L63
-/

namespace ListLemmas

/-- A `get` element is a member of the list. (We prove this instead of relying on library names.) -/
theorem get_mem {α : Type} :
    ∀ {xs : List α} (i : Fin xs.length), xs.get i ∈ xs
  | [], i => by
      cases i with
      | mk v hv =>
        cases hv
  | x :: xs, ⟨0, _⟩ => by
      simp
  | x :: xs, ⟨Nat.succ k, hk⟩ => by
      have hmem : xs.get ⟨k, Nat.lt_of_succ_lt_succ hk⟩ ∈ xs :=
        get_mem (xs := xs) ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      -- `get` at `k+1` in a cons list is `get` at `k` in the tail.
      simpa using (List.mem_cons_of_mem x (by simpa using hmem))

/-- Membership in `insertByKey` is exactly “new element or old membership”. -/
theorem mem_insertByKey {α : Type} (key : α → Nat) (a x : α) :
    ∀ xs : List α, x ∈ insertByKey key a xs ↔ x = a ∨ x ∈ xs
  | [] => by
      simp [insertByKey]
  | b :: bs => by
      by_cases h : key a ≤ key b
      · -- inserted before `b`
        simp [insertByKey, h, or_left_comm, or_assoc, or_comm]
      · -- inserted somewhere in the tail
        have ih := mem_insertByKey (xs := bs)
        simp [insertByKey, h, ih, or_left_comm, or_assoc, or_comm]

/-- `sortByKey` is a permutation in the weak sense that it preserves membership. -/
theorem mem_sortByKey {α : Type} (key : α → Nat) (x : α) :
    ∀ xs : List α, x ∈ sortByKey key xs ↔ x ∈ xs
  | [] => by
      simp [sortByKey]
  | a :: as => by
      have ih := mem_sortByKey (xs := as)
      -- `sortByKey` = insert into sorted tail.
      simp [sortByKey, mem_insertByKey, ih, or_left_comm, or_assoc, or_comm]

/-- `filter` preserves nodup. (We avoid depending on a particular Std lemma name.) -/
theorem nodup_filter {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, xs.Nodup → (xs.filter p).Nodup
  | [], _ => by
      simp
  | x :: xs, hnd => by
      have hx : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hxs : xs.Nodup := (List.nodup_cons.mp hnd).2
      by_cases hp : p x
      · -- keep `x`
        have hx' : x ∉ xs.filter p := by
          intro hmem
          have : x ∈ xs := (List.mem_filter.mp hmem).1
          exact hx this
        simp only [List.filter, hp, ↓reduceIte]
        exact List.nodup_cons.mpr ⟨hx', nodup_filter p hxs⟩
      · -- drop `x`
        simp only [List.filter, hp, ↓reduceIte, Bool.false_eq_true]
        exact nodup_filter p hxs

/-- `insertByKey` preserves nodup if you insert something not already present. -/
theorem nodup_insertByKey {α : Type} [DecidableEq α] (key : α → Nat) (a : α) :
    ∀ {xs : List α}, xs.Nodup → a ∉ xs → (insertByKey key a xs).Nodup
  | [], _hnd, _hnmem => by
      simp [insertByKey]
  | b :: bs, hnd, hnmem => by
      have hb : b ∉ bs := (List.nodup_cons.mp hnd).1
      have hbs : bs.Nodup := (List.nodup_cons.mp hnd).2
      have ha_ne_b : a ≠ b := by
        intro hab
        apply hnmem
        simp [hab]
      have ha_not_bs : a ∉ bs := by
        intro hmem
        apply hnmem
        exact List.mem_cons_of_mem b hmem
      by_cases h : key a ≤ key b
      · -- insert before b: result is `a :: b :: bs`
        simp only [insertByKey, h, ↓reduceIte]
        have ha_not_tail : a ∉ b :: bs := by
          intro hmem
          rcases List.mem_cons.mp hmem with rfl | hmem'
          · exact ha_ne_b rfl
          · exact ha_not_bs hmem'
        exact List.nodup_cons.mpr ⟨ha_not_tail, List.nodup_cons.mpr ⟨hb, hbs⟩⟩
      · -- insert into tail: `b :: insertByKey key a bs`
        simp only [insertByKey, h, ↓reduceIte]
        have htail : (insertByKey key a bs).Nodup :=
          nodup_insertByKey (xs := bs) (key := key) (a := a) hbs ha_not_bs
        have hb_not_tail : b ∉ insertByKey key a bs := by
          intro hmem
          have : b = a ∨ b ∈ bs := (mem_insertByKey (key := key) (a := a) (x := b) (xs := bs)).1 hmem
          rcases this with hba | hbmem
          · exact ha_ne_b hba.symm
          · exact hb hbmem
        exact List.nodup_cons.mpr ⟨hb_not_tail, htail⟩

/-- `sortByKey` preserves nodup. -/
theorem nodup_sortByKey {α : Type} [DecidableEq α] (key : α → Nat) :
    ∀ {xs : List α}, xs.Nodup → (sortByKey key xs).Nodup
  | [], _ => by
      simp [sortByKey]
  | a :: as, hnd => by
      have ha : a ∉ as := (List.nodup_cons.mp hnd).1
      have has : as.Nodup := (List.nodup_cons.mp hnd).2
      have ih : (sortByKey key as).Nodup := nodup_sortByKey (xs := as) (key := key) has
      have ha' : a ∉ sortByKey key as := by
        intro hmem
        have : a ∈ as := (mem_sortByKey (key := key) (x := a) (xs := as)).1 hmem
        exact ha this
      -- now insert `a` into the sorted tail
      exact nodup_insertByKey (xs := sortByKey key as) (key := key) (a := a) ih ha'

end ListLemmas

namespace Pos

open ListLemmas

/-- If `pos? xs a = some i`, then `xs.get i = a`. -/
theorem get_of_pos?_some {α : Type} [DecidableEq α] :
    ∀ (xs : List α) (a : α) (i : Fin xs.length), pos? xs a = some i → xs.get i = a
  | [], _, i, _ => i.elim0
  | hd :: tl, a, i, h => by
      unfold pos? at h
      split at h
      · -- case a = hd
        rename_i heq
        have hi : i = ⟨0, Nat.zero_lt_succ tl.length⟩ := (Option.some.inj h).symm
        simp [hi, heq]
      · -- case a ≠ hd
        rename_i hne
        cases hp : pos? tl a with
        | none => simp [hp] at h
        | some i0 =>
            simp only [hp] at h
            have hi : i = ⟨i0.val.succ, Nat.succ_lt_succ i0.isLt⟩ := (Option.some.inj h).symm
            have htl : tl.get i0 = a := get_of_pos?_some tl a i0 hp
            simp only [hi, List.get, htl]

/-- If `xs` is nodup, then `pos? xs (xs.get i) = some i`. -/
theorem pos?_get_of_nodup {α : Type} [DecidableEq α] :
    ∀ {xs : List α}, xs.Nodup → (i : Fin xs.length) → pos? xs (xs.get i) = some i
  | [], _hnd, i => by
      cases i with
      | mk v hv => cases hv
  | x :: xs, hnd, ⟨0, _⟩ => by
      simp [pos?]
  | hd :: tl, hnd, ⟨Nat.succ k, hk⟩ => by
      have hhd_not_tail : hd ∉ tl := (List.nodup_cons.mp hnd).1
      have htl_nodup : tl.Nodup := (List.nodup_cons.mp hnd).2
      have hk_lt : k < tl.length := Nat.lt_of_succ_lt_succ hk
      let i' : Fin tl.length := ⟨k, hk_lt⟩
      have ih : pos? tl (tl.get i') = some i' := pos?_get_of_nodup (xs := tl) htl_nodup i'
      -- show the searched element is not equal to the head
      have hne : tl.get i' ≠ hd := by
        intro hEq
        have hmem : tl.get i' ∈ tl := get_mem (xs := tl) i'
        rw [hEq] at hmem
        exact hhd_not_tail hmem
      -- unfold `pos?` on the cons list
      -- Goal: pos? (hd :: tl) ((hd :: tl).get ⟨k.succ, hk⟩) = some ⟨k.succ, hk⟩
      -- (hd :: tl).get ⟨k.succ, hk⟩ = tl.get ⟨k, ...⟩ = tl.get i'
      show pos? (hd :: tl) ((hd :: tl)[k.succ]) = some ⟨k.succ, hk⟩
      simp only [List.getElem_cons_succ]
      -- Now: pos? (hd :: tl) (tl[k]) = some ⟨k.succ, hk⟩
      unfold pos?
      split
      · -- case tl[k] = hd - contradiction with hne
        rename_i heq_hd
        have : tl.get i' = hd := heq_hd
        exact absurd this hne
      · -- case tl[k] ≠ hd
        -- ih : pos? tl (tl.get i') = some i'
        -- tl.get i' = tl[k] since i' = ⟨k, hk_lt⟩
        -- Goal: match pos? tl tl[k] with | none => none | some i => some ⟨i.val.succ, ...⟩ = some ⟨k.succ, hk⟩
        -- Rewrite using the fact that tl[k] = tl.get i'
        have heq_elem : tl[k] = tl.get i' := rfl
        simp only [heq_elem, ih]
        -- Goal: some ⟨(↑i').succ, ⋯⟩ = some ⟨k.succ, hk⟩
        -- Since i' = ⟨k, hk_lt⟩, we have ↑i' = k, so both Fins have val = k.succ
        rfl

end Pos

namespace ActiveAxes

open ListLemmas

/-- Membership in `activeAxes` is membership in the underlying filtered axis set.

We keep the `allAxes` conjunct explicit so we do not depend on a specific
library characterization of `List.finRange`.
-/
theorem mem_activeAxes_iff {n : Nat} (m : Exponents n) (s : Nat) (j : Axis n) :
    j ∈ activeAxes m s ↔ (j ∈ allAxes n) ∧ (s ≤ m j) := by
  -- `activeAxes` is `sortByKey ... (filter ...)` and sorting preserves membership.
  simp [activeAxes, mem_sortByKey, allAxes]

/-- Monotone activation: if an axis is active at `s+1`, it is active at `s`. -/
theorem mem_activeAxes_of_mem_activeAxes_succ {n : Nat} (m : Exponents n) (s : Nat) (j : Axis n) :
    j ∈ activeAxes m (Nat.succ s) → j ∈ activeAxes m s := by
  intro hj
  have hj' : (j ∈ allAxes n) ∧ (Nat.succ s ≤ m j) := (mem_activeAxes_iff (m := m) (s := Nat.succ s) (j := j)).1 hj
  have hs : s ≤ m j := Nat.le_trans (Nat.le_succ s) hj'.2
  exact (mem_activeAxes_iff (m := m) (s := s) (j := j)).2 ⟨hj'.1, hs⟩

/-- `List.finRange n` is nodup. We prove this directly since the Std lemma name varies. -/
theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp [List.finRange]
  | succ n ih =>
    rw [List.finRange_succ]
    refine List.nodup_cons.mpr ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_map] at h
      obtain ⟨x, _, hx⟩ := h
      exact Fin.succ_ne_zero x hx
    · refine List.Pairwise.map Fin.succ ?_ ih
      intro a b hab heq
      have hval : a.val.succ = b.val.succ := congrArg Fin.val heq
      have hv : a.val = b.val := Nat.succ.inj hval
      exact hab (Fin.ext hv)

/-- `allAxes n` is nodup. -/
theorem nodup_allAxes (n : Nat) : (allAxes n).Nodup := by
  simp only [allAxes]
  exact finRange_nodup n

/-- `activeAxes m s` is nodup (unique axes).

Proof: `allAxes` is nodup, filtering preserves nodup, and sorting preserves nodup.
-/
theorem nodup_activeAxes {n : Nat} (m : Exponents n) (s : Nat) : (activeAxes m s).Nodup := by
  -- start from nodup `allAxes`
  have h0 : (allAxes n).Nodup := nodup_allAxes n
  -- filtering keeps nodup
  have h1 : ((allAxes n).filter (fun j => s ≤ m j)).Nodup :=
    nodup_filter (p := fun j => s ≤ m j) h0
  -- sorting keeps nodup
  -- (we need decidable equality on axes)
  simpa [activeAxes] using (nodup_sortByKey (α := Axis n) (key := axisKey m) (xs := (allAxes n).filter (fun j => s ≤ m j)) h1)

end ActiveAxes

end AnisoHilbert
