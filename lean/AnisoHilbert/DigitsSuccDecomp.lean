import AnisoHilbert.IndexSucc

namespace AnisoHilbert

namespace Digits

/-!
Pivot / decomposition lemmas for the variable-radix successor on `Digits`.

We first analyze the auxiliary least-significant-first successor `succAux`, then
transport the result through `List.reverse` to obtain the MSF statement about
`succ`.
-/

/-- Decomposition lemma for the *least-significant-first* successor `succAux`.

If `succAux ds = (ds', false)` (no total overflow), then `ds` splits as

* a prefix `pre` of digits that overflow (carry propagates through them),
* a pivot digit `pivot` that increments without overflow,
* a suffix `suf` of more-significant digits that remain unchanged.

Moreover `ds'` is obtained by applying `succDigit` to the overflow prefix and the
pivot, leaving the suffix unchanged.
-/
theorem succAux_decomp :
    ∀ (ds ds' : List Digit), succAux ds = (ds', false) →
      ∃ pre pivot suf,
        ds = pre ++ pivot :: suf ∧
        (∀ x ∈ pre, (succDigit x).2 = true) ∧
        (succDigit pivot).2 = false ∧
        ds' = (pre.map (fun x => (succDigit x).1)) ++ (succDigit pivot).1 :: suf := by
  intro ds
  induction ds with
  | nil =>
      intro ds' h
      -- `succAux [] = ([], true)` so it cannot equal `(_, false)`.
      simp [succAux] at h
  | cons d ds ih =>
      intro ds' h
      -- Expose the carry bit from the head digit.
      rcases hsd : succDigit d with ⟨d1, c⟩
      cases c with
      | false =>
          -- No carry: pivot is the head digit.
          have h' : (d1 :: ds, false) = (ds', false) := by
            -- `succAux (d :: ds) = (d1 :: ds, false)` in this branch.
            simpa [succAux, hsd] using h
          have hds' : ds' = d1 :: ds := by
            injection h' with hlist
            exact hlist.symm
          subst hds'
          refine ⟨[], d, ds, ?_, ?_, ?_, ?_⟩
          · simp
          · intro x hx; cases hx
          · -- pivot does not overflow
            simpa [hsd]
          · simp [hsd]
      | true =>
          -- Carry: recurse on the tail.
          cases haux : succAux ds with
          | mk ds2 c2 =>
              -- Compute `succAux (d :: ds)` in terms of the tail result.
              have h' : (d1 :: ds2, c2) = (ds', false) := by
                simpa [succAux, hsd, haux] using h
              have hc2 : c2 = false := by
                injection h' with _ hc
              subst hc2
              have hds' : ds' = d1 :: ds2 := by
                injection h' with hlist _
                exact hlist.symm
              subst hds'
              -- Apply IH to the tail since it also did not overflow.
              have ht : succAux ds = (ds2, false) := by
                simpa [haux]
              rcases ih ds2 ht with ⟨pre, pivot, suf, hsplit, hpre, hpivot, hout⟩
              refine ⟨d :: pre, pivot, suf, ?_, ?_, ?_, ?_⟩
              · -- split of the input list
                simpa [List.cons_append, hsplit]
              · -- all digits in the new prefix overflow
                intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with hxd | hxpre
                · -- `x = d`
                  subst hxd
                  simpa [hsd]
                · exact hpre x hxpre
              · exact hpivot
              · -- output list
                -- `ds2` is already decomposed by `hout`; prepend the zeroed head.
                simpa [hsd, List.map_cons, hout]

/-- Pivot decomposition for the MSF successor `succ`.

If `succ ds = some ds'`, then `ds` decomposes as `hi ++ pivot :: lo` where

* `lo` is the least-significant suffix and every digit in `lo` overflows,
* `pivot` increments without overflow,
* and `hi` is unchanged.

The output `ds'` is obtained by incrementing `pivot` and replacing `lo` with the
zeroed digits produced by `succDigit`.
-/
theorem succ_decomp (ds ds' : Digits) (h : succ ds = some ds') :
    ∃ hi pivot lo,
      ds = hi ++ pivot :: lo ∧
      (∀ d ∈ lo, (succDigit d).2 = true) ∧
      (succDigit pivot).2 = false ∧
      ds' = hi ++ (succDigit pivot).1 :: (lo.map (fun d => (succDigit d).1)) := by
  classical
  unfold succ at h
  cases haux : succAux ds.reverse with
  | mk rev' carry =>
      -- split on whether the whole word overflowed
      cases carry with
      | true =>
          -- `succ ds = none` in this branch
          simp [haux] at h
      | false =>
          -- `succ ds = some rev'.reverse`
          simp [haux] at h
          subst h
          -- Decompose the LSF successor on `ds.reverse`.
          have haux' : succAux ds.reverse = (rev', false) := by
            simpa [haux]
          rcases succAux_decomp (ds := ds.reverse) (ds' := rev') haux' with
            ⟨pre, pivot, suf, hsplit, hpre, hpivot, hout⟩
          -- Transport the split back through `reverse`.
          refine ⟨suf.reverse, pivot, pre.reverse, ?_, ?_, ?_, ?_⟩
          · -- `ds = suf.reverse ++ pivot :: pre.reverse`
            have hr : (ds.reverse).reverse = (pre ++ pivot :: suf).reverse :=
              congrArg List.reverse hsplit
            -- simplify both sides
            simpa [List.reverse_reverse, List.reverse_append, List.reverse_cons, List.append_assoc] using hr
          · -- overflow property for the low suffix `lo = pre.reverse`
            intro d hd
            -- `d ∈ pre.reverse ↔ d ∈ pre`
            have hd' : d ∈ pre := by
              simpa using (List.mem_reverse.mp hd)
            exact hpre d hd'
          · exact hpivot
          · -- output decomposition
            -- From `hout : rev' = pre.map .. ++ succDigit pivot .. :: suf`.
            have hr : rev'.reverse = (pre.map (fun x => (succDigit x).1) ++ (succDigit pivot).1 :: suf).reverse := by
              simpa [hout]
            -- simplify the RHS of `hr` and use `lo = pre.reverse`.
            have hr2 : rev'.reverse = suf.reverse ++ (succDigit pivot).1 :: (pre.reverse.map (fun d => (succDigit d).1)) := by
              simpa [List.reverse_append, List.reverse_cons, List.map_reverse, List.append_assoc] using hr
            simpa [List.map_reverse] using hr2

end Digits

end AnisoHilbert
