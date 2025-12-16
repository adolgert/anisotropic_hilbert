import AnisoHilbert.DigitsSuccDecomp

namespace AnisoHilbert

namespace Digits

/-!
Normal-form lemmas for the variable-radix successor on `Digits`.

The pivot decomposition `Digits.succ_decomp` already gives a common prefix `hi`
and a pivot digit, with the low suffix transformed by `succDigit`.

For the lattice-continuity (“seam”) argument we want an *even more explicit*
pair-of-streams normal form:

* the two streams share the same prefix `hi`;
* the pivot digit increments without overflow;
* the low suffix of the successor stream is literally a list of zero-digits
  (with the right per-digit widths).

This file provides that normalization step.
-/

/-- A zero digit with the same width as `d`. -/
def zeroLike (d : Digit) : Digit :=
  ⟨d.1, BV.zero⟩

@[simp] theorem zeroLike_fst (d : Digit) : (zeroLike d).1 = d.1 := rfl

/-!
### `succDigit` on an overflowing digit

If `succDigit d` reports a carry-out, then its output digit is definitionally
the all-zero word of the same width.

We keep this lemma in a form that can be used by list inductions.
-/

theorem succDigit_fst_eq_zeroLike_of_snd_true (d : Digit)
    (hc : (succDigit d).2 = true) :
    (succDigit d).1 = zeroLike d := by
  cases d with
  | mk k w =>
      -- unfold `succDigit` to an `if` on the overflow test
      dsimp [zeroLike]
      -- split on the overflow test
      by_cases hlt : (BV.toNat w).succ < base k
      · -- In the non-overflow branch, the carry bit is `false`, contradicting `hc`.
        have hcontra : False := by
          have : (false : Bool) = true := by
            simpa [succDigit, hlt] using hc
          cases this
        exact False.elim hcontra
      · -- In the overflow branch, the output is exactly the zero digit.
        simp [succDigit, hlt]

/-!
### Normal form for `succ`

From `succ_decomp` we already get:

`ds' = hi ++ succDigit pivot :: lo.map (succDigit ·).1`.

Using the carry hypothesis on every digit in `lo`, we rewrite that mapped suffix
to `lo.map zeroLike`.
-/

theorem succ_same_prefix_zero_suffix (ds ds' : Digits) (h : succ ds = some ds') :
    ∃ hi pivot lo,
      ds = hi ++ pivot :: lo ∧
      ds' = hi ++ (succDigit pivot).1 :: (lo.map zeroLike) ∧
      (∀ d ∈ lo, (succDigit d).2 = true) ∧
      (succDigit pivot).2 = false := by
  classical
  rcases succ_decomp (ds := ds) (ds' := ds') h with
    ⟨hi, pivot, lo, hds, hloCarry, hpivotCarry, hds'⟩

  -- First rewrite the mapped low suffix into explicit zeros.
  have hmap : lo.map (fun d => (succDigit d).1) = lo.map zeroLike := by
    -- Prove by functional extensionality: each element is equal.
    apply List.map_congr_left
    intro d hd
    exact succDigit_fst_eq_zeroLike_of_snd_true d (hloCarry d hd)

  refine ⟨hi, pivot, lo, hds, ?_, hloCarry, hpivotCarry⟩
  -- Replace the low suffix in `hds'` using `hmap`.
  simpa [hmap] using hds'

end Digits

end AnisoHilbert
