import Mathlib

import AnisoHilbert.BVNatLemmas
import AnisoHilbert.DigitsSuccNormalForm
import AnisoHilbert.IndexSucc

namespace AnisoHilbert

namespace BV

/--
Any `k`-bit word represents a natural number strictly below `2^k`
(equivalently `Nat.shiftLeft 1 k`).
-/
theorem toNat_lt_shiftLeft_one {k : Nat} (x : BV k) : toNat x < Nat.shiftLeft 1 k := by
  induction k with
  | zero =>
      -- `BV 0` has no bits, so `toNat = 0`, and `2^0 = 1`.
      simp [toNat]
  | succ k ih =>
      let tail : BV k := fun j => x (Fin.succ j)
      have htail : toNat tail < Nat.shiftLeft 1 k := ih (x := tail)

      have hx : toNat x = Nat.bit (x 0) (toNat tail) := by
        simpa [tail] using (toNat_succ (x := x))

      have hbase : Nat.shiftLeft 1 (Nat.succ k) = 2 * Nat.shiftLeft 1 k := by
        simp [Nat.shiftLeft_eq, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

      cases h0 : x 0 with
      | false =>
          -- Reduce the goal to the tail bound.
          rw [hx, h0, hbase]
          have hmul : 2 * toNat tail < 2 * Nat.shiftLeft 1 k :=
            Nat.mul_lt_mul_of_pos_left htail (by decide : 0 < 2)
          simpa [Nat.bit] using hmul
      | true =>
          -- Use `toNat tail < base` to show `2*(toNat tail + 1) ≤ 2*base`,
          -- then weaken `+2` to `+1`.
          have hsucc : (toNat tail).succ ≤ Nat.shiftLeft 1 k := Nat.succ_le_of_lt htail
          have hmul : 2 * (toNat tail).succ ≤ 2 * Nat.shiftLeft 1 k :=
            Nat.mul_le_mul_left 2 hsucc

          have hmul' : 2 * (toNat tail).succ = 2 * toNat tail + 2 := by
            simp [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

          have hle : 2 * toNat tail + 2 ≤ 2 * Nat.shiftLeft 1 k := by
            simpa [hmul'] using hmul

          have hlt : 2 * toNat tail + 1 < 2 * toNat tail + 2 := by
            -- `a < a+1` with `a := 2*toNat tail + 1`.
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using Nat.lt_succ_self (2 * toNat tail + 1)

          have hfinal : 2 * toNat tail + 1 < 2 * Nat.shiftLeft 1 k :=
            Nat.lt_of_lt_of_le hlt hle

          rw [hx, h0, hbase]
          simpa [Nat.bit, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfinal

end BV

namespace Digits

/-- Any `k`-bit digit value is strictly below the radix `base k = 2^k`. -/
theorem toNat_lt_base {k : Nat} (w : BV k) : BV.toNat w < base k := by
  -- `base k = Nat.shiftLeft 1 k`.
  simpa [base] using (BV.toNat_lt_shiftLeft_one (x := w))

/-- Re-express `maxVal` as `2^k - 1` in terms of the underlying bitvector `toNat`. -/
theorem val_eq_maxVal_iff_toNat_eq_two_pow_sub_one (d : Digit) :
    val d = maxVal d.1 ↔ BV.toNat d.2 = 2 ^ d.1 - 1 := by
  -- `val d` is definitionally `BV.toNat d.2`, and `maxVal k = base k - 1 = 2^k - 1`.
  simp [val, maxVal, base, Nat.shiftLeft_eq]

/--
If `succDigit` reports a carry-out, then the input digit was already maximal,
so its value is `maxVal k = 2^k - 1`.
-/
theorem succDigit_carry_true_imp_val_eq_maxVal (d : Digit) :
    (succDigit d).2 = true → val d = maxVal d.1 := by
  intro hc
  cases d with
  | mk k w =>
      -- Abbreviate the numeric value and base.
      let n : Nat := BV.toNat w
      let b : Nat := base k

      -- Carry means we are in the overflow branch, i.e. `¬ n.succ < b`.
      have hnotlt : ¬ n.succ < b := by
        by_cases hlt : n.succ < b
        · have : (false : Bool) = true := by
            simpa [succDigit, n, b, hlt] using hc
          cases this
        · exact hlt

      -- Every `k`-bit word is strictly below `b = 2^k`.
      have hbound : n < b := by
        simpa [n, b, base] using (toNat_lt_base (k := k) w)

      -- Therefore `n.succ = b`, so `n = b - 1`.
      have hge : b ≤ n.succ := Nat.le_of_not_gt hnotlt
      have hle : n.succ ≤ b := Nat.succ_le_of_lt hbound
      have hEq : n.succ = b := Nat.le_antisymm hle hge
      have hEq' : n + 1 = b := by simpa [Nat.succ_eq_add_one] using hEq
      have hn : n = b - 1 := by
        have := congrArg (fun t => t - 1) hEq'
        simpa [Nat.add_sub_cancel_right] using this

      -- Unfold `val` / `maxVal` and conclude.
      simpa [Digits.val, Digits.maxVal, n, b, hn]

theorem succ_same_prefix_zero_suffix_max_suffix (ds ds' : Digits) (h : succ ds = some ds') :
    ∃ hi pivot lo,
      ds = hi ++ pivot :: lo ∧
      ds' = hi ++ (succDigit pivot).1 :: (lo.map zeroLike) ∧
      (∀ d ∈ lo, val d = maxVal d.1) ∧
      (succDigit pivot).2 = false := by
  classical
  rcases succ_same_prefix_zero_suffix (ds := ds) (ds' := ds') h with
    ⟨hi, pivot, lo, hds, hds', hloCarry, hpivotCarry⟩
  refine ⟨hi, pivot, lo, hds, hds', ?_, hpivotCarry⟩
  intro d hd
  exact succDigit_carry_true_imp_val_eq_maxVal d (hloCarry d hd)

/--
Variant of `succ_same_prefix_zero_suffix_max_suffix` phrased directly in terms of
`BV.toNat = 2^k - 1` on the low suffix digits.
-/
theorem succ_same_prefix_zero_suffix_two_pow_sub_one_suffix (ds ds' : Digits) (h : succ ds = some ds') :
    ∃ hi pivot lo,
      ds = hi ++ pivot :: lo ∧
      ds' = hi ++ (succDigit pivot).1 :: (lo.map zeroLike) ∧
      (∀ d ∈ lo, BV.toNat d.2 = 2 ^ d.1 - 1) ∧
      (succDigit pivot).2 = false := by
  classical
  rcases succ_same_prefix_zero_suffix_max_suffix (ds := ds) (ds' := ds') h with
    ⟨hi, pivot, lo, hds, hds', hloMax, hpivotCarry⟩
  refine ⟨hi, pivot, lo, hds, hds', ?_, hpivotCarry⟩
  intro d hd
  exact (val_eq_maxVal_iff_toNat_eq_two_pow_sub_one d).1 (hloMax d hd)

end Digits

end AnisoHilbert
