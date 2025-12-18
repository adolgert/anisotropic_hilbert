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

/-!
### No-carry facts for `succDigit`

These are small helpers used later in the lattice-continuity proof (Theorem 5.4):

* `carry = false` means the numeric value increments without overflow,
  so the successor word is `ofNat (toNat w).succ`;
* in particular, `toNat w` is not the all-ones value `2^k - 1`, so `tsb (toNat w) < k`.
-/

theorem succDigit_carry_false_imp_toNat_succ_lt_base (d : Digit) :
    (succDigit d).2 = false → (BV.toNat d.2).succ < base d.1 := by
  intro hc
  cases d with
  | mk k w =>
      by_cases hlt : (BV.toNat w).succ < base k
      · exact hlt
      · -- In the overflow branch, `succDigit` reports `true`, contradicting `hc`.
        have : (true : Bool) = false := by
          simpa [succDigit, hlt] using hc
        cases this

theorem succDigit_eq_ofNat_succ_of_carry_false (d : Digit) (hc : (succDigit d).2 = false) :
    (succDigit d).1 = ⟨d.1, BV.ofNat (k := d.1) (BV.toNat d.2).succ⟩ := by
  cases d with
  | mk k w =>
      have hlt : (BV.toNat w).succ < base k :=
        succDigit_carry_false_imp_toNat_succ_lt_base (d := ⟨k, w⟩) hc
      simp [succDigit, hlt]

private theorem two_pow_sub_one_le_of_le_tsb : ∀ (k x : Nat), k ≤ tsb x → 2 ^ k - 1 ≤ x := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp
  | succ k ih =>
      intro x hx
      have hxpos : 0 < tsb x := Nat.lt_of_lt_of_le (Nat.succ_pos k) hx
      have hxodd : x % 2 = 1 := by
        have h01 := Nat.mod_two_eq_zero_or_one x
        cases h01 with
        | inl h0 =>
            have htsb0 : tsb x = 0 := by
              rw [tsb.eq_1]
              simp [h0, -tsb.eq_1]
            have : False := by simpa [htsb0] using hxpos
            exact False.elim this
        | inr h1 =>
            exact h1

      have htsb : tsb x = Nat.succ (tsb (x / 2)) := by
        rw [tsb.eq_1]
        simp [hxodd, -tsb.eq_1]

      have hx' : k ≤ tsb (x / 2) := by
        have hx' : Nat.succ k ≤ Nat.succ (tsb (x / 2)) := by
          simpa [htsb] using hx
        exact Nat.le_of_succ_le_succ hx'

      have hind : 2 ^ k - 1 ≤ x / 2 := ih (x / 2) hx'
      -- Reconstruct `x = 2*(x/2) + 1` from `x % 2 = 1`.
      have hxrepr : x = 2 * (x / 2) + 1 := by
        have hdiv := Nat.div_add_mod x 2
        calc
          x = (x / 2) * 2 + x % 2 := by
                simpa [Nat.mul_comm] using hdiv.symm
          _ = 2 * (x / 2) + 1 := by
                simpa [Nat.mul_comm, hxodd]
      -- Multiply the IH bound by `2` and add `1`.
      have hmul : 2 * (2 ^ k - 1) + 1 ≤ 2 * (x / 2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 hind) 1
      -- Normalize the LHS to `2^(k+1) - 1`.
      have hnorm : 2 * (2 ^ k - 1) + 1 = 2 ^ Nat.succ k - 1 := by
        have hkpos : 1 ≤ 2 ^ k := Nat.succ_le_iff.2 (Nat.pow_pos (n := k) (Nat.succ_pos 1))
        have ha2 : 2 ≤ 2 * 2 ^ k := by
          have : 2 * 1 ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 hkpos
          simpa using this
        calc
          2 * (2 ^ k - 1) + 1
              = (2 * 2 ^ k - 2) + 1 := by
                  simp [Nat.mul_sub_left_distrib, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ = 2 * 2 ^ k - 1 := by
                have ha1 : 1 ≤ 2 * 2 ^ k - 1 := by
                  have := Nat.sub_le_sub_right ha2 1
                  simpa using this
                have h : (2 * 2 ^ k - 1 - 1) + 1 = 2 * 2 ^ k - 1 := by
                  simpa using (Nat.sub_add_cancel ha1)
                have hsub : 2 * 2 ^ k - 1 - 1 = 2 * 2 ^ k - 2 := by
                  simpa [Nat.sub_sub, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Nat.sub_sub (2 * 2 ^ k) 1 1)
                simpa [hsub] using h
          _ = 2 ^ Nat.succ k - 1 := by
                simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have : 2 ^ Nat.succ k - 1 ≤ x := by
        calc
          2 ^ Nat.succ k - 1 = 2 * (2 ^ k - 1) + 1 := hnorm.symm
          _ ≤ 2 * (x / 2) + 1 := hmul
          _ = x := hxrepr.symm
      exact this

private theorem tsb_lt_of_lt_two_pow
    (k x : Nat) (hk : 0 < k) (hx : x < 2 ^ k) (hne : x ≠ 2 ^ k - 1) : tsb x < k := by
  by_contra hge
  have hle : 2 ^ k - 1 ≤ x := two_pow_sub_one_le_of_le_tsb k x (Nat.le_of_not_gt hge)
  have hkpos : 1 ≤ 2 ^ k := Nat.succ_le_iff.2 (Nat.pow_pos (n := k) (Nat.succ_pos 1))
  have hxle : x ≤ 2 ^ k - 1 := by
    have hrew : 2 ^ k = (2 ^ k - 1) + 1 := by
      simpa [Nat.add_comm, Nat.succ_eq_add_one] using (Nat.sub_add_cancel hkpos).symm
    have hxlt : x < (2 ^ k - 1).succ := by
      simpa [Nat.succ_eq_add_one] using (lt_of_lt_of_eq hx hrew)
    exact Nat.le_of_lt_succ hxlt
  have hEq : x = 2 ^ k - 1 := Nat.le_antisymm hxle hle
  exact hne hEq

theorem succDigit_carry_false_imp_tsb_lt (d : Digit) :
    (succDigit d).2 = false → tsb (BV.toNat d.2) < d.1 := by
  intro hc
  cases d with
  | mk k w =>
      cases k with
      | zero =>
          -- Width 0 digits always overflow: `0 + 1` cannot fit in base `2^0 = 1`.
          have : (true : Bool) = false := by
            simpa [succDigit, base] using hc
          cases this
      | succ k' =>
          have hk : 0 < Nat.succ k' := Nat.succ_pos k'
          have hx : BV.toNat w < 2 ^ Nat.succ k' := by
            -- `base (succ k') = 2^(succ k')`
            simpa [base, Nat.shiftLeft_eq] using (toNat_lt_base (k := Nat.succ k') w)
          have hsucc : (BV.toNat w).succ < 2 ^ Nat.succ k' := by
            -- from carry-false, the successor is still < base
            simpa [base, Nat.shiftLeft_eq] using
              (succDigit_carry_false_imp_toNat_succ_lt_base (d := ⟨Nat.succ k', w⟩) hc)
          have hne : BV.toNat w ≠ 2 ^ Nat.succ k' - 1 := by
            intro hEq
            have hkPowPos : 0 < 2 ^ Nat.succ k' := Nat.pow_pos (n := Nat.succ k') (Nat.succ_pos 1)
            have hkpos : 1 ≤ 2 ^ Nat.succ k' := Nat.succ_le_iff.2 hkPowPos
            have hmaxSucc : (2 ^ Nat.succ k' - 1).succ = 2 ^ Nat.succ k' := by
              simpa [Nat.succ_eq_add_one] using (Nat.sub_add_cancel hkpos)
            have hSuccEq : (BV.toNat w).succ = 2 ^ Nat.succ k' := by
              simpa [hEq] using hmaxSucc
            -- contradict `hsucc` by rewriting the RHS to `w.toNat.succ`
            have h : (BV.toNat w).succ < (BV.toNat w).succ := by
              have h' := hsucc
              rw [← hSuccEq] at h'
              exact h'
            exact Nat.lt_irrefl _ h
          exact tsb_lt_of_lt_two_pow (k := Nat.succ k') (x := BV.toNat w) hk hx hne

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
