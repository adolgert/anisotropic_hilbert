import Mathlib

import AnisoHilbert.AdjacencyLemmas
import AnisoHilbert.DigitsCarryMaxLemmas
import AnisoHilbert.GrayAdjacencyLemmas
import AnisoHilbert.RotLOneHotLemmas

namespace AnisoHilbert

/-!
Hamilton-style “child glue” lemmas.

The `childEntry` / `childDir` closed forms (Hamilton Theorems 2.10 / 2.9) satisfy
the endpoint recurrence (Hamilton Equation (1), labelled (H1) in `discrete_proof.md`):

`e(i+1) = e(i) ⊕ 2^{d(i)} ⊕ 2^{g(i)}`.

We formalize it in our `BV` encoding, with `oneHotFin` standing for `2^{·}` and
`g(i) = tsb i` (trailing set bits).
-/

namespace BV

open scoped BigOperators

private theorem ofNat_inj_of_lt {k a b : Nat}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k) (h : ofNat (k := k) a = ofNat (k := k) b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hik : i < k
  · -- In-range bits are equal by the `BV` equality.
    have hbit := congrArg (fun (v : BV k) => v ⟨i, hik⟩) h
    simpa [ofNat] using hbit
  · -- Out-of-range bits are `false` because both numbers are `< 2^k ≤ 2^i`.
    have hki : k ≤ i := Nat.le_of_not_gt hik
    have hpow : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hki
    have ha' : a < 2 ^ i := lt_of_lt_of_le ha hpow
    have hb' : b < 2 ^ i := lt_of_lt_of_le hb hpow
    simp [Nat.testBit_eq_false_of_lt ha', Nat.testBit_eq_false_of_lt hb']

/-- `toNat (ofNat n) = n` when `n < 2^k` (no truncation). -/
private theorem toNat_ofNat_eq_of_lt {k n : Nat} (hn : n < 2 ^ k) :
    toNat (ofNat (k := k) n) = n := by
  -- Let `m` be the reconstructed number from the low `k` bits of `n`.
  set m : Nat := toNat (ofNat (k := k) n)
  have hm : m < 2 ^ k := by
    -- Any `k`-bit word represents a number `< 2^k`.
    simpa [m, Nat.shiftLeft_eq] using (toNat_lt_shiftLeft_one (x := ofNat (k := k) n))
  have hof : ofNat (k := k) m = ofNat (k := k) n := by
    -- `ofNat_toNat` is a left inverse.
    simpa [m] using (ofNat_toNat (x := ofNat (k := k) n))
  -- `ofNat` is injective on the range `< 2^k`.
  have : m = n := ofNat_inj_of_lt (k := k) (a := m) (b := n) hm hn hof
  simpa [m, this]

private theorem xor_assoc {k : Nat} (x y z : BV k) : xor (xor x y) z = xor x (xor y z) := by
  funext i
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;> simp [xor, bxor, hx, hy, hz]

private theorem xor_comm {k : Nat} (x y : BV k) : xor x y = xor y x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [xor, bxor, hx, hy]

/-- `childDir k i` is always a valid direction index `< k` when `k > 0`. -/
private theorem childDir_lt {k : Nat} (hk : 0 < k) (i : Nat) : childDir k i < k := by
  by_cases h0 : i = 0
  · subst h0
    simpa [childDir, hk]
  · by_cases hEven : i % 2 = 0
    · simp [childDir, h0, hEven, Nat.mod_lt _ hk]
    · simp [childDir, h0, hEven, Nat.mod_lt _ hk]

/-- If `k ≤ tsb x`, then the lowest `k` bits of `x` are `1`, hence `2^k - 1 ≤ x`. -/
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
        -- `x = (x/2)*2 + x%2`; commute the product.
        calc
          x = (x / 2) * 2 + x % 2 := by simpa [Nat.mul_comm] using hdiv.symm
          _ = 2 * (x / 2) + 1 := by simpa [Nat.mul_comm, hxodd]
      -- Multiply the IH bound by `2` and add `1`.
      have hmul : 2 * (2 ^ k - 1) + 1 ≤ 2 * (x / 2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 2 hind) 1
      -- Normalize the LHS to `2^(k+1) - 1`.
      have hnorm : 2 * (2 ^ k - 1) + 1 = 2 ^ Nat.succ k - 1 := by
        have hkpos : 1 ≤ 2 ^ k := Nat.succ_le_iff.2 (Nat.pow_pos (n := k) (Nat.succ_pos 1))
        have ha2 : 2 ≤ 2 * 2 ^ k := by
          -- `2 * 2^k ≥ 2 * 1`.
          have : 2 * 1 ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 hkpos
          simpa using this
        calc
          2 * (2 ^ k - 1) + 1
              = (2 * 2 ^ k - 2) + 1 := by
                  -- expand `2*(a-1)` as `2*a - 2`
                  simp [Nat.mul_sub_left_distrib, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          _ = 2 * 2 ^ k - 1 := by
                -- `a - 2 + 1 = a - 1` when `a ≥ 2`.
                have ha1 : 1 ≤ 2 * 2 ^ k - 1 := by
                  have := Nat.sub_le_sub_right ha2 1
                  simpa using this
                have h : (2 * 2 ^ k - 1 - 1) + 1 = 2 * 2 ^ k - 1 := by
                  simpa using (Nat.sub_add_cancel ha1)
                have hsub : 2 * 2 ^ k - 1 - 1 = 2 * 2 ^ k - 2 := by
                  -- `a - 1 - 1 = a - 2`
                  simpa [Nat.sub_sub, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                    (Nat.sub_sub (2 * 2 ^ k) 1 1)
                simpa [hsub] using h
          _ = 2 ^ Nat.succ k - 1 := by
                simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      -- Finish.
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
    -- `x < 2^k = (2^k - 1) + 1`
    have hrew : 2 ^ k = (2 ^ k - 1) + 1 := by
      simpa [Nat.add_comm, Nat.succ_eq_add_one] using (Nat.sub_add_cancel hkpos).symm
    have hxlt : x < (2 ^ k - 1).succ := by
      simpa [Nat.succ_eq_add_one] using (lt_of_lt_of_eq hx hrew)
    exact Nat.le_of_lt_succ hxlt
  have hEq : x = 2 ^ k - 1 := Nat.le_antisymm hxle hle
  exact hne hEq

private theorem tsb_two_pow_sub_one : ∀ k : Nat, tsb (2 ^ k - 1) = k := by
  intro k
  induction k with
  | zero =>
      simp [tsb]
  | succ k ih =>
      -- `2^(k+1) - 1 = 1 + 2 * (2^k - 1)`
      have hkpos : 1 ≤ 2 ^ k := Nat.succ_le_iff.2 (Nat.pow_pos (n := k) (Nat.succ_pos 1))
      have ha2 : 2 ≤ 2 * 2 ^ k := by
        have : 2 * 1 ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 hkpos
        simpa using this
      have hrepr : 2 ^ Nat.succ k - 1 = 1 + 2 * (2 ^ k - 1) := by
        -- rewrite `2^(k+1)` as `2 * 2^k` and rearrange
        have hpow : 2 ^ Nat.succ k = 2 * 2 ^ k := by
          simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        -- `a - 1 = 1 + (a - 2)` for `a ≥ 2`.
        have ha1 : 1 ≤ 2 * 2 ^ k - 1 := by
          have := Nat.sub_le_sub_right ha2 1
          simpa using this
        have hsub : 2 * 2 ^ k - 1 = 1 + (2 * 2 ^ k - 2) := by
          have : (2 * 2 ^ k - 1 - 1) + 1 = 2 * 2 ^ k - 1 := by
            simpa using (Nat.sub_add_cancel ha1)
          -- `(a-1)-1 = a-2`
          have : 2 * 2 ^ k - 1 = (2 * 2 ^ k - 2) + 1 := by
            simpa [Nat.sub_sub, Nat.add_assoc] using this.symm
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
        calc
          2 ^ Nat.succ k - 1 = 2 * 2 ^ k - 1 := by simpa [hpow]
          _ = 1 + (2 * 2 ^ k - 2) := hsub
          _ = 1 + 2 * (2 ^ k - 1) := by
                simp [Nat.mul_sub_left_distrib, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

      have hmod : (2 ^ Nat.succ k - 1) % 2 = 1 := by
        simp [hrepr]
      have hdiv : (2 ^ Nat.succ k - 1) / 2 = 2 ^ k - 1 := by
        -- `(1 + 2*z) / 2 = z`
        simpa [hrepr] using (Nat.add_mul_div_left 1 (2 ^ k - 1) (y := 2) (by decide : 0 < (2 : Nat)))
      -- `tsb` peels one trailing `1`.
      simp [tsb, hmod, hdiv, ih]

/--
Hamilton's endpoint recurrence (H1) for the closed forms `childEntry` / `childDir`.

We restrict to `i < 2^k` (child indices of a `k`-cube) and assume `tsb i < k`
so that the successor `i+1` does not wrap in the low `k` bits.
-/
theorem childEntry_succ_eq_xor_oneHotFin_childDir_tsb
    {k : Nat} (hk : 0 < k) (i : Nat) (hi : i < 2 ^ k) (ht : tsb i < k) :
    childEntry k i.succ
      =
    xor (xor (childEntry k i) (oneHotFin ⟨childDir k i, childDir_lt hk i⟩)) (oneHotFin ⟨tsb i, ht⟩) := by
  have hmod := Nat.mod_two_eq_zero_or_one i
  cases hmod with
  | inl hEven =>
      have htsb : tsb i = 0 := by
        rw [tsb.eq_1]
        simp [hEven, -tsb.eq_1]
      have hG : oneHotFin (⟨tsb i, ht⟩ : Fin k) = oneHotFin ⟨0, hk⟩ := by
        have hfin : (⟨tsb i, ht⟩ : Fin k) = ⟨0, hk⟩ := by
          apply Fin.ext
          simpa [htsb]
        simpa using congrArg oneHotFin hfin

      cases i with
      | zero =>
          have hgc0 : gc (ofNat (k := k) 0) = (zero : BV k) := by
            funext j
            simp [gc, shr1, ofNat, zero, xor, bxor, getBit]
          have hDir0 : oneHotFin (⟨childDir k 0, childDir_lt hk 0⟩ : Fin k) = oneHotFin ⟨0, hk⟩ := by
            have hfin : (⟨childDir k 0, childDir_lt hk 0⟩ : Fin k) = ⟨0, hk⟩ := by
              apply Fin.ext
              simp [childDir]
            simpa using congrArg oneHotFin hfin
          -- Both one-hot terms are the same and cancel.
          have hR :
              (zero : BV k) =
                xor (xor (zero : BV k) (oneHotFin ⟨0, hk⟩)) (oneHotFin ⟨0, hk⟩) := by
            simpa using (xor_invol_right (x := (zero : BV k)) (e := oneHotFin ⟨0, hk⟩)).symm
          simpa [childEntry, childDir, hgc0, hDir0, hG] using hR
      | succ i' =>
          have hDvdI : 2 ∣ Nat.succ i' := Nat.dvd_of_mod_eq_zero hEven
          have hJ2 : 2 * ((Nat.succ i') / 2) = Nat.succ i' := by
            simpa using (Nat.mul_div_cancel' hDvdI)

          have hOdd' : i' % 2 = 1 := by
            have h01 := Nat.mod_two_eq_zero_or_one i'
            cases h01 with
            | inl h0 =>
                have hs : (Nat.succ i') % 2 = (i' % 2 + 1) % 2 := by
                  simpa [Nat.succ_eq_add_one] using (Nat.add_mod i' 1 2)
                have : (Nat.succ i') % 2 = 1 := by
                  calc
                    (Nat.succ i') % 2 = (i' % 2 + 1) % 2 := hs
                    _ = (0 + 1) % 2 := by simp [h0]
                    _ = 1 := by decide
                exact False.elim (by simpa [this] using hEven)
            | inr h1 =>
                exact h1

          have hrepr : 2 * (i' / 2) + 1 = i' := by
            simpa [hOdd'] using (Nat.div_add_mod i' 2)
          have hJ1 : 2 * (i' / 2) = i' - 1 := by
            have := congrArg (fun t => t - 1) hrepr
            simpa [Nat.add_sub_cancel] using this

          have hi' : i' < 2 ^ k := Nat.lt_trans (Nat.lt_succ_self i') hi
          have hi'ne : i' ≠ 2 ^ k - 1 := by
            intro hEq
            have hkpow : 1 ≤ 2 ^ k :=
              Nat.succ_le_iff.2 (Nat.pow_pos (n := k) (Nat.succ_pos 1))
            have hsucc : (2 ^ k - 1).succ = 2 ^ k := by
              simpa [Nat.succ_eq_add_one] using (Nat.sub_add_cancel hkpow)
            have hEqSucc : Nat.succ i' = 2 ^ k := by
              simpa [hEq.symm] using hsucc
            have hi0 : Nat.succ i' < 2 ^ k := hi
            rw [hEqSucc] at hi0
            exact (Nat.lt_irrefl _ hi0)
          have htPred : tsb i' < k := tsb_lt_of_lt_two_pow k i' hk hi' hi'ne

          have hDir : childDir k (Nat.succ i') = tsb i' := by
            simp [childDir, Nat.succ_ne_zero, hEven, Nat.succ_sub_one, Nat.mod_eq_of_lt htPred]
          have hDirFin :
              (⟨childDir k (Nat.succ i'), childDir_lt hk (Nat.succ i')⟩ : Fin k) = ⟨tsb i', htPred⟩ := by
            apply Fin.ext
            simpa [hDir]
          have hOneHotDir :
              oneHotFin (⟨childDir k (Nat.succ i'), childDir_lt hk (Nat.succ i')⟩ : Fin k) =
                oneHotFin ⟨tsb i', htPred⟩ := by
            simpa using congrArg oneHotFin hDirFin

          have hDvdPredPred : 2 ∣ i' - 1 := ⟨i' / 2, hJ1.symm⟩
          have hmodPredPred : (i' - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd hDvdPredPred
          have htsbPredPred : tsb (i' - 1) = 0 := by
            rw [tsb.eq_1]
            simp [hmodPredPred, -tsb.eq_1]
          have htPredPred : tsb (i' - 1) < k := by
            simpa [htsbPredPred] using hk

          have hi'pos : 0 < i' := Nat.pos_of_ne_zero (by
            intro h0
            subst h0
            simp at hOdd')
          have hsuccPred : (i' - 1).succ = i' := by
            simpa [Nat.pred_eq_sub_one] using (Nat.succ_pred_eq_of_pos hi'pos)
          have hsuccPred' : i' - 1 + 1 = i' := by
            simpa [Nat.succ_eq_add_one] using hsuccPred

          have hGc0 :
              xor (gc (ofNat (k := k) (i' - 1))) (gc (ofNat (k := k) i')) =
                oneHotFin ⟨tsb (i' - 1), htPredPred⟩ := by
            simpa [Nat.succ_eq_add_one, hsuccPred'] using
              (xor_gc_ofNat_succ_eq_oneHotFin (k := k) (i := i' - 1) htPredPred)

          have hGc1 :
              xor (gc (ofNat (k := k) i')) (gc (ofNat (k := k) (Nat.succ i'))) =
                oneHotFin ⟨tsb i', htPred⟩ := by
            simpa using (xor_gc_ofNat_succ_eq_oneHotFin (k := k) (i := i') htPred)

          have hOneHotPredPred :
              oneHotFin ⟨tsb (i' - 1), htPredPred⟩ = oneHotFin ⟨0, hk⟩ := by
            have hfin : (⟨tsb (i' - 1), htPredPred⟩ : Fin k) = ⟨0, hk⟩ := by
              apply Fin.ext
              simpa [htsbPredPred]
            simpa using congrArg oneHotFin hfin

          have hGcStep0 :
              gc (ofNat (k := k) i') =
                xor (gc (ofNat (k := k) (i' - 1))) (oneHotFin ⟨0, hk⟩) := by
            calc
              gc (ofNat (k := k) i') =
                  xor (gc (ofNat (k := k) (i' - 1)))
                    (xor (gc (ofNat (k := k) (i' - 1))) (gc (ofNat (k := k) i'))) := by
                      simpa using
                        (xor_invol_left (x := gc (ofNat (k := k) i'))
                          (e := gc (ofNat (k := k) (i' - 1)))).symm
              _ = xor (gc (ofNat (k := k) (i' - 1))) (oneHotFin ⟨tsb (i' - 1), htPredPred⟩) := by
                    simpa [hGc0]
              _ = xor (gc (ofNat (k := k) (i' - 1))) (oneHotFin ⟨0, hk⟩) := by
                    simp [hOneHotPredPred]

          have hGcStep1 :
              gc (ofNat (k := k) (Nat.succ i')) =
                xor (gc (ofNat (k := k) i')) (oneHotFin ⟨tsb i', htPred⟩) := by
            calc
              gc (ofNat (k := k) (Nat.succ i')) =
                  xor (gc (ofNat (k := k) i'))
                    (xor (gc (ofNat (k := k) i')) (gc (ofNat (k := k) (Nat.succ i')))) := by
                      simpa using
                        (xor_invol_left (x := gc (ofNat (k := k) (Nat.succ i')))
                          (e := gc (ofNat (k := k) i'))).symm
              _ = xor (gc (ofNat (k := k) i')) (oneHotFin ⟨tsb i', htPred⟩) := by
                    simpa [hGc1]

          have hGcSucc :
              gc (ofNat (k := k) (Nat.succ i')) =
                xor (xor (gc (ofNat (k := k) (i' - 1))) (oneHotFin ⟨0, hk⟩))
                  (oneHotFin ⟨tsb i', htPred⟩) := by
            calc
              gc (ofNat (k := k) (Nat.succ i')) =
                  xor (gc (ofNat (k := k) i')) (oneHotFin ⟨tsb i', htPred⟩) := hGcStep1
              _ = xor (xor (gc (ofNat (k := k) (i' - 1))) (oneHotFin ⟨0, hk⟩))
                    (oneHotFin ⟨tsb i', htPred⟩) := by
                      rw [hGcStep0]

          have hMain :
              gc (ofNat (k := k) (Nat.succ i')) =
                xor (xor (gc (ofNat (k := k) (i' - 1))) (oneHotFin ⟨tsb i', htPred⟩))
                  (oneHotFin ⟨0, hk⟩) := by
            -- Swap the last two one-hot terms.
            calc
              gc (ofNat (k := k) (Nat.succ i')) =
                  xor (xor (gc (ofNat (k := k) (i' - 1))) (oneHotFin ⟨0, hk⟩))
                    (oneHotFin ⟨tsb i', htPred⟩) := hGcSucc
              _ = xor (gc (ofNat (k := k) (i' - 1)))
                    (xor (oneHotFin ⟨0, hk⟩) (oneHotFin ⟨tsb i', htPred⟩)) := by
                      simpa using
                        (xor_assoc (gc (ofNat (k := k) (i' - 1)))
                          (oneHotFin ⟨0, hk⟩) (oneHotFin ⟨tsb i', htPred⟩))
              _ = xor (gc (ofNat (k := k) (i' - 1)))
                    (xor (oneHotFin ⟨tsb i', htPred⟩) (oneHotFin ⟨0, hk⟩)) := by
                      simp [xor_comm]
              _ = xor (xor (gc (ofNat (k := k) (i' - 1))) (oneHotFin ⟨tsb i', htPred⟩))
                    (oneHotFin ⟨0, hk⟩) := by
                      simpa using
                        (xor_assoc (gc (ofNat (k := k) (i' - 1)))
                          (oneHotFin ⟨tsb i', htPred⟩) (oneHotFin ⟨0, hk⟩)).symm

          have hEntrySucc : childEntry k (Nat.succ (Nat.succ i')) = gc (ofNat (k := k) (Nat.succ i')) := by
            simp [childEntry, hJ2]
          have hEntry : childEntry k (Nat.succ i') = gc (ofNat (k := k) (i' - 1)) := by
            simp [childEntry, Nat.succ_sub_one, hJ1]

          simpa [hEntrySucc, hEntry, hOneHotDir, hG] using hMain

  | inr hOdd =>
      -- Odd `i`: the even predecessor for `childEntry` is the same for `i` and `i+1`,
      -- and `childDir i = tsb i` (since `tsb i < k`).
      have hiNe0 : i ≠ 0 := by
        intro h0
        subst h0
        simp at hOdd
      have hDvdPred : 2 ∣ i - 1 := by
        -- Since `i` is odd, `i = 2*(i/2) + 1`, hence `i-1 = 2*(i/2)`.
        have hrepr : i = 2 * (i / 2) + 1 := by
          have hdiv := Nat.div_add_mod i 2
          simpa [Nat.mul_comm, hOdd] using hdiv.symm
        refine ⟨i / 2, ?_⟩
        have hsub : i - 1 = (2 * (i / 2) + 1) - 1 :=
          congrArg (fun t => t - 1) hrepr
        calc
          i - 1 = (2 * (i / 2) + 1) - 1 := hsub
          _ = 2 * (i / 2) := by simp
      have hJ : 2 * ((i - 1) / 2) = i - 1 := by
        simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hDvdPred)
      have hOddMul : 2 * (i / 2) = i - 1 := by
        -- `i = 2*(i/2) + 1` since `i` is odd.
        have hdiv := Nat.div_add_mod i 2
        have : i = 2 * (i / 2) + 1 := by
          simpa [Nat.mul_comm, hOdd] using hdiv.symm
        have hiPos : 0 < i := Nat.pos_of_ne_zero hiNe0
        have : i - 1 = 2 * (i / 2) := by
          -- subtract 1 from both sides (safe since `i > 0`)
          have := congrArg (fun t => t - 1) this
          simpa [Nat.add_sub_cancel, Nat.sub_add_cancel hiPos] using this
        simpa [Nat.mul_comm] using this.symm
      have hDir : childDir k i = tsb i := by
        simp [childDir, hiNe0, hOdd, Nat.mod_eq_of_lt ht]
      have hDirFin : (⟨childDir k i, childDir_lt hk i⟩ : Fin k) = ⟨tsb i, ht⟩ := by
        apply Fin.ext
        simp [hDir]
      have hOneHotEq :
          oneHotFin ⟨childDir k i, childDir_lt hk i⟩ = oneHotFin ⟨tsb i, ht⟩ := by
        simpa using congrArg oneHotFin hDirFin
      have hEntryEq : childEntry k i.succ = childEntry k i := by
        simp [childEntry, hiNe0, hJ, hOddMul]
      -- In the odd case, the two one-hots are equal and cancel.
      calc
        childEntry k i.succ = childEntry k i := hEntryEq
        _ = xor (xor (childEntry k i) (oneHotFin ⟨tsb i, ht⟩)) (oneHotFin ⟨tsb i, ht⟩) := by
              simpa using
                (xor_invol_right (x := childEntry k i) (e := oneHotFin ⟨tsb i, ht⟩)).symm
        _ = xor (xor (childEntry k i) (oneHotFin ⟨childDir k i, childDir_lt hk i⟩))
              (oneHotFin ⟨tsb i, ht⟩) := by
              simp [hOneHotEq]

/--
Oriented version of the “child endpoints glue” step at the **state** level:
the entry corner of child `(i+1)` equals the exit corner of child `i`, XOR a rotated one-hot.

This is the algebraic bridge used in the seam step of Theorem 5.4.
-/
theorem entryCorner_stateUpdate_succ_eq_exitCorner_stateUpdate_xor_rotL_oneHotFin_tsb
    {n : Nat} {A : List (Axis n)} (st : State n A) (w : BV A.length)
    (ht : tsb (toNat w) < A.length) :
    (stateUpdate A st (ofNat (k := A.length) (toNat w).succ)).e
      =
    xor (xor (stateUpdate A st w).e (oneHotFin (stateUpdate A st w).dPos))
        (rotL (k := A.length) (st.dPos.val.succ) (oneHotFin ⟨tsb (toNat w), ht⟩)) := by
  classical
  -- Abbreviations for the numeric child index and the active dimension.
  let k : Nat := A.length
  let i : Nat := toNat w
  have hk : 0 < k := by
    simpa [k] using (State.length_pos st)
  have hi : i < 2 ^ k := by
    simpa [i, k, Nat.shiftLeft_eq] using (toNat_lt_shiftLeft_one (x := w))
  have htI : tsb i < k := by
    simpa [i, k] using ht

  -- `i.succ < 2^k` because `tsb i < k` excludes the all-ones case.
  have hiSucc : i.succ < 2 ^ k := by
    have hneMax : i ≠ 2 ^ k - 1 := by
      intro hEq
      have htsbEq : tsb i = k := by
        simpa [hEq] using (tsb_two_pow_sub_one k)
      have : False := by simpa [htsbEq] using htI
      exact this
    have hkPowPos : 0 < 2 ^ k := Nat.pow_pos (n := k) (Nat.succ_pos 1)
    have hkpos : 1 ≤ 2 ^ k := Nat.succ_le_iff.2 hkPowPos
    have hrew : 2 ^ k = (2 ^ k - 1) + 1 := (Nat.sub_add_cancel hkpos).symm
    have hiLe : i ≤ 2 ^ k - 1 := by
      have hiLt : i < (2 ^ k - 1) + 1 := lt_of_lt_of_eq hi hrew
      exact Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hiLt)
    have hiLtMax : i < 2 ^ k - 1 := Nat.lt_of_le_of_ne hiLe (by exact hneMax)
    have hiSuccLe : i.succ ≤ 2 ^ k - 1 := Nat.succ_le_of_lt hiLtMax
    have hlt : 2 ^ k - 1 < 2 ^ k := Nat.sub_lt hkPowPos (Nat.succ_pos 0)
    exact Nat.lt_of_le_of_lt hiSuccLe hlt

  have hwSuccNat : toNat (ofNat (k := k) i.succ) = i.succ :=
    toNat_ofNat_eq_of_lt (k := k) (n := i.succ) hiSucc

  -- Shorthands for the two child states.
  set st₁ : State n A := stateUpdate A st w with hst₁
  set st₂ : State n A := stateUpdate A st (ofNat (k := k) i.succ) with hst₂

  have hEntry₁ : st₁.e = xor st.e (rotL (k := k) (st.dPos.val.succ) (childEntry k i)) := by
    simp [hst₁, stateUpdate, i, k, State.mk']
  have hEntry₂ : st₂.e = xor st.e (rotL (k := k) (st.dPos.val.succ) (childEntry k i.succ)) := by
    simp [hst₂, stateUpdate, i, k, hwSuccNat, State.mk']

  have hH1 : childEntry k i.succ =
      xor (xor (childEntry k i) (oneHotFin ⟨childDir k i, childDir_lt hk i⟩)) (oneHotFin ⟨tsb i, htI⟩) :=
    childEntry_succ_eq_xor_oneHotFin_childDir_tsb (k := k) hk i hi htI

  have hdPos :
      rotL (k := k) (st.dPos.val.succ) (oneHotFin ⟨childDir k i, childDir_lt hk i⟩) = oneHotFin st₁.dPos := by
    have hRot :=
      rotL_oneHotFin_eq_of_pos (k := k) hk (r := st.dPos.val.succ) ⟨childDir k i, childDir_lt hk i⟩
    have hIdx :
        (⟨(childDir k i + st.dPos.val.succ) % k, Nat.mod_lt _ hk⟩ : Fin k) = st₁.dPos := by
      apply Fin.ext
      simp [hst₁, stateUpdate, i, k, State.mk', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    simpa [hIdx] using hRot

  have hGoal :
      st₂.e =
        xor (xor st₁.e (oneHotFin st₁.dPos))
            (rotL (k := k) (st.dPos.val.succ) (oneHotFin ⟨tsb i, htI⟩)) := by
    calc
      st₂.e
          = xor st.e (rotL (k := k) (st.dPos.val.succ) (childEntry k i.succ)) := hEntry₂
      _ = xor st.e (rotL (k := k) (st.dPos.val.succ)
            (xor (xor (childEntry k i) (oneHotFin ⟨childDir k i, childDir_lt hk i⟩))
                 (oneHotFin ⟨tsb i, htI⟩))) := by
            simp [hH1]
      _ = xor st.e
            (xor (xor (rotL (k := k) (st.dPos.val.succ) (childEntry k i))
                      (rotL (k := k) (st.dPos.val.succ) (oneHotFin ⟨childDir k i, childDir_lt hk i⟩)))
                 (rotL (k := k) (st.dPos.val.succ) (oneHotFin ⟨tsb i, htI⟩))) := by
            simp [xor_rotL, xor_assoc]
      _ = xor (xor (xor st.e (rotL (k := k) (st.dPos.val.succ) (childEntry k i))) (oneHotFin st₁.dPos))
            (rotL (k := k) (st.dPos.val.succ) (oneHotFin ⟨tsb i, htI⟩)) := by
            -- Reassociate the nested XORs, then rewrite the rotated direction bit as `st₁.dPos`.
            -- (No commutativity needed here.)
            rw [← xor_assoc st.e
              (xor (rotL (k := k) (st.dPos.val.succ) (childEntry k i))
                   (rotL (k := k) (st.dPos.val.succ) (oneHotFin ⟨childDir k i, childDir_lt hk i⟩)))
              (rotL (k := k) (st.dPos.val.succ) (oneHotFin ⟨tsb i, htI⟩))]
            rw [← xor_assoc st.e
              (rotL (k := k) (st.dPos.val.succ) (childEntry k i))
              (rotL (k := k) (st.dPos.val.succ) (oneHotFin ⟨childDir k i, childDir_lt hk i⟩))]
            simp [hdPos]
      _ = xor (xor st₁.e (oneHotFin st₁.dPos))
            (rotL (k := k) (st.dPos.val.succ) (oneHotFin ⟨tsb i, htI⟩)) := by
            simpa [hEntry₁, xor_assoc]

  have htsbIdx : (⟨tsb i, htI⟩ : Fin k) = ⟨tsb (toNat w), ht⟩ := by
    apply Fin.ext
    simp [i, k]
  simpa [hst₁, hst₂, i, k, htsbIdx] using hGoal

end BV

end AnisoHilbert
