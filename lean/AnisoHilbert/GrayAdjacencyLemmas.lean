import AnisoHilbert.Step
import AnisoHilbert.Lemma41

namespace AnisoHilbert

/-!
Gray-code adjacency facts.

For the `k`-bit reflected Gray code `gc : BV k → BV k` (defined as `x XOR (x >> 1)`),
successive integers (when increment does not wrap inside the low `k` bits)
map to vertices that differ in exactly one bit.

We formulate this as an equality

`gc(i) XOR gc(i+1) = oneHot(tsb i)`

where `tsb i` is the number of trailing `1` bits of `i` (our `tsb`), and `oneHot` is
the bitvector with a single `true` entry.
-/

namespace BV

/-- A one-hot `k`-bit word (single `true` bit). -/
def oneHotFin {k : Nat} (g : Fin k) : BV k := fun i => decide (i = g)

@[simp] lemma oneHotFin_apply {k : Nat} (g i : Fin k) : oneHotFin g i = decide (i = g) := rfl

/-!
### Small `Nat.testBit` helpers

We only need the low-bit (index `0`) toggle under successor.
The proof is by splitting `m` into even/odd using `m % 2` and rewriting with
`Nat.div_add_mod`.
-/

private lemma testBit_succ_zero (m : Nat) : Nat.testBit (m.succ) 0 = ! Nat.testBit m 0 := by
  -- Express `m` as `Nat.bit (m.testBit 0) (m >>> 1)` and split on the low bit.
  have hm : Nat.bit (Nat.testBit m 0) (m >>> 1) = m := by
    simpa using (Nat.bit_testBit_zero_shiftRight_one m)
  cases hb : Nat.testBit m 0 with
  | false =>
      -- even: `m = bit false t`, so `m+1 = bit true t`.
      have hm' : Nat.bit false (m >>> 1) = m := by
        simpa [hb] using hm
      have hms : m.succ = Nat.bit true (m >>> 1) := by
        calc
          m.succ = (Nat.bit false (m >>> 1)).succ := by simpa [hm']
          _ = Nat.bit true (m >>> 1) := by
                -- `bit false t = 2*t`, so successor is `2*t+1 = bit true t`.
                simp [Nat.bit, Nat.succ_eq_add_one, Nat.add_assoc]
      -- Rewrite the RHS using `hb` and finish by `Nat.testBit_bit_zero`.
      simp only [Bool.not_false]
      rw [hms]
      exact Nat.testBit_bit_zero true (m >>> 1)
  | true =>
      -- odd: `m = bit true t`, so `m+1 = bit false (t+1)`.
      have hm' : Nat.bit true (m >>> 1) = m := by
        simpa [hb] using hm
      have hms : m.succ = Nat.bit false ((m >>> 1).succ) := by
        calc
          m.succ = (Nat.bit true (m >>> 1)).succ := by simpa [hm']
          _ = Nat.bit false ((m >>> 1).succ) := by
                -- `bit true t = 2*t+1`, so successor is `2*(t+1) = bit false (t+1)`.
                -- `simp` reduces to an arithmetic identity; `omega` closes it.
                simp [Nat.bit, Nat.succ_eq_add_one, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm,
                  Nat.add_comm]
                omega
      -- Rewrite the RHS using `hb` and finish by `Nat.testBit_bit_zero`.
      simp only [Bool.not_true]
      rw [hms]
      exact Nat.testBit_bit_zero false ((m >>> 1).succ)

/-!
### `ofNat` and `gc` shift lemmas

When we pass from width `k` to width `k+1`, and look at indices `Fin.succ j`,
`ofNat (Nat.bit b m)` behaves like `ofNat m` (a right-shift of the binary representation).
This is the usual right-shift on binary representations.
-/

private lemma ofNat_bit_false_zero {k : Nat} (m : Nat) :
    (ofNat (k := Nat.succ k) (Nat.bit false m)) 0 = false := by
  simp [ofNat, Nat.testBit_bit_zero]

private lemma ofNat_bit_true_zero {k : Nat} (m : Nat) :
    (ofNat (k := Nat.succ k) (Nat.bit true m)) 0 = true := by
  simp [ofNat, Nat.testBit_bit_zero]

private lemma ofNat_bit_succ {k : Nat} (b : Bool) (m : Nat) (j : Fin k) :
    (ofNat (k := Nat.succ k) (Nat.bit b m)) (Fin.succ j) = (ofNat (k := k) m) j := by
  simp [ofNat, Nat.testBit_bit_succ]

private lemma getBit_ofNat_bit_succ {k : Nat} (b : Bool) (m : Nat) (j : Fin k) :
    getBit (ofNat (k := Nat.succ k) (Nat.bit b m)) (j.val + 2) =
      getBit (ofNat (k := k) m) (j.val + 1) := by
  have hjle : j.val.succ ≤ k := Nat.succ_le_of_lt j.isLt
  by_cases h : j.val.succ < k
  · -- both indices are in range
    have hR : j.val + 1 < k := by
      simpa [Nat.succ_eq_add_one] using h
    have hL : j.val + 2 < Nat.succ k := by
      -- from `j.val + 1 < k` we get `j.val + 2 < k + 1`
      have : j.val + 1 < k := hR
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using (Nat.succ_lt_succ this)
    -- unfold `getBit` and reduce to `Nat.testBit_bit_succ`
    simp [getBit, hL, hR, ofNat, Nat.testBit_bit_succ, Nat.succ_eq_add_one, Nat.add_assoc]
  · -- `j` is the last index, so both `getBit`s are out of range and return `false`
    have hEq : j.val.succ = k := by
      have hkge : k ≤ j.val.succ := Nat.le_of_not_gt h
      exact Nat.le_antisymm hjle hkge
    have hk : j.val + 1 = k := by
      simpa [Nat.succ_eq_add_one] using hEq
    have hR : ¬ j.val + 1 < k := by
      -- rewrite to `¬ k < k`
      simpa [hk] using (Nat.lt_irrefl k)
    have hL : ¬ j.val + 2 < Nat.succ k := by
      have hk' : j.val + 2 = Nat.succ k := by
        -- `j.val + 2 = (j.val + 1) + 1`
        simp [hk, Nat.succ_eq_add_one, Nat.add_assoc]
      -- rewrite to `¬ succ k < succ k`
      simpa [hk'] using (Nat.lt_irrefl (Nat.succ k))
    simp [getBit, hL, hR]

private lemma gc_ofNat_bit_succ {k : Nat} (b : Bool) (m : Nat) (j : Fin k) :
    (gc (ofNat (k := Nat.succ k) (Nat.bit b m))) (Fin.succ j) = (gc (ofNat (k := k) m)) j := by
  -- unfold `gc`; both sides are `bxor` of the same two shifted bits
  simp [gc, xor, shr1, ofNat_bit_succ, getBit_ofNat_bit_succ, Nat.add_assoc, Nat.succ_eq_add_one]

/-!
### Main adjacency lemma

Assuming `tsb i < k` (i.e. there is a `0` bit among the lowest `k` bits),
incrementing `i` does not wrap in the `k`-bit truncation, and the Gray code
changes exactly in bit `tsb i`.
-/

theorem xor_gc_ofNat_succ_eq_oneHotFin
    {k : Nat} (i : Nat) (ht : tsb i < k) :
    xor (gc (ofNat (k := k) i)) (gc (ofNat (k := k) i.succ)) = oneHotFin ⟨tsb i, ht⟩ := by
  induction k generalizing i with
  | zero =>
      -- `tsb i < 0` is impossible
      cases (Nat.not_lt_zero _ ht)
  | succ k ih =>
      -- split on `i % 2` (0 or 1)
      have hlt : i % 2 < 2 := Nat.mod_lt _ (by decide)
      cases hmod : i % 2 with
      | zero =>
          -- even case: `tsb i = 0`, and `i = bit0 (i/2)`
          let m : Nat := i / 2
          have hi : i = Nat.bit false m := by
              have h := Nat.div_add_mod i 2
              have hm2 : 2 * m = i := by
                -- `2 * (i / 2) + i % 2 = i`
                simpa [m, hmod] using h
              calc
                i = 2 * m := by simpa using hm2.symm
                _ = Nat.bit false m := by simp [Nat.bit]
          have hsucc : i.succ = Nat.bit true m := by
              calc
                i.succ = (Nat.bit false m).succ := by simpa [hi]
                _ = Nat.bit true m := by simp [Nat.bit, Nat.succ_eq_add_one, Nat.add_assoc]
          have htsb : tsb i = 0 := by
            simp [tsb, hmod]
          -- show pointwise equality
          ext j
          refine Fin.cases ?_ ?_ j
          · -- j = 0
            -- Reduce to a pure Bool computation:
            -- the bit-1 terms in `gc` agree, while the bit-0 terms differ.
            have htsb2 : tsb (2 * m) = 0 := by
              simpa [hi, Nat.bit] using htsb
            have htb0 : (2 * m).testBit 1 = m.testBit 0 := by
              simpa [Nat.bit] using (Nat.testBit_bit_succ 0 false m)
            have htb1 : (2 * m + 1).testBit 1 = m.testBit 0 := by
              simpa [Nat.bit] using (Nat.testBit_bit_succ 0 true m)
            -- After rewriting, it's just `A XOR (not A) = true`.
            have hdec : decide (tsb (2 * m) = 0) = true := by simp [htsb2]
            -- Work with the simplified goal.
            -- `simp` produces the Bool expression; then case split on `A`.
            simp [oneHotFin, hi, hsucc, gc, xor, shr1, getBit, ofNat, htb0, htb1, hdec]
            cases (decide (0 < k) && m.testBit 0) <;> simp [BV.bxor] <;>
              -- `simp` reduces the remaining Bool goal to a tautology about `k` and `m % 2`.
              cases Nat.eq_zero_or_pos k with
              | inl hk0 =>
                  exact Or.inr (Or.inl hk0)
              | inr hkpos =>
                  cases Nat.mod_two_eq_zero_or_one m with
                  | inl hm0 =>
                      exact Or.inr (Or.inr hm0)
                  | inr hm1 =>
                      exact Or.inl ⟨hkpos, hm1⟩
          · intro j
            -- higher bits of Gray codes agree, so XOR is false, and the one-hot at `0` is also false here.
            have hL :
                (xor (gc (ofNat (k := Nat.succ k) i)) (gc (ofNat (k := Nat.succ k) i.succ))) (Fin.succ j) =
                  false := by
              -- Rewrite `i`/`i.succ` into `Nat.bit` form, then shift back to the width-`k` statement.
              have hgc0 :
                  (gc (ofNat (k := Nat.succ k) (Nat.bit false m))) (Fin.succ j) =
                    (gc (ofNat (k := k) m)) j :=
                gc_ofNat_bit_succ (k := k) (b := false) (m := m) (j := j)
              have hgc1 :
                  (gc (ofNat (k := Nat.succ k) (Nat.bit true m))) (Fin.succ j) =
                    (gc (ofNat (k := k) m)) j :=
                gc_ofNat_bit_succ (k := k) (b := true) (m := m) (j := j)
              change
                  bxor ((gc (ofNat (k := Nat.succ k) i)) (Fin.succ j))
                    ((gc (ofNat (k := Nat.succ k) i.succ)) (Fin.succ j)) = false
              rw [hsucc, hi, hgc0, hgc1]
              simpa using (bxor_self ((gc (ofNat (k := k) m)) j))
            have hneq : (Fin.succ j : Fin (Nat.succ k)) ≠ ⟨tsb i, ht⟩ := by
              intro hEq
              have hval : (Fin.succ j : Fin (Nat.succ k)).val = tsb i := congrArg Fin.val hEq
              have : j.val.succ = 0 := by simpa [htsb] using hval
              exact Nat.succ_ne_zero _ this
            have hR : (oneHotFin ⟨tsb i, ht⟩) (Fin.succ j) = false := by
              -- `decide (Fin.succ j = g)` is false because the values differ.
              have : decide ((Fin.succ j : Fin (Nat.succ k)) = (⟨tsb i, ht⟩ : Fin (Nat.succ k))) = false := by
                exact (decide_eq_false_iff_not).2 hneq
              simpa [oneHotFin] using this
            -- Combine the two sides.
            simpa [hL, hR]
      | succ r =>
          cases r with
          | zero =>
              -- odd case: `i = bit1 (i/2)`, `i+1 = bit0 ((i/2)+1)`
              let m : Nat := i / 2
              have hi : i = Nat.bit true m := by
                      have h := Nat.div_add_mod i 2
                      have hm2 : 2 * m + 1 = i := by
                        -- `2 * (i / 2) + i % 2 = i`
                        simpa [m, hmod, Nat.add_assoc] using h
                      calc
                        i = 2 * m + 1 := by simpa using hm2.symm
                        _ = Nat.bit true m := by simp [Nat.bit]
              have hsucc : i.succ = Nat.bit false (m.succ) := by
                calc
                  i.succ = (Nat.bit true m).succ := by simpa [hi]
                  _ = Nat.bit false (m.succ) := by
                        simp [Nat.bit, Nat.succ_eq_add_one, Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm,
                          Nat.add_comm]
                        omega
              have htsb' : tsb i = Nat.succ (tsb (i / 2)) := by
                -- `i % 2 = 1` so we take the recursive branch
                have hmod1 : i % 2 = 1 := by simpa using hmod
                -- Use the recursion equation for `tsb` (avoids unfolding the recursive call).
                rw [tsb.eq_1]
                simp [hmod1]
              have htsb : tsb i = Nat.succ (tsb m) := by
                simpa [m] using htsb'
              have ht' : tsb m < k := by
                -- from `succ (tsb m) < succ k`
                have : Nat.succ (tsb m) < Nat.succ k := by simpa [htsb] using ht
                exact Nat.lt_of_succ_lt_succ this
              have ih' := ih (i := m) ht'
              ext j
              refine Fin.cases ?_ ?_ j
              · -- bit 0: unchanged for odd step
                cases k with
                | zero =>
                    cases (Nat.not_lt_zero _ ht')
                | succ k =>
                    have h1 : (1 : Nat) < Nat.succ (Nat.succ k) := by
                      simpa using Nat.succ_lt_succ (Nat.succ_pos k)
                    have hR : (oneHotFin ⟨tsb i, ht⟩) 0 = false := by
                      simp [oneHotFin, htsb]
                    have hL :
                        (xor (gc (ofNat (k := Nat.succ (Nat.succ k)) i))
                              (gc (ofNat (k := Nat.succ (Nat.succ k)) i.succ))) 0 = false := by
                      change
                          bxor ((gc (ofNat (k := Nat.succ (Nat.succ k)) i)) 0)
                            ((gc (ofNat (k := Nat.succ (Nat.succ k)) i.succ)) 0) = false
                      rw [hsucc, hi]
                      have hx0 :
                          (ofNat (k := Nat.succ (Nat.succ k)) (Nat.bit true m)) 0 = true := by
                        dsimp [ofNat]
                        simpa using (Nat.testBit_bit_zero true m)
                      have hx1 :
                          getBit (ofNat (k := Nat.succ (Nat.succ k)) (Nat.bit true m)) 1 = m.testBit 0 := by
                        simp [getBit, h1]
                        dsimp [ofNat]
                        simpa using (Nat.testBit_bit_succ 0 true m)
                      have hy0 :
                          (ofNat (k := Nat.succ (Nat.succ k)) (Nat.bit false (m.succ))) 0 = false := by
                        dsimp [ofNat]
                        simpa using (Nat.testBit_bit_zero false (m.succ))
                      have hy1 :
                          getBit (ofNat (k := Nat.succ (Nat.succ k)) (Nat.bit false (m.succ))) 1 =
                            (m.succ).testBit 0 := by
                        simp [getBit, h1]
                        dsimp [ofNat]
                        simpa using (Nat.testBit_bit_succ 0 false (m.succ))
                      have hgx :
                          (gc (ofNat (k := Nat.succ (Nat.succ k)) (Nat.bit true m))) 0 =
                            bxor true (m.testBit 0) := by
                        dsimp [gc, xor, shr1]
                        have hbit : Nat.bit true m = 2 * m + 1 := by
                          simp [Nat.bit]
                        rw [← hbit]
                        rw [hx0, hx1]
                      have hgy :
                          (gc (ofNat (k := Nat.succ (Nat.succ k)) (Nat.bit false (m.succ)))) 0 =
                            bxor false ((m.succ).testBit 0) := by
                        dsimp [gc, xor, shr1]
                        have hbit : Nat.bit false (m.succ) = 2 * (m + 1) := by
                          simp [Nat.bit, Nat.succ_eq_add_one]
                        rw [← hbit]
                        rw [hy0, hy1]
                      rw [hgx, hgy, bxor_false_left, testBit_succ_zero m]
                      cases hb : m.testBit 0 <;> simp [BV.bxor, hb]
                    rw [hL, hR]
              · intro j
                -- lift IH through `Fin.succ`
                -- LHS at `Fin.succ j` reduces to the IH stream at `j`
                -- and RHS reduces by `decide` congruence.
                --
                -- First rewrite the `gc` terms using the shift lemmas.
                -- Then apply IH.
                have :
                    (xor (gc (ofNat (k := k) m)) (gc (ofNat (k := k) m.succ))) j =
                      (oneHotFin ⟨tsb m, ht'⟩) j := by
                  simpa [oneHotFin] using congrArg (fun f => f j) ih'
                -- Normalize to the width-`succ k` statement.
                have hgc0 :
                    (gc (ofNat (k := Nat.succ k) (Nat.bit true m))) (Fin.succ j) =
                      (gc (ofNat (k := k) m)) j :=
                  gc_ofNat_bit_succ (k := k) (b := true) (m := m) (j := j)
                have hgc1 :
                    (gc (ofNat (k := Nat.succ k) (Nat.bit false (m.succ)))) (Fin.succ j) =
                      (gc (ofNat (k := k) m.succ)) j :=
                  gc_ofNat_bit_succ (k := k) (b := false) (m := m.succ) (j := j)
                have hg : (⟨tsb i, ht⟩ : Fin (Nat.succ k)) = Fin.succ ⟨tsb m, ht'⟩ := by
                  ext
                  simp [htsb]
                have hdec :
                    decide ((Fin.succ j : Fin (Nat.succ k)) = ⟨tsb i, ht⟩) =
                      decide (j = ⟨tsb m, ht'⟩) := by
                  -- Rewrite the target index into a `Fin.succ` form, then use injectivity of `Fin.succ`.
                  rw [hg]
                  have h :
                      (Fin.succ j = (Fin.succ ⟨tsb m, ht'⟩ : Fin (Nat.succ k))) ↔
                        (j = ⟨tsb m, ht'⟩) := by
                    simpa using (Fin.succ_inj (a := j) (b := ⟨tsb m, ht'⟩))
                  exact decide_eq_decide.mpr h
                calc
                  (xor (gc (ofNat (k := Nat.succ k) i)) (gc (ofNat (k := Nat.succ k) i.succ))) (Fin.succ j)
                      =
                      (xor (gc (ofNat (k := k) m)) (gc (ofNat (k := k) m.succ))) j := by
                        change
                            bxor ((gc (ofNat (k := Nat.succ k) i)) (Fin.succ j))
                              ((gc (ofNat (k := Nat.succ k) i.succ)) (Fin.succ j)) =
                              bxor ((gc (ofNat (k := k) m)) j) ((gc (ofNat (k := k) m.succ)) j)
                        rw [hsucc, hi, hgc0, hgc1]
                  _ = (oneHotFin ⟨tsb m, ht'⟩) j := by
                        exact this
                  _ = decide (j = ⟨tsb m, ht'⟩) := by
                        rfl
                  _ = decide ((Fin.succ j : Fin (Nat.succ k)) = ⟨tsb i, ht⟩) := by
                        simpa using hdec.symm
          | succ r2 =>
              -- impossible since `i % 2 < 2`
              exfalso
              have : (Nat.succ (Nat.succ r2)) < 2 := by simpa [hmod] using hlt
              exact Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))) this

theorem gc_ofNat_succ_adjacent
    {k : Nat} (i : Nat) (ht : tsb i < k) :
    ∃ g : Fin k, xor (gc (ofNat (k := k) i)) (gc (ofNat (k := k) i.succ)) = oneHotFin g := by
  refine ⟨⟨tsb i, ht⟩, ?_⟩
  simpa using xor_gc_ofNat_succ_eq_oneHotFin (k := k) i ht

end BV

end AnisoHilbert
