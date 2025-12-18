import Mathlib

import AnisoHilbert.AdjacencyLemmas
import AnisoHilbert.BVNatLemmas
import AnisoHilbert.DecodeHeadPlaneLemmas
import AnisoHilbert.EmbedLemmas
import AnisoHilbert.Loops
import AnisoHilbert.RotLOneHotLemmas

namespace AnisoHilbert

namespace State

open BV

/-- Entry corner label (Hamilton's `e`) for a Hilbert state. -/
def entryCorner {n : Nat} {A : List (Axis n)} (st : State n A) : BV A.length :=
  st.e

/-- Exit corner label `f = e ⊕ 2^d` (in one-hot form) for a Hilbert state. -/
def exitCorner {n : Nat} {A : List (Axis n)} (st : State n A) : BV A.length :=
  BV.xor st.e (BV.oneHotFin st.dPos)

end State

namespace BV

open scoped BigOperators

theorem xor_assoc {k : Nat} (x y z : BV k) : xor (xor x y) z = xor x (xor y z) := by
  funext i
  simpa [xor] using (BV.bxor_assoc (x i) (y i) (z i))

theorem xor_comm {k : Nat} (x y : BV k) : xor x y = xor y x := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [xor, bxor, hx, hy]

theorem rotL_zero {k : Nat} (r : Nat) : BV.rotL (k := k) r BV.zero = BV.zero := by
  cases k with
  | zero => rfl
  | succ k' =>
      funext i
      simp [BV.rotL, BV.zero]

theorem xor_zero_left {k : Nat} (x : BV k) : BV.xor BV.zero x = x := by
  funext i
  cases hx : x i <;> simp [BV.xor, BV.bxor, hx, BV.zero]

theorem xor_zero_right {k : Nat} (x : BV k) : BV.xor x BV.zero = x := by
  funext i
  cases hx : x i <;> simp [BV.xor, BV.bxor, hx, BV.zero]

theorem gc_zero {k : Nat} : BV.gc (k := k) BV.zero = BV.zero := by
  funext i
  simp [BV.gc, BV.shr1, BV.zero, BV.xor, BV.bxor, getBit]

theorem sub_one_lt_of_pos {k : Nat} (hk : 0 < k) : k - 1 < k :=
  Nat.sub_lt_of_pos_le (by decide : 0 < 1) (Nat.succ_le_of_lt hk)

private theorem two_pow_ge_two {k : Nat} (hk : 0 < k) : 2 ≤ 2 ^ k := by
  cases k with
  | zero =>
      cases (Nat.not_lt_zero 0 hk)
  | succ k' =>
      -- `2^(k'+1) = 2^k' * 2 ≥ 1 * 2 = 2`.
      have hpow : 1 ≤ 2 ^ k' := Nat.succ_le_iff.2 (Nat.pow_pos (n := k') (Nat.succ_pos 1))
      have hmul : 2 * 1 ≤ 2 * (2 ^ k') := Nat.mul_le_mul_left 2 hpow
      -- rewrite `2^(k'+1)` and commute the multiplication.
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul

private theorem tsb_two_pow_sub_one : ∀ k : Nat, tsb (2 ^ k - 1) = k := by
  intro k
  induction k with
  | zero =>
      simp [tsb]
  | succ k ih =>
      -- `2^(k+1) - 1` is odd, so `tsb` recurses once.
      have hmod : (2 ^ Nat.succ k - 1) % 2 = 1 := by
        -- `2^(k+1)` is even.
        have : (2 ^ Nat.succ k) % 2 = 0 := by
          simp [Nat.pow_succ, Nat.mul_mod]
        -- so `2^(k+1) - 1` is odd
        -- `simp` knows how to reduce `% 2` on `x - 1` when `x % 2 = 0`.
        have hk2 : 2 ≤ 2 ^ Nat.succ k := two_pow_ge_two (k := Nat.succ k) (Nat.succ_pos k)
        -- use the fact `2 ^ (k+1) ≥ 1` so subtraction is not clamped
        have hpos : 0 < 2 ^ Nat.succ k := Nat.pow_pos (n := Nat.succ k) (Nat.succ_pos 1)
        -- brute force via rewriting to `2 * t + 1`
        have hrepr : 2 ^ Nat.succ k - 1 = 1 + 2 * (2 ^ k - 1) := by
          -- set `x := 2^k` to keep the arithmetic linear
          set x : Nat := 2 ^ k
          have hx : 0 < x := Nat.pow_pos (n := k) (Nat.succ_pos 1)
          -- `2^(k+1) = 2*x`
          calc
            2 ^ Nat.succ k - 1 = 2 * x - 1 := by
              simp [x, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
            _ = 1 + 2 * (x - 1) := by
              -- `2*x - 1 = 2*(x-1) + 1`, then commute.
              have hx1 : 1 ≤ x := Nat.succ_le_of_lt hx
              have hx2 : 2 ≤ 2 * x := Nat.le_trans (by decide : 2 ≤ 2) (Nat.mul_le_mul_left 2 hx1)
              -- show `2*x - 1 = 2*x - 2 + 1`
              have hsub : 2 * x - 1 = 2 * x - 2 + 1 := by
                have hxA : 1 ≤ 2 * x := Nat.le_trans (by decide : 1 ≤ 2) hx2
                apply (Nat.sub_eq_iff_eq_add hxA).2
                -- `2*x = (2*x - 2 + 1) + 1`
                calc
                  2 * x = 2 * x - 2 + 2 := (Nat.sub_add_cancel hx2).symm
                  _ = (2 * x - 2 + 1) + 1 := by omega
              -- rewrite `2*(x-1)` as `2*x - 2`
              -- and normalize to `1 + 2*(x-1)`
              calc
                2 * x - 1 = 2 * x - 2 + 1 := hsub
                _ = 2 * (x - 1) + 1 := by
                      simp [Nat.mul_sub_left_distrib, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
                        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                _ = 1 + 2 * (x - 1) := by ac_rfl
            _ = 1 + 2 * (2 ^ k - 1) := by simp [x, Nat.mul_sub_left_distrib, Nat.mul_assoc]
        -- now reduce modulo 2 from the explicit representation
        simpa [hrepr] using (by decide : (1 + 2 * (2 ^ k - 1)) % 2 = 1)
      have hdiv : (2 ^ Nat.succ k - 1) / 2 = 2 ^ k - 1 := by
        -- Use the same `1 + 2*(...)` representation and `add_mul_div_left`.
        have hrepr : 2 ^ Nat.succ k - 1 = 1 + 2 * (2 ^ k - 1) := by
          -- Reuse `hmod`-proof's internal representation.
          -- (Duplicated for simplicity.)
          set x : Nat := 2 ^ k
          have hx : 0 < x := Nat.pow_pos (n := k) (Nat.succ_pos 1)
          calc
            2 ^ Nat.succ k - 1 = 2 * x - 1 := by
              simp [x, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
            _ = 1 + 2 * (x - 1) := by
              have hx1 : 1 ≤ x := Nat.succ_le_of_lt hx
              have hx2 : 2 ≤ 2 * x := Nat.le_trans (by decide : 2 ≤ 2) (Nat.mul_le_mul_left 2 hx1)
              have hsub : 2 * x - 1 = 2 * x - 2 + 1 := by
                have hxA : 1 ≤ 2 * x := Nat.le_trans (by decide : 1 ≤ 2) hx2
                apply (Nat.sub_eq_iff_eq_add hxA).2
                calc
                  2 * x = 2 * x - 2 + 2 := (Nat.sub_add_cancel hx2).symm
                  _ = (2 * x - 2 + 1) + 1 := by omega
              calc
                2 * x - 1 = 2 * x - 2 + 1 := hsub
                _ = 2 * (x - 1) + 1 := by
                      simp [Nat.mul_sub_left_distrib, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
                        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
                _ = 1 + 2 * (x - 1) := by ac_rfl
            _ = 1 + 2 * (2 ^ k - 1) := by simp [x, Nat.mul_sub_left_distrib, Nat.mul_assoc]
        -- divide by 2
        have := congrArg (fun n => n / 2) hrepr
        -- `Nat.add_mul_div_left` with `y = 2`
        simpa [Nat.add_mul_div_left, Nat.div_eq_of_lt, Nat.succ_eq_add_one] using this
      -- Now compute `tsb`.
      simp [tsb, hmod, hdiv, ih]

private theorem childDir_two_pow_sub_one {k : Nat} (hk : 0 < k) :
    childDir k (2 ^ k - 1) = 0 := by
  have htsb : tsb (2 ^ k - 1) = k := tsb_two_pow_sub_one k
  -- For `w ≠ 0`, `2^k - 1` is odd, so `childDir` uses the `w % 2 = 1` branch.
  have hne : (2 ^ k - 1) ≠ 0 := by
    have hk2 : 2 ≤ 2 ^ k := two_pow_ge_two (k := k) hk
    -- `2^k - 1 ≥ 1`
    have : 1 ≤ 2 ^ k - 1 := by
      have h1lt : 1 < 2 ^ k := Nat.lt_of_lt_of_le (by decide : 1 < 2) hk2
      exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt h1lt)
    exact Nat.ne_of_gt (Nat.pos_of_ne_zero (by
      intro h0
      have : 1 ≤ (0 : Nat) := by simpa [h0] using this
      exact Nat.not_succ_le_zero 0 this))
  have hodd : (2 ^ k - 1) % 2 ≠ 0 := by
    -- Oddness: `w % 2 = 1`.
    have : (2 ^ k - 1) % 2 = 1 := by
      -- `simp` reduces this goal to the assumption `0 < k`.
      simpa using hk
    exact (Nat.mod_two_ne_zero).2 this
  -- Unfold `childDir` and simplify.
  simp [childDir, hne, Nat.mod_two_ne_zero.mp hodd, htsb]

private theorem gc_ofNat_two_pow_sub_one_eq_oneHotFin_last {k : Nat} (hk : 0 < k) :
    gc (ofNat (k := k) (2 ^ k - 1)) = oneHotFin ⟨k - 1, sub_one_lt_of_pos hk⟩ := by
  cases k with
  | zero =>
      cases (Nat.not_lt_zero 0 hk)
  | succ k' =>
      let n : Nat := Nat.succ k'
      let last : Fin n := ⟨k', Nat.lt_succ_self k'⟩
      funext i
      by_cases hlast : i = last
      · subst hlast
        -- At the last bit: `x = 1`, `x>>1 = 0`.
        simp [n, gc, xor, shr1, ofNat, getBit, oneHotFin, last, Nat.testBit_two_pow_sub_one, bxor]
      ·
        -- If `i ≠ last`, then `i.val < k'`.
        have hi : (i.val : Nat) < k' := by
          have hiLe : (i.val : Nat) ≤ k' := (Nat.lt_succ_iff.mp i.isLt)
          refine Nat.lt_of_le_of_ne hiLe ?_
          intro hEq
          apply hlast
          apply Fin.ext
          simpa [last] using hEq
        have hiSucc : (i.val : Nat) + 1 < n := by
          have hiLe' : (i.val : Nat).succ ≤ k' := Nat.succ_le_of_lt hi
          have : (i.val : Nat).succ < n := Nat.lt_of_le_of_lt hiLe' (Nat.lt_succ_self k')
          simpa [n, Nat.succ_eq_add_one] using this

        -- For `i ≠ last`, both `x i` and `(x>>1) i` are `1`, so Gray code bit is `0`.
        simp [n, gc, xor, shr1, ofNat, getBit, oneHotFin, last, hlast, Nat.testBit_two_pow_sub_one, i.isLt,
          hiSucc, hi, bxor]

private theorem tsb_two_pow_sub_two {k : Nat} (hk : 0 < k) : tsb (2 ^ k - 2) = 0 := by
  -- `2` divides `2^k - 2`, so the number is even and `tsb` is `0`.
  have hpow : 2 ∣ 2 ^ k := by
    cases k with
    | zero =>
        cases (Nat.not_lt_zero 0 hk)
    | succ k' =>
        refine ⟨2 ^ k', ?_⟩
        simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have h2 : 2 ∣ 2 := ⟨1, by simp⟩
  have hdvd : 2 ∣ 2 ^ k - 2 := Nat.dvd_sub hpow h2
  have hmod : (2 ^ k - 2) % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  simp [tsb, hmod]

private theorem gc_ofNat_two_pow_sub_two_eq_xor_oneHotFin_zero_last {k : Nat} (hk : 0 < k) :
    gc (ofNat (k := k) (2 ^ k - 2))
      =
    xor (oneHotFin ⟨0, hk⟩) (oneHotFin ⟨k - 1, sub_one_lt_of_pos hk⟩) := by
  let i : Nat := 2 ^ k - 2
  have htsb : tsb i = 0 := by
    simpa [i] using tsb_two_pow_sub_two (k := k) hk
  have ht : tsb i < k := by
    simpa [htsb] using hk
  have hAdj :
      xor (gc (ofNat (k := k) i)) (gc (ofNat (k := k) i.succ)) = oneHotFin ⟨tsb i, ht⟩ := by
    simpa [i] using (xor_gc_ofNat_succ_eq_oneHotFin (k := k) i ht)

  have hIdx : (⟨tsb i, ht⟩ : Fin k) = ⟨0, hk⟩ := by
    apply Fin.ext
    simp [htsb]

  have hAdj' :
      xor (gc (ofNat (k := k) i)) (gc (ofNat (k := k) i.succ)) = oneHotFin ⟨0, hk⟩ := by
    simpa [hIdx] using hAdj

  have hSolve :=
    congrArg (fun t => xor t (gc (ofNat (k := k) i.succ))) hAdj'
  have hLeft :
      xor (xor (gc (ofNat (k := k) i)) (gc (ofNat (k := k) i.succ))) (gc (ofNat (k := k) i.succ))
        =
      gc (ofNat (k := k) i) := by
    simpa using (BV.xor_invol_right (x := gc (ofNat (k := k) i)) (e := gc (ofNat (k := k) i.succ)))

  have hgc2 : gc (ofNat (k := k) i.succ) = oneHotFin ⟨k - 1, sub_one_lt_of_pos hk⟩ := by
    have hk2 : 2 ≤ 2 ^ k := two_pow_ge_two (k := k) hk
    have h1lt : 1 < 2 ^ k := Nat.lt_of_lt_of_le (by decide : 1 < 2) hk2
    have hiSucc : i.succ = 2 ^ k - 1 := by
      -- `(a-2)+1 = a-1` for `a ≥ 2`.
      set a : Nat := 2 ^ k
      have ha : 2 ≤ a := by simpa [a] using hk2
      have ha1pos : 0 < a - 1 := Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 2) ha)
      have ha1 : 1 ≤ a - 1 := Nat.succ_le_of_lt ha1pos
      have hsub : a - 1 - 1 = a - 2 := by
        have := (Nat.sub_add_eq a 1 1).symm
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      calc
        i.succ = (a - 2).succ := by simp [i, a]
        _ = (a - 2) + 1 := by simp [Nat.succ_eq_add_one]
        _ = (a - 1 - 1) + 1 := by simp [hsub]
        _ = a - 1 := Nat.sub_add_cancel ha1
        _ = 2 ^ k - 1 := by simp [a]
    -- Apply the `gc`-of-all-ones lemma.
    simpa [hiSucc.symm] using gc_ofNat_two_pow_sub_one_eq_oneHotFin_last (k := k) hk

  -- Solve for `gc(ofNat i)` using XOR involution.
  have hx : gc (ofNat (k := k) i) = xor (oneHotFin ⟨0, hk⟩) (gc (ofNat (k := k) i.succ)) :=
    hLeft.symm.trans hSolve
  -- Substitute the computed `gc(ofNat i.succ)`.
  simpa [i, hgc2, xor_comm] using hx

theorem childEntry_two_pow_sub_one_eq_xor_oneHotFin_zero_last {k : Nat} (hk : 0 < k) :
    childEntry k (2 ^ k - 1)
      =
    xor (oneHotFin ⟨0, hk⟩) (oneHotFin ⟨k - 1, sub_one_lt_of_pos hk⟩) := by
  -- `2^k - 1 ≠ 0` for `k > 0`.
  have hk2 : 2 ≤ 2 ^ k := two_pow_ge_two (k := k) hk
  have h1lt : 1 < 2 ^ k := Nat.lt_of_lt_of_le (by decide : 1 < 2) hk2
  have hne : (2 ^ k - 1) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt h1lt)

  -- The even predecessor `2^k - 2` is divisible by `2`, so `2 * ((2^k - 2)/2) = 2^k - 2`.
  have hpow : 2 ∣ 2 ^ k := by
    cases k with
    | zero =>
        cases (Nat.not_lt_zero 0 hk)
    | succ k' =>
        refine ⟨2 ^ k', ?_⟩
        simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have h2 : 2 ∣ 2 := ⟨1, by simp⟩
  have hdvd : 2 ∣ 2 ^ k - 2 := Nat.dvd_sub hpow h2
  have hsub : (2 ^ k - 1) - 1 = 2 ^ k - 2 := by
    -- `(a-1)-1 = a-2`
    have := (Nat.sub_add_eq (2 ^ k) 1 1).symm
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  have hj : 2 * (((2 ^ k - 1) - 1) / 2) = 2 ^ k - 2 := by
    -- rewrite the inner subtraction and cancel the division (evenness)
    simpa [hsub] using (Nat.mul_div_cancel' hdvd)

  -- Unfold `childEntry` and reduce to the computed Gray code for `2^k - 2`.
  simp [childEntry, hne, hj, gc_ofNat_two_pow_sub_two_eq_xor_oneHotFin_zero_last (k := k) hk]

end BV

namespace State

open BV

theorem entryCorner_stateUpdate_toNat_zero
    {n : Nat} {A : List (Axis n)} (st : State n A) (w : BV A.length)
    (hw : BV.toNat w = 0) :
    entryCorner (stateUpdate A st w) = entryCorner st := by
  -- `w = 0` implies `childEntry … w = 0`, so the entry mask is unchanged.
  simp [entryCorner, stateUpdate, hw, childEntry, BV.rotL_zero, BV.xor_zero_right, State.mk']

/-!
If the current digit is maximal (`w = 2^k - 1`), then descending into that child preserves the
exit-corner label `f = e ⊕ 2^d`.

This is the key invariant used to show that an all-max suffix of digits decodes to an exit corner.
-/
theorem exitCorner_stateUpdate_toNat_two_pow_sub_one
    {n : Nat} {A : List (Axis n)} (st : State n A) (w : BV A.length)
    (hw : BV.toNat w = 2 ^ A.length - 1) :
    exitCorner (stateUpdate A st w) = exitCorner st := by
  classical
  have hk : 0 < A.length := State.length_pos st
  let r : Nat := st.dPos.val + 1
  let dPosNext : Fin A.length := ⟨(st.dPos.val + 1) % A.length, Nat.mod_lt _ hk⟩

  have hEntry :
      childEntry A.length (2 ^ A.length - 1)
        =
      xor (oneHotFin ⟨0, hk⟩) (oneHotFin ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩) := by
    simpa using BV.childEntry_two_pow_sub_one_eq_xor_oneHotFin_zero_last (k := A.length) hk

  have hDir : childDir A.length (2 ^ A.length - 1) = 0 := by
    simpa using (BV.childDir_two_pow_sub_one (k := A.length) hk)

  have hRot0 :
      rotL (k := A.length) r (oneHotFin ⟨0, hk⟩) = oneHotFin dPosNext := by
    have h :=
      BV.rotL_oneHotFin_eq_of_pos (k := A.length) hk r ⟨0, hk⟩
    have hIdx : (⟨(0 + r) % A.length, Nat.mod_lt _ hk⟩ : Fin A.length) = dPosNext := by
      apply Fin.ext
      simp [dPosNext, r, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    simpa [hIdx] using h

  have hRotLast :
      rotL (k := A.length) r (oneHotFin ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩) =
        oneHotFin st.dPos := by
    have h :=
      BV.rotL_oneHotFin_eq_of_pos (k := A.length) hk r ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩
    have hk1 : 1 ≤ A.length := Nat.succ_le_of_lt hk
    have hLastVal : ((A.length - 1) + r) % A.length = st.dPos.val := by
      calc
        ((A.length - 1) + r) % A.length
            = ((A.length - 1) + (st.dPos.val + 1)) % A.length := by
                simp [r]
        _ = (((A.length - 1) + 1) + st.dPos.val) % A.length := by
              have h' : (A.length - 1) + (st.dPos.val + 1) = ((A.length - 1) + 1) + st.dPos.val := by
                ac_rfl
              simpa [h']
        _ = (A.length + st.dPos.val) % A.length := by
              simp [Nat.sub_add_cancel hk1]
        _ = st.dPos.val % A.length := by
              simp [Nat.add_mod]
        _ = st.dPos.val := Nat.mod_eq_of_lt st.dPos.isLt
    have hIdx :
        (⟨((A.length - 1) + r) % A.length, Nat.mod_lt _ hk⟩ : Fin A.length) = st.dPos := by
      apply Fin.ext
      exact hLastVal
    simpa [hIdx] using h

  have hRotEntry :
      rotL (k := A.length) r (childEntry A.length (2 ^ A.length - 1))
        =
      xor (oneHotFin dPosNext) (oneHotFin st.dPos) := by
    calc
      rotL (k := A.length) r (childEntry A.length (2 ^ A.length - 1))
          =
        rotL (k := A.length) r
          (xor (oneHotFin ⟨0, hk⟩) (oneHotFin ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩)) := by
            simp [hEntry]
      _ =
        xor (rotL (k := A.length) r (oneHotFin ⟨0, hk⟩))
            (rotL (k := A.length) r (oneHotFin ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩)) := by
            simpa using
              (BV.xor_rotL (k := A.length) r (oneHotFin ⟨0, hk⟩)
                    (oneHotFin ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩)).symm
      _ = xor (oneHotFin dPosNext) (oneHotFin st.dPos) := by
            simp [hRot0, hRotLast]

  have hExit :
      exitCorner (stateUpdate A st w)
        =
      xor (xor st.e (xor (oneHotFin dPosNext) (oneHotFin st.dPos))) (oneHotFin dPosNext) := by
    -- Unfold `stateUpdate`, rewrite the max-digit hypotheses, and use the computed rotated entry.
    simp [State.exitCorner, stateUpdate, State.mk', hw, hDir, hRotEntry, r, dPosNext]

  -- Cancel the duplicated `2^(d+1)` term in `e' ⊕ 2^{d'}` to recover `e ⊕ 2^d`.
  have hCancel :
      xor (xor st.e (xor (oneHotFin dPosNext) (oneHotFin st.dPos))) (oneHotFin dPosNext)
        =
      xor st.e (oneHotFin st.dPos) := by
    -- `((e ⊕ a ⊕ b) ⊕ a) = e ⊕ b` by commutativity/associativity and involution.
    let a : BV A.length := oneHotFin dPosNext
    let b : BV A.length := oneHotFin st.dPos
    simpa [a, b] using (calc
      xor (xor st.e (xor a b)) a
          = xor (xor (xor st.e a) b) a := by
              rw [(BV.xor_assoc st.e a b).symm]
      _ = xor (xor st.e a) (xor b a) := by
              simpa using BV.xor_assoc (x := xor st.e a) (y := b) (z := a)
      _ = xor (xor st.e a) (xor a b) := by
              rw [BV.xor_comm b a]
      _ = xor (xor (xor st.e a) a) b := by
              simpa using (BV.xor_assoc (x := xor st.e a) (y := a) (z := b)).symm
      _ = xor st.e b := by
              rw [BV.xor_invol_right (x := st.e) (e := a)]
      )

  calc
    exitCorner (stateUpdate A st w)
        =
      xor (xor st.e (xor (oneHotFin dPosNext) (oneHotFin st.dPos))) (oneHotFin dPosNext) := hExit
    _ = xor st.e (oneHotFin st.dPos) := hCancel
    _ = exitCorner st := rfl

  /-!
  The exit corner also shows up directly in decoding: the plane word written for a maximal digit
  is exactly `exitCorner`.
  -/

theorem Tinv_gc_toNat_zero_eq_entryCorner
    {n : Nat} {A : List (Axis n)} (st : State n A) (w : BV A.length)
    (hw : BV.toNat w = 0) :
    Tinv st.e st.dPos.val (BV.gc w) = entryCorner st := by
  have hwOf : BV.ofNat (k := A.length) 0 = w := by
    simpa [hw] using (BV.ofNat_toNat (x := w))
  have hOfNat0 : BV.ofNat (k := A.length) 0 = (BV.zero (k := A.length)) := by
    funext i
    simp [BV.ofNat, BV.zero]
  have hw0 : w = (BV.zero (k := A.length)) := by
    calc
      w = BV.ofNat (k := A.length) 0 := hwOf.symm
      _ = BV.zero := hOfNat0

  have hgc : BV.gc w = BV.zero := by
    simpa [hw0] using (BV.gc_zero (k := A.length))

  have hRot : BV.rotL (k := A.length) (st.dPos.val.succ) (BV.zero) = BV.zero :=
    BV.rotL_zero (k := A.length) (r := st.dPos.val.succ)

  calc
    Tinv st.e st.dPos.val (BV.gc w)
        = BV.xor (BV.rotL (st.dPos.val.succ) (BV.gc w)) st.e := by
            simp [Tinv]
    _ = BV.xor (BV.rotL (st.dPos.val.succ) BV.zero) st.e := by
          simp [hgc]
    _ = BV.xor (BV.zero (k := A.length)) st.e := by
          simp [hRot]
    _ = st.e := by
          simpa using (BV.xor_zero_left (k := A.length) st.e)
    _ = entryCorner st := rfl

theorem Tinv_gc_toNat_two_pow_sub_one_eq_exitCorner
    {n : Nat} {A : List (Axis n)} (st : State n A) (w : BV A.length)
    (hw : BV.toNat w = 2 ^ A.length - 1) :
    Tinv st.e st.dPos.val (BV.gc w) = exitCorner st := by
  classical
  have hk : 0 < A.length := State.length_pos st

  have hwOf : BV.ofNat (k := A.length) (2 ^ A.length - 1) = w := by
    -- Rewrite `toNat w` to the maximal value and use `ofNat_toNat`.
    simpa [hw] using (BV.ofNat_toNat (x := w))

  have hgc : BV.gc w = BV.oneHotFin ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩ := by
    -- `gc(2^k - 1)` is the last one-hot bit.
    simpa [hwOf] using
      BV.gc_ofNat_two_pow_sub_one_eq_oneHotFin_last (k := A.length) hk

  have hk1 : 1 ≤ A.length := Nat.succ_le_of_lt hk
  have hRot :
      BV.rotL (k := A.length) (st.dPos.val + 1)
          (BV.oneHotFin ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩)
        =
        BV.oneHotFin st.dPos := by
    have h :=
      BV.rotL_oneHotFin_eq_of_pos (k := A.length) hk (st.dPos.val + 1)
        ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩
    have hLastVal : ((A.length - 1) + (st.dPos.val + 1)) % A.length = st.dPos.val := by
      have hkm : (A.length + st.dPos.val) % A.length = st.dPos.val := by
        calc
          (A.length + st.dPos.val) % A.length
              = ((A.length % A.length) + (st.dPos.val % A.length)) % A.length := by
                  simpa using (Nat.add_mod A.length st.dPos.val A.length)
          _ = st.dPos.val % A.length := by simp
          _ = st.dPos.val := Nat.mod_eq_of_lt st.dPos.isLt
      calc
        ((A.length - 1) + (st.dPos.val + 1)) % A.length
            = (((A.length - 1) + 1) + st.dPos.val) % A.length := by
                ac_rfl
        _ = (A.length + st.dPos.val) % A.length := by
              simp [Nat.sub_add_cancel hk1]
        _ = st.dPos.val := hkm
    have hIdx :
        (⟨((A.length - 1) + (st.dPos.val + 1)) % A.length, Nat.mod_lt _ hk⟩ : Fin A.length) =
          st.dPos := by
      apply Fin.ext
      exact hLastVal
    simpa [hIdx] using h

  calc
    Tinv st.e st.dPos.val (BV.gc w)
        =
      BV.xor (BV.rotL (st.dPos.val.succ) (BV.gc w)) st.e := by
        simp [Tinv]
    _ =
        BV.xor (BV.rotL (st.dPos.val + 1) (BV.oneHotFin ⟨A.length - 1, BV.sub_one_lt_of_pos hk⟩))
          st.e := by
        simp [hgc, Nat.succ_eq_add_one]
    _ = BV.xor (BV.oneHotFin st.dPos) st.e := by
        simp [hRot, Nat.succ_eq_add_one]
    _ = BV.xor st.e (BV.oneHotFin st.dPos) := by
        simpa using (BV.xor_comm (x := BV.oneHotFin st.dPos) (y := st.e))
    _ = exitCorner st := rfl

end State

namespace Embed

open BV

theorem embedBV_xor {n : Nat} (Aold Anew : List (Axis n)) (x y : BV Aold.length) :
    embedBV Aold Anew (BV.xor x y) = BV.xor (embedBV Aold Anew x) (embedBV Aold Anew y) := by
  funext j
  cases h : pos? Aold (Anew.get j) with
  | none =>
      have hxy :
          embedBV Aold Anew (BV.xor x y) j = false :=
        embedBV_of_pos?_none (Aold := Aold) (Anew := Anew) (x := BV.xor x y) (j := j) h
      have hx : embedBV Aold Anew x j = false :=
        embedBV_of_pos?_none (Aold := Aold) (Anew := Anew) (x := x) (j := j) h
      have hy : embedBV Aold Anew y j = false :=
        embedBV_of_pos?_none (Aold := Aold) (Anew := Anew) (x := y) (j := j) h
      simp [BV.xor, BV.bxor, hxy, hx, hy]
  | some i =>
      have hxy :
          embedBV Aold Anew (BV.xor x y) j = (BV.xor x y) i :=
        embedBV_of_pos?_some (Aold := Aold) (Anew := Anew) (x := BV.xor x y) (j := j) (i := i) h
      have hx : embedBV Aold Anew x j = x i :=
        embedBV_of_pos?_some (Aold := Aold) (Anew := Anew) (x := x) (j := j) (i := i) h
      have hy : embedBV Aold Anew y j = y i :=
        embedBV_of_pos?_some (Aold := Aold) (Anew := Anew) (x := y) (j := j) (i := i) h
      simp [BV.xor, BV.bxor, hxy, hx, hy]

private theorem get_ne_of_pos?_some_of_nodup {n : Nat} {A : List (Axis n)}
    (hA : A.Nodup) {a : Axis n} {i : Fin A.length}
    (hpos : pos? A a = some i) (j : Fin A.length) (hj : j ≠ i) :
    A.get j ≠ a := by
  intro hEq
  have hposj : pos? A (A.get j) = some j := Pos.pos?_get_of_nodup (xs := A) hA j
  have hposArg : pos? A (A.get j) = pos? A a := congrArg (fun x => pos? A x) hEq
  have hpos' : pos? A a = some j := by
    calc
      pos? A a = pos? A (A.get j) := by simpa using hposArg.symm
      _ = some j := hposj
  have : (some i : Option (Fin A.length)) = some j := by
    simpa [hpos] using hpos'
  exact hj (Option.some.inj this).symm

/-- `entryCorner` commutes with activation embedding. -/
theorem embedState?_entryCorner_eq
    {n : Nat} (Aold Anew : List (Axis n))
    (st : State n Aold) {st' : State n Anew}
    (h : embedState? (Aold := Aold) (Anew := Anew) st = some st') :
    State.entryCorner st' = embedBV Aold Anew (State.entryCorner st) := by
  unfold embedState? at h
  cases hpos : pos? Anew st.dirAxis with
  | none =>
      simp [hpos] at h
  | some dPos' =>
      have hMk :
          State.mk' (A := Anew) (e := embedBV Aold Anew st.e) (dPos := dPos') = st' :=
        Option.some.inj (by simpa [hpos] using h)
      have hE : st'.e = embedBV Aold Anew st.e := by
        simpa [State.mk'] using (congrArg State.e hMk).symm
      simpa [State.entryCorner] using hE

/-- `exitCorner` commutes with activation embedding (on nodup axis lists). -/
theorem embedState?_exitCorner_eq
    {n : Nat} (Aold Anew : List (Axis n))
    (hOld : Aold.Nodup) (hNew : Anew.Nodup)
    (st : State n Aold) {st' : State n Anew}
    (h : embedState? (Aold := Aold) (Anew := Anew) st = some st') :
    State.exitCorner st' = embedBV Aold Anew (State.exitCorner st) := by
  classical
  unfold embedState? at h
  cases hpos : pos? Anew st.dirAxis with
  | none =>
      simp [hpos] at h
  | some dPos' =>
      have hMk :
          State.mk' (A := Anew) (e := embedBV Aold Anew st.e) (dPos := dPos') = st' :=
        Option.some.inj (by simpa [hpos] using h)

      have hE : st'.e = embedBV Aold Anew st.e := by
        simpa [State.mk'] using (congrArg State.e hMk).symm

      have hD : st'.dPos = dPos' := by
        simpa [State.mk'] using (congrArg State.dPos hMk).symm

      have hposOld : pos? Aold st.dirAxis = some st.dPos := by
        -- `pos?` finds the index of a `get` element in a nodup list.
        have hpos0 : pos? Aold (Aold.get st.dPos) = some st.dPos :=
          Pos.pos?_get_of_nodup (xs := Aold) hOld st.dPos
        have hposArg : pos? Aold (Aold.get st.dPos) = pos? Aold st.dirAxis :=
          congrArg (fun x => pos? Aold x) st.dir_ok
        exact (by
          calc
            pos? Aold st.dirAxis = pos? Aold (Aold.get st.dPos) := by simpa using hposArg.symm
            _ = some st.dPos := hpos0)

      have hDir : Anew.get dPos' = st.dirAxis :=
        Pos.get_of_pos?_some (xs := Anew) (a := st.dirAxis) (i := dPos') hpos

      have hone :
          embedBV Aold Anew (oneHotFin st.dPos) = oneHotFin dPos' := by
        funext j
        by_cases hj : j = dPos'
        ·
          have hposAt : pos? Aold (Anew.get dPos') = some st.dPos := by
            have hposArg : pos? Aold (Anew.get dPos') = pos? Aold st.dirAxis :=
              congrArg (fun x => pos? Aold x) hDir
            calc
              pos? Aold (Anew.get dPos') = pos? Aold st.dirAxis := by simpa using hposArg
              _ = some st.dPos := hposOld
          cases hj
          -- Embed the old one-hot along the (preserved) direction axis.
          rw [Embed.embedBV_of_pos?_some (Aold := Aold) (Anew := Anew) (x := oneHotFin st.dPos)
            (j := dPos') (i := st.dPos) hposAt]
          simp [oneHotFin]
        ·
          have hR : oneHotFin dPos' j = false := by
            simp [oneHotFin, hj]
          have hAxNe : Anew.get j ≠ st.dirAxis :=
            get_ne_of_pos?_some_of_nodup (A := Anew) hNew (a := st.dirAxis) (i := dPos') hpos j hj
          cases hposj : pos? Aold (Anew.get j) with
          | none =>
              rw [Embed.embedBV_of_pos?_none (Aold := Aold) (Anew := Anew) (x := oneHotFin st.dPos)
                (j := j) hposj, hR]
          | some i =>
              have hiNe : i ≠ st.dPos := by
                intro hiEq
                have hposSd : pos? Aold (Anew.get j) = some st.dPos := by
                  simpa [hiEq] using hposj
                have hget :
                    Aold.get st.dPos = Anew.get j :=
                  Pos.get_of_pos?_some (xs := Aold) (a := Anew.get j) (i := st.dPos) hposSd
                have : Anew.get j = st.dirAxis := by
                  calc
                    Anew.get j = Aold.get st.dPos := by simpa using hget.symm
                    _ = st.dirAxis := st.dir_ok
                exact hAxNe this
              rw [Embed.embedBV_of_pos?_some (Aold := Aold) (Anew := Anew) (x := oneHotFin st.dPos)
                (j := j) (i := i) hposj]
              rw [hR]
              simp [oneHotFin, hiNe]

      calc
        State.exitCorner st'
            =
          BV.xor (embedBV Aold Anew st.e) (oneHotFin dPos') := by
            simp [State.exitCorner, hE, hD]
        _ =
          BV.xor (embedBV Aold Anew st.e) (embedBV Aold Anew (oneHotFin st.dPos)) := by
            rw [← hone]
        _ =
          embedBV Aold Anew (BV.xor st.e (oneHotFin st.dPos)) := by
            simpa using (embedBV_xor (Aold := Aold) (Anew := Anew) (x := st.e) (y := oneHotFin st.dPos)).symm
        _ = embedBV Aold Anew (State.exitCorner st) := rfl

end Embed

namespace DecodeHead

open BV

theorem packPlane_decodeFromLevel_head_toNat_zero_eq_entryCorner
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (w : BV (activeAxes m (Nat.succ s)).length)
    (rest : Digits)
    (pAcc pOut : PointBV m)
    (hDec :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w⟩ :: rest) pAcc = some pOut)
    (hw : BV.toNat w = 0) :
    packPlane (activeAxes m (Nat.succ s)) pOut s = State.entryCorner st := by
  have hPlane :=
    DecodeHead.packPlane_decodeFromLevel_head (m := m)
      (s := s) (st := st) (w := w) (rest := rest) (pAcc := pAcc) (pOut := pOut) hDec
  simpa [State.Tinv_gc_toNat_zero_eq_entryCorner (st := st) (w := w) (hw := hw)] using hPlane

theorem packPlane_decodeFromLevel_head_toNat_two_pow_sub_one_eq_exitCorner
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (w : BV (activeAxes m (Nat.succ s)).length)
    (rest : Digits)
    (pAcc pOut : PointBV m)
    (hDec :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w⟩ :: rest) pAcc = some pOut)
    (hw : BV.toNat w = 2 ^ (activeAxes m (Nat.succ s)).length - 1) :
    packPlane (activeAxes m (Nat.succ s)) pOut s = State.exitCorner st := by
  have hPlane :=
    DecodeHead.packPlane_decodeFromLevel_head (m := m)
      (s := s) (st := st) (w := w) (rest := rest) (pAcc := pAcc) (pOut := pOut) hDec
  -- Rewrite the reconstructed word for the maximal digit.
  simpa [State.Tinv_gc_toNat_two_pow_sub_one_eq_exitCorner (st := st) (w := w) (hw := hw)] using hPlane

end DecodeHead

namespace Digits

/-- A digit suffix for `decodeFromLevel` where every remaining word is `0`. -/
def allZeroForDecode {n : Nat} (m : Exponents n) : Nat → Digits → Prop
  | 0, ds => ds = []
  | Nat.succ s, ds =>
      ∃ (w : BV (activeAxes m (Nat.succ s)).length) (rest : Digits),
        ds = ⟨(activeAxes m (Nat.succ s)).length, w⟩ :: rest ∧
          BV.toNat w = 0 ∧
          allZeroForDecode m s rest

/-- A digit suffix for `decodeFromLevel` where every remaining word is maximal (`2^k - 1`). -/
def allMaxForDecode {n : Nat} (m : Exponents n) : Nat → Digits → Prop
  | 0, ds => ds = []
  | Nat.succ s, ds =>
      ∃ (w : BV (activeAxes m (Nat.succ s)).length) (rest : Digits),
        ds = ⟨(activeAxes m (Nat.succ s)).length, w⟩ :: rest ∧
          BV.toNat w = 2 ^ (activeAxes m (Nat.succ s)).length - 1 ∧
          allMaxForDecode m s rest

theorem allZeroForDecode_of_decodeFromLevel_toNat_eq_zero
    {n : Nat} {m : Exponents n} :
    ∀ (s : Nat) (st : State n (activeAxes m s)) (ds : Digits)
      (pAcc pOut : PointBV m),
      decodeFromLevel (m := m) s st ds pAcc = some pOut →
      (∀ d ∈ ds, BV.toNat d.2 = 0) →
      allZeroForDecode m s ds := by
  intro s
  induction s with
  | zero =>
      intro st ds pAcc pOut hDec hZero
      cases ds with
      | nil =>
          simpa [allZeroForDecode] using rfl
      | cons d rest =>
          simp [decodeFromLevel] at hDec
  | succ s ih =>
      intro st ds pAcc pOut hDec hZero
      cases ds with
      | nil =>
          simp [decodeFromLevel] at hDec
      | cons d rest =>
          rcases d with ⟨kW, w⟩
          let A : List (Axis n) := activeAxes m (Nat.succ s)
          by_cases hk : kW = A.length
          · cases hk
            have hHead : BV.toNat w = 0 := hZero ⟨A.length, w⟩ (by simp)
            have hRest : ∀ d ∈ rest, BV.toNat d.2 = 0 := by
              intro d hd
              exact hZero d (by simp [hd])
            cases s with
            | zero =>
                -- Last level: decoding succeeds only if there are no remaining digits.
                cases rest with
                | nil =>
                    refine ⟨w, [], ?_, hHead, ?_⟩
                    · rfl
                    · simp [allZeroForDecode]
                | cons d2 rest2 =>
                    simp [decodeFromLevel, A] at hDec
            | succ s' =>
                -- Recursive case: extract the recursive decode equality and apply IH to `rest`.
                let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w)
                let p1 : PointBV m := writePlane A l pAcc (Nat.succ s')
                let stNext : State n A := stateUpdate (A := A) st w
                have hDec' :
                    decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st (⟨A.length, w⟩ :: rest) pAcc =
                      some pOut := by
                  simpa [A] using hDec
                simp [decodeFromLevel, A, l, p1, stNext] at hDec'
                split at hDec'
                · exact Option.noConfusion hDec'
                · rename_i stRec hEmb
                  have hRec :
                      decodeFromLevel (m := m) (Nat.succ s') stRec rest p1 = some pOut := hDec'
                  have hAllZeroRest :=
                    ih (st := stRec) (ds := rest) (pAcc := p1) (pOut := pOut) hRec hRest
                  refine ⟨w, rest, ?_, hHead, hAllZeroRest⟩
                  rfl
          · simp [decodeFromLevel, A, hk] at hDec

theorem allMaxForDecode_of_decodeFromLevel_toNat_eq_two_pow_sub_one
    {n : Nat} {m : Exponents n} :
    ∀ (s : Nat) (st : State n (activeAxes m s)) (ds : Digits)
      (pAcc pOut : PointBV m),
      decodeFromLevel (m := m) s st ds pAcc = some pOut →
      (∀ d ∈ ds, BV.toNat d.2 = 2 ^ d.1 - 1) →
      allMaxForDecode m s ds := by
  intro s
  induction s with
  | zero =>
      intro st ds pAcc pOut hDec hMax
      cases ds with
      | nil =>
          simpa [allMaxForDecode] using rfl
      | cons d rest =>
          simp [decodeFromLevel] at hDec
  | succ s ih =>
      intro st ds pAcc pOut hDec hMax
      cases ds with
      | nil =>
          simp [decodeFromLevel] at hDec
      | cons d rest =>
          rcases d with ⟨kW, w⟩
          let A : List (Axis n) := activeAxes m (Nat.succ s)
          by_cases hk : kW = A.length
          · cases hk
            have hHead : BV.toNat w = 2 ^ A.length - 1 := hMax ⟨A.length, w⟩ (by simp)
            have hRest : ∀ d ∈ rest, BV.toNat d.2 = 2 ^ d.1 - 1 := by
              intro d hd
              exact hMax d (by simp [hd])
            cases s with
            | zero =>
                cases rest with
                | nil =>
                    refine ⟨w, [], ?_, ?_, ?_⟩
                    · rfl
                    · simpa using hHead
                    · simp [allMaxForDecode]
                | cons d2 rest2 =>
                    simp [decodeFromLevel, A] at hDec
            | succ s' =>
                let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w)
                let p1 : PointBV m := writePlane A l pAcc (Nat.succ s')
                let stNext : State n A := stateUpdate (A := A) st w
                have hDec' :
                    decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st (⟨A.length, w⟩ :: rest) pAcc =
                      some pOut := by
                  simpa [A] using hDec
                simp [decodeFromLevel, A, l, p1, stNext] at hDec'
                split at hDec'
                · exact Option.noConfusion hDec'
                · rename_i stRec hEmb
                  have hRec :
                      decodeFromLevel (m := m) (Nat.succ s') stRec rest p1 = some pOut := hDec'
                  have hAllMaxRest :=
                    ih (st := stRec) (ds := rest) (pAcc := p1) (pOut := pOut) hRec hRest
                  refine ⟨w, rest, ?_, ?_, hAllMaxRest⟩
                  · rfl
                  · simpa using hHead
          · simp [decodeFromLevel, A, hk] at hDec

end Digits

namespace DecodeSuffix

open BV

private theorem unpackPlane_embedBV_eq_of_mem {n : Nat}
    (Aold Anew : List (Axis n)) (x : BV Aold.length) (j : Axis n)
    (hjOld : j ∈ Aold) (hjNew : j ∈ Anew) :
    unpackPlane Anew (Embed.embedBV Aold Anew x) j = unpackPlane Aold x j := by
  classical
  rcases Pos.pos?_some_of_mem (xs := Aold) (a := j) hjOld with ⟨iOld, hiOld⟩
  rcases Pos.pos?_some_of_mem (xs := Anew) (a := j) hjNew with ⟨iNew, hiNew⟩
  have hgetNew : Anew.get iNew = j := Pos.get_of_pos?_some (xs := Anew) (a := j) (i := iNew) hiNew
  have hLeft : unpackPlane Anew (Embed.embedBV Aold Anew x) j = x iOld := by
    -- `unpackPlane` selects the corresponding embedded bit at position `iNew`.
    simp [unpackPlane, hiNew]
    have hpos : pos? Aold (Anew.get iNew) = some iOld := by
      calc
        pos? Aold (Anew.get iNew) = pos? Aold j := by
          simpa using congrArg (fun a => pos? Aold a) hgetNew
        _ = some iOld := hiOld
    -- Evaluate the embedded bit using the `pos?` witness.
    simpa using (Embed.embedBV_of_pos?_some (Aold := Aold) (Anew := Anew) (x := x) (j := iNew) (i := iOld) hpos)
  have hRight : unpackPlane Aold x j = x iOld := by
    simp [unpackPlane, hiOld]
  exact hLeft.trans hRight.symm

theorem getBit_decodeFromLevel_allZero_eq_entryCorner
    {n : Nat} {m : Exponents n} :
    ∀ (s : Nat) (st : State n (activeAxes m s)) (ds : Digits)
      (pAcc pOut : PointBV m),
      Digits.allZeroForDecode m s ds →
      decodeFromLevel (m := m) s st ds pAcc = some pOut →
      ∀ (j : Axis n), j ∈ activeAxes m s →
        ∀ i, i < s → getBit (pOut j) i = unpackPlane (activeAxes m s) (State.entryCorner st) j := by
  intro s
  induction s with
  | zero =>
      intro st ds pAcc pOut hds hDec j hj i hi
      cases hi
  | succ s ih =>
      intro st ds pAcc pOut hds hDec j hj i hi
      -- Expose the head digit and its `toNat` constraint.
      rcases hds with ⟨w, rest, hds', hw, hrest⟩
      subst hds'
      -- Split on whether we're at the last level.
      cases s with
      | zero =>
          -- `s = 1`: only plane `0` is written.
          have hi0 : i = 0 := Nat.le_zero.mp (Nat.lt_succ_iff.mp hi)
          subst hi0
          have hPlane :
              packPlane (activeAxes m 1) pOut 0 = State.entryCorner st := by
            simpa using
              (DecodeHead.packPlane_decodeFromLevel_head_toNat_zero_eq_entryCorner (m := m)
                (s := 0) (st := st) (w := w) (rest := rest) (pAcc := pAcc) (pOut := pOut) hDec hw)
          -- Read the bit for axis `j` from the packed plane.
          have hjA : j ∈ activeAxes m 1 := hj
          rcases Pos.pos?_some_of_mem (xs := activeAxes m 1) (a := j) hjA with ⟨t, ht⟩
          have hget : (activeAxes m 1).get t = j :=
            Pos.get_of_pos?_some (xs := activeAxes m 1) (a := j) (i := t) ht
          have hbit : getBit (pOut j) 0 = (packPlane (activeAxes m 1) pOut 0) t := by
            simpa [packPlane] using congrArg (fun a => getBit (pOut a) 0) hget.symm
          -- Finish by rewriting with `hPlane` and `ht`.
          calc
            getBit (pOut j) 0 = (packPlane (activeAxes m 1) pOut 0) t := hbit
            _ = (State.entryCorner st) t := by simpa using congrArg (fun l => l t) hPlane
            _ = unpackPlane (activeAxes m 1) (State.entryCorner st) j := by
                  simp [unpackPlane, ht]
      | succ s' =>
          -- `s = succ (succ s')`: recurse to the next level down.
          have hi' : i = Nat.succ s' ∨ i < Nat.succ s' := by
            exact eq_or_lt_of_le (Nat.lt_succ_iff.mp hi)
          cases hi' with
          | inl hiTop =>
              subst hiTop
              have hPlane :
                  packPlane (activeAxes m (Nat.succ (Nat.succ s'))) pOut (Nat.succ s') =
                    State.entryCorner st := by
                simpa using
                  (DecodeHead.packPlane_decodeFromLevel_head_toNat_zero_eq_entryCorner (m := m)
                    (s := Nat.succ s') (st := st) (w := w) (rest := rest) (pAcc := pAcc)
                    (pOut := pOut) hDec hw)
              rcases Pos.pos?_some_of_mem (xs := activeAxes m (Nat.succ (Nat.succ s'))) (a := j) hj with
                ⟨t, ht⟩
              have hget :
                  (activeAxes m (Nat.succ (Nat.succ s'))).get t = j :=
                Pos.get_of_pos?_some (xs := activeAxes m (Nat.succ (Nat.succ s'))) (a := j) (i := t) ht
              have hbit :
                  getBit (pOut j) (Nat.succ s') =
                    (packPlane (activeAxes m (Nat.succ (Nat.succ s'))) pOut (Nat.succ s')) t := by
                simpa [packPlane] using congrArg (fun a => getBit (pOut a) (Nat.succ s')) hget.symm
              calc
                getBit (pOut j) (Nat.succ s')
                    =
                  (packPlane (activeAxes m (Nat.succ (Nat.succ s'))) pOut (Nat.succ s')) t := hbit
                _ = (State.entryCorner st) t := by
                      simpa using congrArg (fun l => l t) hPlane
                _ = unpackPlane (activeAxes m (Nat.succ (Nat.succ s'))) (State.entryCorner st) j := by
                      simp [unpackPlane, ht]
          | inr hiLo =>
              -- Extract the recursive call from `decodeFromLevel`.
              let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s'))
              have hk : (A.length : Nat) = A.length := rfl
              let w' : BV A.length := by
                simpa [A] using w
              let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w')
              let p1 : PointBV m := writePlane A l pAcc (Nat.succ s')
              let stNext : State n A := stateUpdate (A := A) st w'
              have hDec' : decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st
                  (⟨A.length, w'⟩ :: rest) pAcc = some pOut := by
                simpa [A, w', hk] using hDec
              -- Unfold one step and split on the embedding.
              simp [decodeFromLevel, A, w', l, p1, stNext] at hDec'
              split at hDec'
              · exact Option.noConfusion hDec'
              · rename_i stRec hEmb
                have hRec :
                    decodeFromLevel (m := m) (Nat.succ s') stRec rest p1 = some pOut := hDec'
                -- Apply the IH at the recursive level.
                have hjRec : j ∈ activeAxes m (Nat.succ s') :=
                  ActiveAxes.mem_activeAxes_of_mem_activeAxes_succ (m := m) (s := Nat.succ s') (j := j) hj
                have hIH :=
                  ih (st := stRec) (ds := rest) (pAcc := p1) (pOut := pOut) hrest hRec j hjRec i hiLo
                -- Relate the entry corners across the step.
                have hEntryNext :
                    State.entryCorner stNext = State.entryCorner st := by
                  simpa [A] using (State.entryCorner_stateUpdate_toNat_zero (st := st) (w := w') hw)
                have hEntryRec :
                    State.entryCorner stRec =
                      Embed.embedBV A (activeAxes m (Nat.succ s')) (State.entryCorner st) := by
                  -- `entryCorner` commutes with embedding, and is preserved by the zero digit.
                  have hEmbEntry :=
                    Embed.embedState?_entryCorner_eq (Aold := A) (Anew := activeAxes m (Nat.succ s')) (st := stNext)
                      (st' := stRec) hEmb
                  simpa [hEntryNext] using hEmbEntry
                have hCorner :
                    unpackPlane (activeAxes m (Nat.succ s')) (State.entryCorner stRec) j =
                      unpackPlane A (State.entryCorner st) j := by
                  have hjNew : j ∈ activeAxes m (Nat.succ s') := hjRec
                  -- Rewrite `entryCorner stRec` using `hEntryRec` and evaluate `unpackPlane`.
                  simpa [hEntryRec] using
                    (unpackPlane_embedBV_eq_of_mem (Aold := A) (Anew := activeAxes m (Nat.succ s')) (x := State.entryCorner st)
                      (j := j) hj hjNew)
                -- Finish.
                simpa [A] using hIH.trans hCorner

theorem getBit_decodeFromLevel_allMax_eq_exitCorner
    {n : Nat} {m : Exponents n} :
    ∀ (s : Nat) (st : State n (activeAxes m s)) (ds : Digits)
      (pAcc pOut : PointBV m),
      Digits.allMaxForDecode m s ds →
      decodeFromLevel (m := m) s st ds pAcc = some pOut →
      ∀ (j : Axis n), j ∈ activeAxes m s →
        ∀ i, i < s → getBit (pOut j) i = unpackPlane (activeAxes m s) (State.exitCorner st) j := by
  intro s
  induction s with
  | zero =>
      intro st ds pAcc pOut hds hDec j hj i hi
      cases hi
  | succ s ih =>
      intro st ds pAcc pOut hds hDec j hj i hi
      rcases hds with ⟨w, rest, hds', hw, hrest⟩
      subst hds'
      cases s with
      | zero =>
          have hi0 : i = 0 := Nat.le_zero.mp (Nat.lt_succ_iff.mp hi)
          subst hi0
          have hPlane :
              packPlane (activeAxes m 1) pOut 0 = State.exitCorner st := by
            simpa using
              (DecodeHead.packPlane_decodeFromLevel_head_toNat_two_pow_sub_one_eq_exitCorner (m := m)
                (s := 0) (st := st) (w := w) (rest := rest) (pAcc := pAcc) (pOut := pOut) hDec hw)
          have hjA : j ∈ activeAxes m 1 := hj
          rcases Pos.pos?_some_of_mem (xs := activeAxes m 1) (a := j) hjA with ⟨t, ht⟩
          have hget : (activeAxes m 1).get t = j :=
            Pos.get_of_pos?_some (xs := activeAxes m 1) (a := j) (i := t) ht
          have hbit : getBit (pOut j) 0 = (packPlane (activeAxes m 1) pOut 0) t := by
            simpa [packPlane] using congrArg (fun a => getBit (pOut a) 0) hget.symm
          calc
            getBit (pOut j) 0 = (packPlane (activeAxes m 1) pOut 0) t := hbit
            _ = (State.exitCorner st) t := by simpa using congrArg (fun l => l t) hPlane
            _ = unpackPlane (activeAxes m 1) (State.exitCorner st) j := by
                  simp [unpackPlane, ht]
      | succ s' =>
          have hi' : i = Nat.succ s' ∨ i < Nat.succ s' := by
            exact eq_or_lt_of_le (Nat.lt_succ_iff.mp hi)
          cases hi' with
          | inl hiTop =>
              subst hiTop
              have hPlane :
                  packPlane (activeAxes m (Nat.succ (Nat.succ s'))) pOut (Nat.succ s') =
                    State.exitCorner st := by
                simpa using
                  (DecodeHead.packPlane_decodeFromLevel_head_toNat_two_pow_sub_one_eq_exitCorner (m := m)
                    (s := Nat.succ s') (st := st) (w := w) (rest := rest) (pAcc := pAcc)
                    (pOut := pOut) hDec hw)
              rcases Pos.pos?_some_of_mem (xs := activeAxes m (Nat.succ (Nat.succ s'))) (a := j) hj with
                ⟨t, ht⟩
              have hget :
                  (activeAxes m (Nat.succ (Nat.succ s'))).get t = j :=
                Pos.get_of_pos?_some (xs := activeAxes m (Nat.succ (Nat.succ s'))) (a := j) (i := t) ht
              have hbit :
                  getBit (pOut j) (Nat.succ s') =
                    (packPlane (activeAxes m (Nat.succ (Nat.succ s'))) pOut (Nat.succ s')) t := by
                simpa [packPlane] using congrArg (fun a => getBit (pOut a) (Nat.succ s')) hget.symm
              calc
                getBit (pOut j) (Nat.succ s')
                    =
                  (packPlane (activeAxes m (Nat.succ (Nat.succ s'))) pOut (Nat.succ s')) t := hbit
                _ = (State.exitCorner st) t := by
                      simpa using congrArg (fun l => l t) hPlane
                _ = unpackPlane (activeAxes m (Nat.succ (Nat.succ s'))) (State.exitCorner st) j := by
                      simp [unpackPlane, ht]
          | inr hiLo =>
              let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s'))
              have hk : (A.length : Nat) = A.length := rfl
              let w' : BV A.length := by
                simpa [A] using w
              let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w')
              let p1 : PointBV m := writePlane A l pAcc (Nat.succ s')
              let stNext : State n A := stateUpdate (A := A) st w'
              have hDec' : decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st
                  (⟨A.length, w'⟩ :: rest) pAcc = some pOut := by
                simpa [A, w', hk] using hDec
              simp [decodeFromLevel, A, w', l, p1, stNext] at hDec'
              split at hDec'
              · exact Option.noConfusion hDec'
              · rename_i stRec hEmb
                have hRec :
                    decodeFromLevel (m := m) (Nat.succ s') stRec rest p1 = some pOut := hDec'
                have hjRec : j ∈ activeAxes m (Nat.succ s') :=
                  ActiveAxes.mem_activeAxes_of_mem_activeAxes_succ (m := m) (s := Nat.succ s') (j := j) hj
                have hIH :=
                  ih (st := stRec) (ds := rest) (pAcc := p1) (pOut := pOut) hrest hRec j hjRec i hiLo
                have hExitNext :
                    State.exitCorner (stateUpdate A st w') = State.exitCorner st := by
                  -- Convert the head-digit hypothesis to the needed `toNat` equality.
                  have hw' : BV.toNat w' = 2 ^ A.length - 1 := by simpa [A] using hw
                  simpa [A] using (State.exitCorner_stateUpdate_toNat_two_pow_sub_one (st := st) (w := w') hw')
                have hExitRec :
                    State.exitCorner stRec =
                      Embed.embedBV A (activeAxes m (Nat.succ s')) (State.exitCorner st) := by
                  have hOld : A.Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ (Nat.succ s'))
                  have hNew : (activeAxes m (Nat.succ s')).Nodup :=
                    ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ s')
                  have hEmbExit :=
                    Embed.embedState?_exitCorner_eq (Aold := A) (Anew := activeAxes m (Nat.succ s'))
                      (hOld := hOld) (hNew := hNew) (st := stateUpdate A st w') (st' := stRec) hEmb
                  simpa [hExitNext] using hEmbExit
                have hCorner :
                    unpackPlane (activeAxes m (Nat.succ s')) (State.exitCorner stRec) j =
                      unpackPlane A (State.exitCorner st) j := by
                  have hjNew : j ∈ activeAxes m (Nat.succ s') := hjRec
                  simpa [hExitRec] using
                    (unpackPlane_embedBV_eq_of_mem (Aold := A) (Anew := activeAxes m (Nat.succ s')) (x := State.exitCorner st)
                      (j := j) hj hjNew)
                simpa [A] using hIH.trans hCorner

end DecodeSuffix

end AnisoHilbert
