import Mathlib

import AnisoHilbert.AdjacencyLemmas
import AnisoHilbert.ActiveAxesLemmas
import AnisoHilbert.BVNatLemmas
import AnisoHilbert.ChildGlueLemmas
import AnisoHilbert.DigitsCarryMaxLemmas
import AnisoHilbert.DecodeHeadXorLemmas
import AnisoHilbert.DecodeHigherPlaneLemmas
import AnisoHilbert.GrayAdjacencyLemmas
import AnisoHilbert.RotLOneHotLemmas

namespace AnisoHilbert

/-!
Lean theorems mirroring the numbered roadmap in `discrete_proof.md`.

We keep statements “tight” (close to the markdown) and build reusable lemmas
needed for the lattice-continuity endpoint (Theorem 5.4).
-/

namespace DiscreteProof

open BV
open scoped BigOperators

def pointToNat {n : Nat} {m : Exponents n} (p : PointBV m) (j : Axis n) : Nat :=
  BV.toNat (p j)

def l1Dist {n : Nat} {m : Exponents n} (p q : PointBV m) : Nat :=
  ∑ j : Axis n, Nat.dist (pointToNat p j) (pointToNat q j)

private def digitsAllZero : Digits → Prop
  | [] => True
  | d :: ds => d.2 = (BV.zero (k := d.1)) ∧ digitsAllZero ds

private theorem rotL_zero {k : Nat} (r : Nat) : BV.rotL (k := k) r (BV.zero) = BV.zero := by
  cases k with
  | zero => rfl
  | succ k' =>
      funext i
      simp [BV.rotL, BV.zero]

private theorem xor_zero_right {k : Nat} (x : BV k) : BV.xor x BV.zero = x := by
  funext i
  cases hx : x i <;> simp [BV.xor, BV.bxor, hx, BV.zero]

private theorem xor_zero_left {k : Nat} (x : BV k) : BV.xor BV.zero x = x := by
  funext i
  cases hx : x i <;> simp [BV.xor, BV.bxor, hx, BV.zero]

private theorem gc_zero {k : Nat} : BV.gc (k := k) BV.zero = BV.zero := by
  funext i
  simp [BV.gc, BV.shr1, BV.zero, BV.xor, BV.bxor, getBit]

private theorem dist_succ_right (x : Nat) : Nat.dist x x.succ = 1 := by
  unfold Nat.dist
  lia

private theorem dyadic_half_boundary_dist_one (a s : Nat) (hs : 0 < s) :
    Nat.dist (a * 2 ^ s + (2 ^ (s - 1) - 1)) (a * 2 ^ s + 2 ^ (s - 1)) = 1 := by
  cases s with
  | zero =>
      cases (Nat.not_lt_zero 0 hs)
  | succ s' =>
      have hpowpos : 0 < 2 ^ s' := Nat.pow_pos (n := s') (Nat.succ_pos 1)
      have hle : 1 ≤ 2 ^ s' := Nat.succ_le_iff.2 hpowpos
      have hsub : 2 ^ s' - 1 + 1 = 2 ^ s' := Nat.sub_add_cancel hle
      -- rewrite the right endpoint as the successor of the left endpoint
      set L : Nat := a * 2 ^ Nat.succ s' + (2 ^ s' - 1) with hL
      have hR : a * 2 ^ Nat.succ s' + 2 ^ s' = L.succ := by
        calc
          a * 2 ^ Nat.succ s' + 2 ^ s' = a * 2 ^ Nat.succ s' + (2 ^ s' - 1 + 1) := by
            simp [hsub]
          _ = (a * 2 ^ Nat.succ s' + (2 ^ s' - 1)).succ := by
            simp [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          _ = L.succ := by
            simp [hL]
      -- the boundary jump is a unit step
      simpa [hR] using dist_succ_right L

/-- Lemma 5.1 (Oriented Gray order of children differs in one active bit). -/
theorem lemma_5_1
    {k : Nat} (e : BV k) (d : Nat) (i : Nat) (ht : tsb i < k) :
    ∃ g : Fin k,
      xor (Tinv e d (gc (ofNat (k := k) i)))
          (Tinv e d (gc (ofNat (k := k) i.succ)))
        = oneHotFin g := by
  -- Transport Gray adjacency through `Tinv` and simplify to a rotated one-hot.
  have hT :
      xor (Tinv e d (gc (ofNat (k := k) i)))
          (Tinv e d (gc (ofNat (k := k) i.succ)))
        =
      rotL d.succ (xor (gc (ofNat (k := k) i)) (gc (ofNat (k := k) i.succ))) := by
    simpa using
      (BV.xor_Tinv (e := e) (d := d)
        (x := gc (ofNat (k := k) i)) (y := gc (ofNat (k := k) i.succ)))

  have hGc :
      xor (gc (ofNat (k := k) i)) (gc (ofNat (k := k) i.succ)) = oneHotFin ⟨tsb i, ht⟩ := by
    simpa using (xor_gc_ofNat_succ_eq_oneHotFin (k := k) i ht)

  -- A rotation of a one-hot is still one-hot.
  have hRot : ∃ g : Fin k, rotL d.succ (oneHotFin ⟨tsb i, ht⟩) = oneHotFin g :=
    rotL_oneHotFin (k := k) (r := d.succ) ⟨tsb i, ht⟩

  rcases hRot with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  -- Combine the computed XOR with the rotation lemma.
  simpa [hT, hGc, hg]

/-!
### Seam helper lemmas (for Theorem 5.4)

The core continuity proof will compare two successful decodes whose head digit differs by a
variable-radix successor.  The next lemma specializes the `DecodeHeadXor` bridge lemma to that
successor form, using `BV.ofNat_toNat` to convert an arbitrary head word into `ofNat (toNat w)`.
-/

theorem pivot_plane_oneHot_of_decodeFromLevel_toNat_succ_heads
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (w : BV (activeAxes m (Nat.succ s)).length)
    (rest₁ rest₂ : Digits)
    (pAcc pOut₁ pOut₂ : PointBV m)
    (hDec₁ :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w⟩ :: rest₁) pAcc = some pOut₁)
    (hDec₂ :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length,
          BV.ofNat (k := (activeAxes m (Nat.succ s)).length) (BV.toNat w).succ⟩ :: rest₂) pAcc =
        some pOut₂)
    (ht : tsb (BV.toNat w) < (activeAxes m (Nat.succ s)).length) :
    ∃ g : Fin (activeAxes m (Nat.succ s)).length,
      BV.xor (packPlane (activeAxes m (Nat.succ s)) pOut₁ s)
          (packPlane (activeAxes m (Nat.succ s)) pOut₂ s)
        = BV.oneHotFin g := by
  classical
  let k : Nat := (activeAxes m (Nat.succ s)).length
  let i : Nat := BV.toNat w
  have hw : BV.ofNat (k := k) i = w := by
    simpa [k, i] using (BV.ofNat_toNat (x := w))

  have hDec₁' :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨k, BV.ofNat (k := k) i⟩ :: rest₁) pAcc = some pOut₁ := by
    simpa [k, i, hw] using hDec₁

  have hXor :
      BV.xor (packPlane (activeAxes m (Nat.succ s)) pOut₁ s)
          (packPlane (activeAxes m (Nat.succ s)) pOut₂ s)
        =
      BV.rotL (k := k) (st.dPos.val.succ) (BV.oneHotFin ⟨tsb i, by simpa [i, k] using ht⟩) := by
    -- `DecodeHeadXor` gives the rotated one-hot, but expects `ofNat i` and `ofNat (i+1)`.
    simpa [k, i] using
      (DecodeHeadXor.packPlane_xor_decodeFromLevel_ofNat_succ_heads (m := m)
        (s := s) (st := st) (i := i)
        (rest₁ := rest₁) (rest₂ := rest₂)
        (pAcc := pAcc) (pOut₁ := pOut₁) (pOut₂ := pOut₂)
        hDec₁' hDec₂ (ht := by simpa [i, k] using ht))

  -- A rotation of a one-hot is still one-hot.
  have hRot : ∃ g : Fin k, BV.rotL (k := k) (st.dPos.val.succ) (BV.oneHotFin ⟨tsb i, by simpa [i, k] using ht⟩) =
      BV.oneHotFin g :=
    BV.rotL_oneHotFin (k := k) (r := st.dPos.val.succ) ⟨tsb i, by simpa [i, k] using ht⟩

  rcases hRot with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  simpa [hXor, hg]

theorem pivot_plane_oneHot_of_decodeFromLevel_succDigit_heads
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (d : Digit)
    (rest₁ rest₂ : Digits)
    (pAcc pOut₁ pOut₂ : PointBV m)
    (hDec₁ :
      decodeFromLevel (m := m) (Nat.succ s) st (d :: rest₁) pAcc = some pOut₁)
    (hDec₂ :
      decodeFromLevel (m := m) (Nat.succ s) st ((Digits.succDigit d).1 :: rest₂) pAcc = some pOut₂)
    (hCarry : (Digits.succDigit d).2 = false) :
    ∃ g : Fin (activeAxes m (Nat.succ s)).length,
      BV.xor (packPlane (activeAxes m (Nat.succ s)) pOut₁ s)
          (packPlane (activeAxes m (Nat.succ s)) pOut₂ s)
        = BV.oneHotFin g := by
  classical
  -- Extract the width match from the successful decodes.
  rcases d with ⟨kW, w⟩
  let A : List (Axis n) := activeAxes m (Nat.succ s)
  have hkW : kW = A.length := by
    -- If the widths did not match, `decodeFromLevel` would return `none`.
    by_contra hne
    have hNone : decodeFromLevel (m := m) (Nat.succ s) st (⟨kW, w⟩ :: rest₁) pAcc = none := by
      simp [decodeFromLevel, A, hne]
    have : none = some pOut₁ := by
      simpa [hNone] using hDec₁
    exact Option.noConfusion this

  -- Normalize everything after rewriting `kW = A.length`.
  cases hkW
  have hCarryW : (Digits.succDigit ⟨A.length, w⟩).2 = false := by
    simpa using hCarry
  have hSuccW :
      (Digits.succDigit ⟨A.length, w⟩).1 = ⟨A.length, BV.ofNat (k := A.length) (BV.toNat w).succ⟩ := by
    simpa using (Digits.succDigit_eq_ofNat_succ_of_carry_false (d := ⟨A.length, w⟩) hCarryW)
  have hDec₂' :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨A.length, BV.ofNat (k := A.length) (BV.toNat w).succ⟩ :: rest₂) pAcc = some pOut₂ := by
    simpa [hSuccW, A] using hDec₂
  have ht : tsb (BV.toNat w) < A.length := by
    simpa [A] using (Digits.succDigit_carry_false_imp_tsb_lt (d := ⟨A.length, w⟩) hCarryW)

  -- Apply the `toNat.succ` head lemma.
  have h := pivot_plane_oneHot_of_decodeFromLevel_toNat_succ_heads (m := m)
    (s := s) (st := st) (w := w)
    (rest₁ := rest₁) (rest₂ := rest₂)
    (pAcc := pAcc) (pOut₁ := pOut₁) (pOut₂ := pOut₂)
    (hDec₁ := by simpa [A] using hDec₁) (hDec₂ := hDec₂') ht
  simpa [A] using h

/--
Pivot decomposition for `Digits.succ`, matching the “most significant changing digit” discussion
in the proof of Theorem 5.4 in `discrete_proof.md`.
-/
theorem succ_decomp_pivot
    (ds ds' : Digits) (h : Digits.succ ds = some ds') :
    ∃ hi pivot lo,
      ds = hi ++ pivot :: lo ∧
      ds' = hi ++ (Digits.succDigit pivot).1 :: (lo.map Digits.zeroLike) ∧
      (∀ d ∈ lo, BV.toNat d.2 = 2 ^ d.1 - 1) ∧
      (Digits.succDigit pivot).2 = false := by
  simpa using (Digits.succ_same_prefix_zero_suffix_two_pow_sub_one_suffix (ds := ds) (ds' := ds') h)

/-- Convenience: if `succDigit` does not carry, then its pivot `tsb` index is in range. -/
theorem tsb_toNat_lt_of_succDigit_snd_false (d : Digit) (h : (Digits.succDigit d).2 = false) :
    tsb (BV.toNat d.2) < d.1 := by
  exact Digits.succDigit_carry_false_imp_tsb_lt d h

/-- Convenience: if `succDigit` does not carry, the new digit is `ofNat (toNat w).succ`. -/
theorem succDigit_eq_ofNat_toNat_succ_of_snd_false (d : Digit) (h : (Digits.succDigit d).2 = false) :
    (Digits.succDigit d).1 = ⟨d.1, BV.ofNat (k := d.1) (BV.toNat d.2).succ⟩ := by
  exact Digits.succDigit_eq_ofNat_succ_of_carry_false d h

/-- Lemma 5.2 (Hilbert child endpoints glue along that bit). -/
theorem lemma_5_2
    {n : Nat} {A : List (Axis n)} (st : State n A) (w : BV A.length)
    (ht : tsb (toNat w) < A.length) :
    (stateUpdate A st (ofNat (k := A.length) (toNat w).succ)).e
      =
    xor (xor (stateUpdate A st w).e (oneHotFin (stateUpdate A st w).dPos))
        (rotL (k := A.length) (st.dPos.val.succ) (oneHotFin ⟨tsb (toNat w), ht⟩)) := by
  simpa using
    (BV.entryCorner_stateUpdate_succ_eq_exitCorner_stateUpdate_xor_rotL_oneHotFin_tsb (st := st) (w := w) ht)

/-- Lemma 5.3 (Cube-corner adjacency implies unit lattice step after scaling). -/
theorem lemma_5_3
    {n : Nat} {m : Exponents n} (g : Axis n) (s a : Nat) (hs : 0 < s)
    (pLow pHigh : PointBV m)
    (hgLow : pointToNat pLow g = a * 2 ^ s + (2 ^ (s - 1) - 1))
    (hgHigh : pointToNat pHigh g = a * 2 ^ s + 2 ^ (s - 1))
    (hEq : ∀ j : Axis n, j ≠ g → pointToNat pLow j = pointToNat pHigh j) :
    l1Dist pLow pHigh = 1 := by
  classical
  unfold l1Dist
  rw [Fintype.sum_eq_single g]
  · have : Nat.dist (pointToNat pLow g) (pointToNat pHigh g) = 1 := by
      rw [hgLow, hgHigh]
      exact dyadic_half_boundary_dist_one a s hs
    simpa [pointToNat] using this
  · intro j hj
    have : pointToNat pLow j = pointToNat pHigh j := hEq j hj
    exact Nat.dist_eq_zero this

end DiscreteProof

end AnisoHilbert
