import Mathlib

import AnisoHilbert.AdjacencyLemmas
import AnisoHilbert.ActiveAxesLemmas
import AnisoHilbert.BVNatLemmas
import AnisoHilbert.DecodeHeadXorLemmas
import AnisoHilbert.DecodeHigherPlaneLemmas
import AnisoHilbert.GrayAdjacencyLemmas

namespace AnisoHilbert

/-!
Lean theorems mirroring the numbered roadmap in `discrete_proof.md`.

We keep statements “tight” (close to the markdown) and build reusable lemmas
needed for the lattice-continuity endpoint (Theorem 5.4).
-/

namespace BV

/-- Rotating a one-hot word is still one-hot (explicitly: the hot index shifts by `r`). -/
theorem rotL_oneHotFin {k : Nat} (r : Nat) (g : Fin k) :
    ∃ g' : Fin k, rotL r (oneHotFin g) = oneHotFin g' := by
  cases k with
  | zero =>
      exact (Fin.elim0 g)
  | succ k' =>
      let n : Nat := Nat.succ k'
      have hn : 0 < n := Nat.succ_pos k'
      let s : Nat := n - (r % n)
      let g' : Fin n := ⟨(g.val + r) % n, Nat.mod_lt _ hn⟩
      refine ⟨g', ?_⟩
      funext i
      -- `s = n - (r % n)` so `s + r ≡ 0 (mod n)`.
      have hstep : (s + r) % n = 0 := by
        have hr : (r / n) * n + (r % n) = r := Nat.div_add_mod' r n
        have hle : r % n ≤ n := Nat.le_of_lt (Nat.mod_lt r hn)
        calc
          (s + r) % n = ((n - (r % n)) + r) % n := by rfl
          _ = ((n - (r % n)) + ((r / n) * n + (r % n))) % n := by simpa [hr]
          _ = (((r / n) * n) + ((n - (r % n)) + (r % n))) % n := by
                ac_rfl
          _ = (((r / n) * n) + n) % n := by
                simp [Nat.sub_add_cancel hle]
          _ = (n + ((r / n) * n)) % n := by
                simp [Nat.add_comm]
          _ = (n + n * (r / n)) % n := by
                simp [Nat.mul_comm]
          _ = n % n := by
                simpa using (Nat.add_mul_mod_self_left n n (r / n))
          _ = 0 := by simp

      -- Pointwise: reduce to a `decide` equality on `Fin` and prove the underlying ↔.
      have hEq : ((⟨(i.val + s) % n, Nat.mod_lt _ hn⟩ : Fin n) = g) ↔ (i = g') := by
        -- First do the modular arithmetic on values.
        have hNat : ((i.val + s) % n = g.val) ↔ (i.val = (g.val + r) % n) := by
          constructor
          · intro h
            have hadd : ((i.val + s) + r) % n = (g.val + r) % n := by
              calc
                ((i.val + s) + r) % n
                    = (((i.val + s) % n) + (r % n)) % n := by
                        simpa [Nat.add_assoc] using (Nat.add_mod (i.val + s) r n)
                _ = (g.val + (r % n)) % n := by simpa [h]
                _ = (g.val + r) % n := by
                        -- Replace `r` by `r % n` under `% n`.
                        have hgmod : g.val % n = g.val := Nat.mod_eq_of_lt g.isLt
                        have hmod : (g.val + r) % n = (g.val + (r % n)) % n := by
                          calc
                            (g.val + r) % n = ((g.val % n) + (r % n)) % n := by
                                  simpa using (Nat.add_mod g.val r n)
                            _ = (g.val + (r % n)) % n := by simp [hgmod]
                        exact hmod.symm

            have hi : i.val < n := i.isLt
            have hL : ((i.val + s) + r) % n = i.val := by
              calc
                ((i.val + s) + r) % n = (i.val + (s + r)) % n := by
                      simp [Nat.add_assoc]
                _ = ((i.val % n) + ((s + r) % n)) % n := by
                      simpa using (Nat.add_mod i.val (s + r) n)
                _ = (i.val + 0) % n := by
                      simp [Nat.mod_eq_of_lt hi, hstep]
                _ = i.val := by
                      simp [Nat.mod_eq_of_lt hi]

            exact hL.symm.trans hadd
          · intro h
            have hg : g.val < n := g.isLt
            calc
              (i.val + s) % n
                  = (((g.val + r) % n) + s) % n := by simpa [h]
              _ = (g.val + r + s) % n := by
                    -- Remove the inner `% n` (both sides normalize to the same form via `Nat.add_mod`).
                    have h1 :
                        (((g.val + r) % n) + s) % n = (((g.val + r) % n) + (s % n)) % n := by
                      simpa [Nat.mod_mod] using (Nat.add_mod ((g.val + r) % n) s n)
                    have h2 :
                        (g.val + r + s) % n = (((g.val + r) % n) + (s % n)) % n := by
                      simpa [Nat.add_assoc] using (Nat.add_mod (g.val + r) s n)
                    exact h1.trans h2.symm
              _ = (g.val + (r + s)) % n := by simp [Nat.add_assoc]
              _ = g.val := by
                    have hstep' : (r + s) % n = 0 := by
                      simpa [Nat.add_comm] using hstep
                    calc
                      (g.val + (r + s)) % n
                          = ((g.val % n) + ((r + s) % n)) % n := by
                                simpa using (Nat.add_mod g.val (r + s) n)
                      _ = (g.val + 0) % n := by
                                simp [Nat.mod_eq_of_lt hg, hstep']
                      _ = g.val := by
                                simp [Nat.mod_eq_of_lt hg]

        have hleft :
            ((⟨(i.val + s) % n, Nat.mod_lt _ hn⟩ : Fin n) = g) ↔ ((i.val + s) % n = g.val) := by
          simpa [Fin.ext_iff]
        have hright : (i = g') ↔ (i.val = (g.val + r) % n) := by
          simpa [Fin.ext_iff, g']

        exact hleft.trans (hNat.trans hright.symm)

      by_cases h : ((⟨(i.val + s) % n, Nat.mod_lt _ hn⟩ : Fin n) = g)
      · have hi : i = g' := (hEq.mp h)
        have hR : oneHotFin g' i = true := by
          simp [oneHotFin, hi]
        have hL : rotL r (oneHotFin g) i = true := by
          simp [rotL, oneHotFin, n, s, h]
        rw [hR]
        exact hL
      · have hi : i ≠ g' := by
          intro hi'
          exact h (hEq.mpr hi')
        have hR : oneHotFin g' i = false := by
          simp [oneHotFin, hi]
        have hL : rotL r (oneHotFin g) i = false := by
          simp [rotL, oneHotFin, n, s, h]
        rw [hR]
        exact hL

end BV

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

/-- Lemma 5.2 (Hilbert child endpoints glue along that bit). -/
theorem lemma_5_2
    {k : Nat} (e eNext : BV k) (d g : Fin k)
    (hH1 : eNext = xor (xor e (oneHotFin d)) (oneHotFin g)) :
    let f : BV k := xor e (oneHotFin d)
    eNext = xor f (oneHotFin g) := by
  intro f
  simpa [f] using hH1

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
