import Mathlib

import AnisoHilbert.AdjacencyLemmas
import AnisoHilbert.ActiveAxesLemmas
import AnisoHilbert.BVNatLemmas
import AnisoHilbert.ChildGlueLemmas
import AnisoHilbert.DigitsCarryMaxLemmas
import AnisoHilbert.DecodeHeadXorLemmas
import AnisoHilbert.ExitCornerLemmas
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

/-!
### Theorem 5.4 (Lattice continuity)

We prove continuity by isolating the seam step between consecutive children at the pivot level
identified by `Digits.succ`.
-/

private theorem unpackPlane_oneHotFin_eq_true_of_get
    {n : Nat} (A : List (Axis n)) (hA : A.Nodup) (g : Fin A.length) :
    unpackPlane A (BV.oneHotFin g) (A.get g) = true := by
  classical
  have hpos0 : pos? A (A.get g) = some g := Pos.pos?_get_of_nodup (xs := A) hA g
  have hpos : pos? A A[g.1] = some g := by
    simpa using hpos0
  simp [unpackPlane, hpos, BV.oneHotFin]

private theorem unpackPlane_oneHotFin_eq_false_of_mem_ne_get
    {n : Nat} (A : List (Axis n)) (hA : A.Nodup) (g : Fin A.length) (j : Axis n)
    (hj : j ∈ A) (hne : j ≠ A.get g) :
    unpackPlane A (BV.oneHotFin g) j = false := by
  classical
  rcases Pos.pos?_some_of_mem (xs := A) (a := j) hj with ⟨t, ht⟩
  have hget : A.get t = j := Pos.get_of_pos?_some (xs := A) (a := j) (i := t) ht
  have htne : t ≠ g := by
    intro hEq
    apply hne
    -- `hget : A.get t = j` and `t = g` imply `j = A.get g`.
    simpa [hEq] using hget.symm
  simp [unpackPlane, ht, BV.oneHotFin, htne]

private theorem unpackPlane_oneHotFin_eq_false_of_not_mem
    {n : Nat} (A : List (Axis n)) (g : Fin A.length) (j : Axis n) (hj : j ∉ A) :
    unpackPlane A (BV.oneHotFin g) j = false := by
  classical
  cases hpos : pos? A j with
  | none =>
      simp [unpackPlane, hpos]
  | some t =>
      exfalso
      have : j ∈ A := Pos.mem_of_pos?_some (xs := A) (a := j) (i := t) hpos
      exact hj this

private theorem unpackPlane_embedBV_eq_of_mem
    {n : Nat} (Aold Anew : List (Axis n)) (x : BV Aold.length) (j : Axis n)
    (hjOld : j ∈ Aold) (hjNew : j ∈ Anew) :
    unpackPlane Anew (Embed.embedBV Aold Anew x) j = unpackPlane Aold x j := by
  classical
  rcases Pos.pos?_some_of_mem (xs := Aold) (a := j) hjOld with ⟨iOld, hiOld⟩
  rcases Pos.pos?_some_of_mem (xs := Anew) (a := j) hjNew with ⟨iNew, hiNew⟩
  have hgetNew : Anew.get iNew = j := Pos.get_of_pos?_some (xs := Anew) (a := j) (i := iNew) hiNew
  have hpos : pos? Aold (Anew.get iNew) = some iOld := by
    calc
      pos? Aold (Anew.get iNew) = pos? Aold j := by
        simpa using congrArg (fun a => pos? Aold a) hgetNew
      _ = some iOld := hiOld
  have hpos' : pos? Aold Anew[iNew.1] = some iOld := by
    simpa using hpos
  have hLeft : unpackPlane Anew (Embed.embedBV Aold Anew x) j = x iOld := by
    -- Reduce `unpackPlane` at `j` to the embedded bit at position `iNew`.
    simp [unpackPlane, hiNew, Embed.embedBV, hpos']
  have hRight : unpackPlane Aold x j = x iOld := by
    simp [unpackPlane, hiOld]
  exact hLeft.trans hRight.symm

private theorem unpackPlane_embedBV_eq_false_of_not_mem_old
    {n : Nat} (Aold Anew : List (Axis n)) (x : BV Aold.length) (j : Axis n)
    (hjOld : j ∉ Aold) (hjNew : j ∈ Anew) :
    unpackPlane Anew (Embed.embedBV Aold Anew x) j = false := by
  classical
  rcases Pos.pos?_some_of_mem (xs := Anew) (a := j) hjNew with ⟨iNew, hiNew⟩
  have hgetNew : Anew.get iNew = j :=
    Pos.get_of_pos?_some (xs := Anew) (a := j) (i := iNew) hiNew
  have hgetNew' : Anew[iNew.1] = j := by
    simpa using hgetNew
  have hposOld : pos? Aold Anew[iNew.1] = none := by
    have : pos? Aold j = none := by
      cases hpos : pos? Aold j with
      | none => rfl
      | some t =>
          exfalso
          have : j ∈ Aold := Pos.mem_of_pos?_some (xs := Aold) (a := j) (i := t) hpos
          exact hjOld this
    simpa [hgetNew'] using this
  -- `unpackPlane` selects the embedded bit at `iNew`, which is `false` since `j ∉ Aold`.
  simp [unpackPlane, hiNew, Embed.embedBV, hposOld]

private theorem unpackPlane_xor
    {n : Nat} (A : List (Axis n)) (x y : BV A.length) (j : Axis n) :
    unpackPlane A (BV.xor x y) j = BV.bxor (unpackPlane A x j) (unpackPlane A y j) := by
  classical
  by_cases hj : j ∈ A
  · rcases Pos.pos?_some_of_mem (xs := A) (a := j) hj with ⟨t, ht⟩
    simp [unpackPlane, ht, BV.xor, BV.bxor]
  · -- if `j` is inactive, `unpackPlane` returns `false` on both sides.
    have hx : unpackPlane A x j = false := by
      cases hpos : pos? A j with
      | none => simp [unpackPlane, hpos]
      | some t =>
          exfalso
          have : j ∈ A := Pos.mem_of_pos?_some (xs := A) (a := j) (i := t) hpos
          exact hj this
    have hy : unpackPlane A y j = false := by
      cases hpos : pos? A j with
      | none => simp [unpackPlane, hpos]
      | some t =>
          exfalso
          have : j ∈ A := Pos.mem_of_pos?_some (xs := A) (a := j) (i := t) hpos
          exact hj this
    have hxy : unpackPlane A (BV.xor x y) j = false := by
      cases hpos : pos? A j with
      | none => simp [unpackPlane, hpos]
      | some t =>
          exfalso
          have : j ∈ A := Pos.mem_of_pos?_some (xs := A) (a := j) (i := t) hpos
          exact hj this
    simp [hxy, hx, hy, BV.bxor]

/-!
### Bit facts for the seam step

For the pivot/seam proof we need a small combinatorial fact:

* along the Gray-change axis `tsb i`, the child-entry corner of `(i+1)` agrees (in that bit)
  with the Gray code word of `i`.

This is the missing “carry boundary” ingredient that lets us identify the unit step as the
dyadic half-boundary jump.
-/

private theorem rotL_apply_at_add_mod
    {k : Nat} (hk : 0 < k) (r : Nat) (t : Fin k) (x : BV k) :
    let g : Fin k := ⟨(t.val + r) % k, Nat.mod_lt _ hk⟩
    BV.rotL (k := k) r x g = x t := by
  intro g
  cases k with
  | zero =>
      cases (Nat.not_lt_zero 0 hk)
  | succ k' =>
      -- Unfold the rotation and compute the resulting index.
      let n : Nat := Nat.succ k'
      have hn : 0 < n := Nat.succ_pos k'
      let s : Nat := n - (r % n)
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
      have hstep' : (r + s) % n = 0 := by simpa [Nat.add_comm] using hstep

      -- Evaluate `rotL` at the chosen index `g`.
      have hgVal : g.val = (t.val + r) % n := by rfl
      have htVal : t.val < n := t.isLt
      have hIdx : (g.val + s) % n = t.val := by
        calc
          (g.val + s) % n = (((t.val + r) % n) + s) % n := by simpa [hgVal]
          _ = (t.val + r + s) % n := by
                -- normalize through `Nat.add_mod`
                have h1 : (((t.val + r) % n) + s) % n = (((t.val + r) % n) + (s % n)) % n := by
                  simpa [Nat.mod_mod] using (Nat.add_mod ((t.val + r) % n) s n)
                have h2 : (t.val + r + s) % n = (((t.val + r) % n) + (s % n)) % n := by
                  simpa [Nat.add_assoc] using (Nat.add_mod (t.val + r) s n)
                exact h1.trans h2.symm
          _ = (t.val + (r + s)) % n := by simp [Nat.add_assoc]
          _ = ((t.val % n) + ((r + s) % n)) % n := by
                simpa using (Nat.add_mod t.val (r + s) n)
          _ = (t.val + 0) % n := by simp [Nat.mod_eq_of_lt htVal, hstep']
          _ = t.val := by simp [Nat.mod_eq_of_lt htVal]

      -- Finish by rewriting the computed `Fin` index.
      simp [BV.rotL, n, s, hIdx]

private theorem childEntry_succ_get_tsb_eq_gc_get_tsb
    {k : Nat} (hk : 0 < k) (i : Nat) (ht : tsb i < k) :
    (childEntry k i.succ) ⟨tsb i, ht⟩ = (BV.gc (BV.ofNat (k := k) i)) ⟨tsb i, ht⟩ := by
  classical
  -- Split on parity of `i`.
  rcases Nat.mod_two_eq_zero_or_one i with hEven | hOdd
  · -- even: `i+1` is odd, so `childEntry (i+1) = gc i`.
    have hdvd : 2 ∣ i := Nat.dvd_of_mod_eq_zero hEven
    have hj : 2 * (i / 2) = i := Nat.mul_div_cancel' hdvd
    have hCE : childEntry k i.succ = BV.gc (BV.ofNat (k := k) i) := by
      -- `i.succ ≠ 0` and `2 * ((i.succ - 1) / 2) = i`.
      simp [childEntry, Nat.succ_ne_zero, Nat.succ_sub_one, hj]
    simpa [hCE]
  · -- odd: `i+1` is even, so `childEntry (i+1) = gc (i-1)`, and Gray codes agree at `tsb i > 0`.
    have hiNe0 : i ≠ 0 := by
      intro h0
      subst h0
      simp at hOdd
    have hiPos : 0 < i := Nat.pos_of_ne_zero hiNe0
    have htsbPos : 0 < tsb i := by
      -- `tsb i = succ _` when `i` is odd.
      have htsb : tsb i = Nat.succ (tsb (i / 2)) := by
        -- use the recursion equation lemma to avoid unfolding `tsb` under itself
        rw [tsb.eq_1]
        rw [if_pos hOdd]
      -- avoid `simp` loops by rewriting once
      rw [htsb]
      exact Nat.succ_pos (tsb (i / 2))

    -- Compute the even predecessor appearing in `childEntry`.
    have hrepr : i / 2 * 2 + 1 = i := by
      -- `i / 2 * 2 + i % 2 = i` and `i % 2 = 1`.
      simpa [hOdd] using (Nat.div_add_mod' i 2)
    have hpred : 2 * (i / 2) = i - 1 := by
      -- Rearrange `hrepr` and subtract `1` from both sides.
      have h' : i = 2 * (i / 2) + 1 := by
        simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hrepr.symm
      have := congrArg (fun t => t - 1) h'
      -- `(a+1)-1 = a`, after commuting.
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm

    have hCE : childEntry k i.succ = BV.gc (BV.ofNat (k := k) (i - 1)) := by
      simp [childEntry, Nat.succ_ne_zero, Nat.succ_sub_one, hpred]

    -- Gray adjacency between `i-1` and `i` flips only bit `0`.
    have hPredEven : (i - 1) % 2 = 0 := by
      -- If `(i-1)` were odd, then adding `1` would make `i` even, contradicting `hOdd`.
      rcases Nat.mod_two_eq_zero_or_one (i - 1) with h0 | h1
      · exact h0
      · have hEq : (i - 1) + 1 = i := Nat.sub_add_cancel hiPos
        have hMod : i % 2 = 0 := by
          -- compute `(i-1 + 1) % 2`
          have := congrArg (fun t => t % 2) hEq
          -- simplify the LHS using `h1`.
          -- `((i-1) % 2 + 1 % 2) % 2 = (1 + 1) % 2 = 0`
          simpa [Nat.add_mod, h1] using this.symm
        -- contradiction with `i % 2 = 1`
        have : (0 : Nat) = 1 := by simpa [hMod] using hOdd.symm
        cases this

    have htPred : tsb (i - 1) < k := by
      -- `tsb (i-1) = 0` since `(i-1)` is even.
      have htsbPred : tsb (i - 1) = 0 := by simp [tsb, hPredEven]
      simpa [htsbPred] using hk

    have hXorPred :
        BV.xor (BV.gc (BV.ofNat (k := k) (i - 1))) (BV.gc (BV.ofNat (k := k) i)) =
          BV.oneHotFin ⟨tsb (i - 1), htPred⟩ := by
      -- `(i-1).succ = i` because `i > 0`.
      have hEq : (i - 1) + 1 = i := Nat.sub_add_cancel hiPos
      simpa [Nat.succ_eq_add_one, hEq] using
        (BV.xor_gc_ofNat_succ_eq_oneHotFin (k := k) (i := i - 1) htPred)

    have hbit :
        BV.bxor (BV.gc (BV.ofNat (k := k) (i - 1)) (⟨tsb i, ht⟩ : Fin k))
          (BV.gc (BV.ofNat (k := k) i) (⟨tsb i, ht⟩ : Fin k)) = false := by
      have := congrArg (fun w => w (⟨tsb i, ht⟩ : Fin k)) hXorPred
      -- `oneHot` at index `0` is `false` at `tsb i > 0`.
      have htsbPred : tsb (i - 1) = 0 := by simp [tsb, hPredEven]
      have hdec : decide (tsb i = 0) = false :=
        (decide_eq_false_iff_not).2 (Nat.ne_of_gt htsbPos)
      simpa [BV.xor, BV.oneHotFin, htsbPred, hdec] using this

    -- `bxor a b = false` implies `a = b`.
    have hEqBit :
        BV.gc (BV.ofNat (k := k) (i - 1)) (⟨tsb i, ht⟩ : Fin k)
          =
        BV.gc (BV.ofNat (k := k) i) (⟨tsb i, ht⟩ : Fin k) := by
      cases ha : (BV.gc (BV.ofNat (k := k) (i - 1)) (⟨tsb i, ht⟩ : Fin k)) <;>
        cases hb : (BV.gc (BV.ofNat (k := k) i) (⟨tsb i, ht⟩ : Fin k)) <;>
        simp [BV.bxor, ha, hb] at hbit <;>
        simp [ha, hb]

    -- Finish by rewriting `childEntry (i+1)` as `gc (i-1)`.
    simpa [hCE] using hEqBit

private theorem ofNat_inj_of_lt {k a b : Nat}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k) (h : BV.ofNat (k := k) a = BV.ofNat (k := k) b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hik : i < k
  · -- In-range bits are equal by the `BV` equality.
    have hbit := congrArg (fun (v : BV k) => v ⟨i, hik⟩) h
    simpa [BV.ofNat] using hbit
  · -- Out-of-range bits are `false` because both numbers are `< 2^k ≤ 2^i`.
    have hki : k ≤ i := Nat.le_of_not_gt hik
    have hpow : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hki
    have ha' : a < 2 ^ i := lt_of_lt_of_le ha hpow
    have hb' : b < 2 ^ i := lt_of_lt_of_le hb hpow
    simp [Nat.testBit_eq_false_of_lt ha', Nat.testBit_eq_false_of_lt hb']

private theorem toNat_ofNat_eq_of_lt {k n : Nat} (hn : n < 2 ^ k) :
    BV.toNat (BV.ofNat (k := k) n) = n := by
  -- Let `m` be the reconstructed number from the low `k` bits of `n`.
  set m : Nat := BV.toNat (BV.ofNat (k := k) n)
  have hm : m < 2 ^ k := by
    -- Any `k`-bit word represents a number `< 2^k`.
    simpa [m, Nat.shiftLeft_eq] using (BV.toNat_lt_shiftLeft_one (x := BV.ofNat (k := k) n))
  have hof : BV.ofNat (k := k) m = BV.ofNat (k := k) n := by
    -- `BV.ofNat_toNat` is a left inverse.
    simpa [m] using (BV.ofNat_toNat (x := BV.ofNat (k := k) n))
  have : m = n := ofNat_inj_of_lt (k := k) (a := m) (b := n) hm hn hof
  simpa [m, this]

private theorem testBit_pointToNat_eq_getBit
    {n : Nat} {m : Exponents n} (p : PointBV m) (j : Axis n) (i : Nat) (hi : i < m j) :
    Nat.testBit (pointToNat p j) i = getBit (p j) i := by
  -- Convert `testBit` on the reconstructed Nat back to the original bitvector using `ofNat_toNat`.
  have hOfNat : BV.ofNat (k := m j) (BV.toNat (p j)) = p j := BV.ofNat_toNat (x := p j)
  -- Evaluate the equality at index `⟨i,hi⟩`.
  have : (BV.ofNat (k := m j) (BV.toNat (p j))) ⟨i, hi⟩ = (p j) ⟨i, hi⟩ := by
    simpa [hOfNat]
  -- Unfold definitions of `pointToNat`, `ofNat`, and `getBit`.
  simpa [pointToNat, BV.ofNat, getBit, hi] using this

/-!
### Suffix-corner facts (for Theorem 5.4)

When we decode a head digit at level `s+1`, the recursive decode (levels `< s`) determines all
lower bit-planes. For the special suffixes “all max” and “all zero”, we can read those lower bits
directly from the child state's exit/entry corner label.
-/

private theorem getBit_decodeFromLevel_head_allMax_suffix_eq_exitCorner
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (w : BV (activeAxes m (Nat.succ s)).length)
    (lo : Digits)
    (pAcc pOut : PointBV m)
    (hDec :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w⟩ :: lo) pAcc = some pOut)
    (hLoMax : ∀ d ∈ lo, BV.toNat d.2 = 2 ^ d.1 - 1) :
    ∀ (j : Axis n), j ∈ activeAxes m (Nat.succ s) →
      ∀ i0, i0 < s →
        getBit (pOut j) i0 =
          unpackPlane (activeAxes m (Nat.succ s))
            (State.exitCorner (stateUpdate (activeAxes m (Nat.succ s)) st w)) j := by
  classical
  intro j hj i0 hi0
  cases s with
  | zero =>
      cases (Nat.not_lt_zero _ hi0)
  | succ s' =>
      -- Unfold one head step of the decoder to expose the recursive call on `lo`.
      let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s'))
      let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w)
      let p1 : PointBV m := writePlane A l pAcc (Nat.succ s')
      let stNext : State n A := stateUpdate (A := A) st w

      have ⟨stRec, hEmb⟩ := Embed.embedState?_activeAxes_succ_some (m := m) (s := Nat.succ s') stNext

      have hDec' := hDec
      simp [decodeFromLevel, A, l, p1, stNext, hEmb] at hDec'
      -- `hDec'` is now the recursive decode equality.
      have hRec :
          decodeFromLevel (m := m) (Nat.succ s') stRec lo p1 = some pOut := hDec'

      -- Apply the all-max suffix corner lemma at the recursive level.
      have hjRec : j ∈ activeAxes m (Nat.succ s') :=
        ActiveAxes.mem_activeAxes_of_mem_activeAxes_succ (m := m) (s := Nat.succ s') (j := j) hj
      have hAllMax : Digits.allMaxForDecode m (Nat.succ s') lo :=
        Digits.allMaxForDecode_of_decodeFromLevel_toNat_eq_two_pow_sub_one (m := m)
          (s := Nat.succ s') (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut) hRec hLoMax
      have hBit :=
        DecodeSuffix.getBit_decodeFromLevel_allMax_eq_exitCorner (m := m)
          (s := Nat.succ s') (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut) hAllMax hRec j hjRec
          i0 hi0

      -- Transport `exitCorner` back across the embedding.
      have hOld : A.Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ (Nat.succ s'))
      have hNew : (activeAxes m (Nat.succ s')).Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ s')
      have hExitEmb :
          State.exitCorner stRec =
            Embed.embedBV A (activeAxes m (Nat.succ s')) (State.exitCorner stNext) := by
        simpa using
          (Embed.embedState?_exitCorner_eq (Aold := A) (Anew := activeAxes m (Nat.succ s')) (hOld := hOld) (hNew := hNew)
            (st := stNext) (st' := stRec) hEmb)
      have hCorner :
          unpackPlane (activeAxes m (Nat.succ s')) (State.exitCorner stRec) j =
            unpackPlane A (State.exitCorner stNext) j := by
        -- `j` is present in both axis lists.
        have hjNew : j ∈ activeAxes m (Nat.succ s') := hjRec
        simpa [hExitEmb] using
          (unpackPlane_embedBV_eq_of_mem (Aold := A) (Anew := activeAxes m (Nat.succ s')) (x := State.exitCorner stNext)
            (j := j) hj hjNew)

      -- Finish, rewriting `A` to the original level's active axes list.
      simpa [A, stNext, State.exitCorner] using hBit.trans hCorner

private theorem getBit_decodeFromLevel_head_allZero_suffix_eq_entryCorner
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (w : BV (activeAxes m (Nat.succ s)).length)
    (lo : Digits)
    (pAcc pOut : PointBV m)
    (hDec :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w⟩ :: lo) pAcc = some pOut)
    (hLoZero : ∀ d ∈ lo, BV.toNat d.2 = 0) :
    ∀ (j : Axis n), j ∈ activeAxes m (Nat.succ s) →
      ∀ i0, i0 < s →
        getBit (pOut j) i0 =
          unpackPlane (activeAxes m (Nat.succ s))
            (State.entryCorner (stateUpdate (activeAxes m (Nat.succ s)) st w)) j := by
  classical
  intro j hj i0 hi0
  cases s with
  | zero =>
      cases (Nat.not_lt_zero _ hi0)
  | succ s' =>
      let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s'))
      let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w)
      let p1 : PointBV m := writePlane A l pAcc (Nat.succ s')
      let stNext : State n A := stateUpdate (A := A) st w

      have ⟨stRec, hEmb⟩ := Embed.embedState?_activeAxes_succ_some (m := m) (s := Nat.succ s') stNext

      have hDec' := hDec
      simp [decodeFromLevel, A, l, p1, stNext, hEmb] at hDec'
      have hRec :
          decodeFromLevel (m := m) (Nat.succ s') stRec lo p1 = some pOut := hDec'

      have hjRec : j ∈ activeAxes m (Nat.succ s') :=
        ActiveAxes.mem_activeAxes_of_mem_activeAxes_succ (m := m) (s := Nat.succ s') (j := j) hj
      have hAllZero : Digits.allZeroForDecode m (Nat.succ s') lo :=
        Digits.allZeroForDecode_of_decodeFromLevel_toNat_eq_zero (m := m)
          (s := Nat.succ s') (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut) hRec hLoZero
      have hBit :=
        DecodeSuffix.getBit_decodeFromLevel_allZero_eq_entryCorner (m := m)
          (s := Nat.succ s') (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut) hAllZero hRec j hjRec
          i0 hi0

      have hEntryEmb :
          State.entryCorner stRec =
            Embed.embedBV A (activeAxes m (Nat.succ s')) (State.entryCorner stNext) := by
        simpa using
          (Embed.embedState?_entryCorner_eq (Aold := A) (Anew := activeAxes m (Nat.succ s')) (st := stNext) (st' := stRec) hEmb)
      have hCorner :
          unpackPlane (activeAxes m (Nat.succ s')) (State.entryCorner stRec) j =
            unpackPlane A (State.entryCorner stNext) j := by
        have hjNew : j ∈ activeAxes m (Nat.succ s') := hjRec
        simpa [hEntryEmb] using
          (unpackPlane_embedBV_eq_of_mem (Aold := A) (Anew := activeAxes m (Nat.succ s')) (x := State.entryCorner stNext)
            (j := j) hj hjNew)

      simpa [A, stNext, State.entryCorner] using hBit.trans hCorner

/-!
### Inactive axes under all-max/all-zero suffixes

If we decode a head digit at level `s+1` and the remaining suffix digits are either all-max
(`2^k-1`) or all-zero, then any axis which is *not* active at that level must decode to `0`
(all bits `false`). This is the key “activation seam is harmless” fact used later when proving
that only the seam axis changes in the unit-step lemma.
-/

private theorem getBit_decodeFromLevel_head_allMax_suffix_eq_false_of_not_mem_activeAxes
    {n : Nat} {m : Exponents n} :
    ∀ (s : Nat)
      (st : State n (activeAxes m (Nat.succ s)))
      (d : Digit) (lo : Digits)
      (pAcc pOut : PointBV m),
        decodeFromLevel (m := m) (Nat.succ s) st (d :: lo) pAcc = some pOut →
        (∀ d ∈ lo, BV.toNat d.2 = 2 ^ d.1 - 1) →
        ∀ (j : Axis n), j ∉ activeAxes m (Nat.succ s) →
          ∀ i0, i0 < m j → getBit (pOut j) i0 = false := by
  intro s
  induction s with
  | zero =>
      intro st d lo pAcc pOut hDec hLoMax j hj i0 hi0
      have hjAll : j ∈ allAxes n := by simp [allAxes]
      have hmjlt : m j < 1 := by
        have : ¬ (1 ≤ m j) := by
          intro hle
          apply hj
          exact (ActiveAxes.mem_activeAxes_iff (m := m) (s := 1) (j := j)).2 ⟨hjAll, hle⟩
        exact Nat.lt_of_not_ge this
      have hmj0 : m j = 0 := Nat.lt_one_iff.mp hmjlt
      cases (Nat.not_lt_zero i0 (by simpa [hmj0] using hi0))
  | succ s ih =>
      intro st d lo pAcc pOut hDec hLoMax j hj i0 hi0
      rcases d with ⟨kW, w⟩
      let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s))
      by_cases hk : kW = A.length
      · cases hk
        let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w)
        let p1 : PointBV m := writePlane A l pAcc (Nat.succ s)
        let stNext : State n A := stateUpdate (A := A) st w

        have ⟨stRec, hEmb⟩ := Embed.embedState?_activeAxes_succ_some (m := m) (s := Nat.succ s) stNext
        have hDec' := hDec
        simp [decodeFromLevel, A, l, p1, stNext, hEmb] at hDec'
        have hRec : decodeFromLevel (m := m) (Nat.succ s) stRec lo p1 = some pOut := hDec'

        have hjAll : j ∈ allAxes n := by simp [allAxes]
        have hmjlt : m j < Nat.succ (Nat.succ s) := by
          have : ¬ (Nat.succ (Nat.succ s) ≤ m j) := by
            intro hle
            apply hj
            exact (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ (Nat.succ s)) (j := j)).2 ⟨hjAll, hle⟩
          exact Nat.lt_of_not_ge this
        have hmjle : m j ≤ Nat.succ s := Nat.le_of_lt_succ hmjlt
        have hmjCases : m j = Nat.succ s ∨ m j ≤ s := by
          rcases Nat.eq_or_lt_of_le hmjle with hEq | hLt
          · exact Or.inl hEq
          · exact Or.inr (Nat.le_of_lt_succ hLt)
        cases hmjCases with
        | inl hmjEq =>
            have hjRec : j ∈ activeAxes m (Nat.succ s) :=
              (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ s) (j := j)).2 ⟨hjAll, by simpa [hmjEq]⟩
            have hAllMax : Digits.allMaxForDecode m (Nat.succ s) lo :=
              Digits.allMaxForDecode_of_decodeFromLevel_toNat_eq_two_pow_sub_one (m := m)
                (s := Nat.succ s) (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut) hRec hLoMax
            have hBit :=
              DecodeSuffix.getBit_decodeFromLevel_allMax_eq_exitCorner (m := m)
                (s := Nat.succ s) (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut) hAllMax hRec j hjRec
                i0 (by simpa [hmjEq] using hi0)

            have hOld : A.Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ (Nat.succ s))
            have hNew : (activeAxes m (Nat.succ s)).Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ s)
            have hExitEmb :
                State.exitCorner stRec =
                  Embed.embedBV A (activeAxes m (Nat.succ s)) (State.exitCorner stNext) := by
              simpa using
                (Embed.embedState?_exitCorner_eq (Aold := A) (Anew := activeAxes m (Nat.succ s)) (hOld := hOld)
                  (hNew := hNew) (st := stNext) (st' := stRec) hEmb)
            have hCorner : unpackPlane (activeAxes m (Nat.succ s)) (State.exitCorner stRec) j = false := by
              have hjOld : j ∉ A := by simpa [A] using hj
              simpa [hExitEmb] using
                (unpackPlane_embedBV_eq_false_of_not_mem_old (Aold := A) (Anew := activeAxes m (Nat.succ s))
                  (x := State.exitCorner stNext) (j := j) hjOld hjRec)
            simpa [hCorner] using hBit
        | inr hmjLe =>
            have hjNotRec : j ∉ activeAxes m (Nat.succ s) := by
              intro hjMem
              have hcond := (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ s) (j := j)).1 hjMem
              have : Nat.succ s ≤ s := Nat.le_trans hcond.2 hmjLe
              exact (Nat.not_succ_le_self s this).elim
            cases lo with
            | nil =>
                -- No digits left at this recursive level: impossible under `= some pOut`.
                simp [decodeFromLevel] at hRec
            | cons d2 lo2 =>
                have hLo2 : ∀ d ∈ lo2, BV.toNat d.2 = 2 ^ d.1 - 1 := by
                  intro d hd
                  exact hLoMax d (by simp [hd])
                exact ih (st := stRec) (d := d2) (lo := lo2) (pAcc := p1) (pOut := pOut) hRec hLo2 j hjNotRec i0 hi0
      · -- width mismatch makes `decodeFromLevel` return `none`, contradicting `hDec`.
        simp [decodeFromLevel, A, hk] at hDec

private theorem getBit_decodeFromLevel_head_allZero_suffix_eq_false_of_not_mem_activeAxes
    {n : Nat} {m : Exponents n} :
    ∀ (s : Nat)
      (st : State n (activeAxes m (Nat.succ s)))
      (d : Digit) (lo : Digits)
      (pAcc pOut : PointBV m),
        decodeFromLevel (m := m) (Nat.succ s) st (d :: lo) pAcc = some pOut →
        (∀ d ∈ lo, BV.toNat d.2 = 0) →
        ∀ (j : Axis n), j ∉ activeAxes m (Nat.succ s) →
          ∀ i0, i0 < m j → getBit (pOut j) i0 = false := by
  intro s
  induction s with
  | zero =>
      intro st d lo pAcc pOut hDec hLoZero j hj i0 hi0
      have hjAll : j ∈ allAxes n := by simp [allAxes]
      have hmjlt : m j < 1 := by
        have : ¬ (1 ≤ m j) := by
          intro hle
          apply hj
          exact (ActiveAxes.mem_activeAxes_iff (m := m) (s := 1) (j := j)).2 ⟨hjAll, hle⟩
        exact Nat.lt_of_not_ge this
      have hmj0 : m j = 0 := Nat.lt_one_iff.mp hmjlt
      cases (Nat.not_lt_zero i0 (by simpa [hmj0] using hi0))
  | succ s ih =>
      intro st d lo pAcc pOut hDec hLoZero j hj i0 hi0
      rcases d with ⟨kW, w⟩
      let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s))
      by_cases hk : kW = A.length
      · cases hk
        let l : BV A.length := Tinv st.e st.dPos.val (BV.gc w)
        let p1 : PointBV m := writePlane A l pAcc (Nat.succ s)
        let stNext : State n A := stateUpdate (A := A) st w

        have ⟨stRec, hEmb⟩ := Embed.embedState?_activeAxes_succ_some (m := m) (s := Nat.succ s) stNext
        have hDec' := hDec
        simp [decodeFromLevel, A, l, p1, stNext, hEmb] at hDec'
        have hRec : decodeFromLevel (m := m) (Nat.succ s) stRec lo p1 = some pOut := hDec'

        have hjAll : j ∈ allAxes n := by simp [allAxes]
        have hmjlt : m j < Nat.succ (Nat.succ s) := by
          have : ¬ (Nat.succ (Nat.succ s) ≤ m j) := by
            intro hle
            apply hj
            exact (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ (Nat.succ s)) (j := j)).2 ⟨hjAll, hle⟩
          exact Nat.lt_of_not_ge this
        have hmjle : m j ≤ Nat.succ s := Nat.le_of_lt_succ hmjlt
        have hmjCases : m j = Nat.succ s ∨ m j ≤ s := by
          rcases Nat.eq_or_lt_of_le hmjle with hEq | hLt
          · exact Or.inl hEq
          · exact Or.inr (Nat.le_of_lt_succ hLt)
        cases hmjCases with
        | inl hmjEq =>
            have hjRec : j ∈ activeAxes m (Nat.succ s) :=
              (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ s) (j := j)).2 ⟨hjAll, by simpa [hmjEq]⟩
            have hAllZero : Digits.allZeroForDecode m (Nat.succ s) lo :=
              Digits.allZeroForDecode_of_decodeFromLevel_toNat_eq_zero (m := m)
                (s := Nat.succ s) (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut) hRec hLoZero
            have hBit :=
              DecodeSuffix.getBit_decodeFromLevel_allZero_eq_entryCorner (m := m)
                (s := Nat.succ s) (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut) hAllZero hRec j hjRec
                i0 (by simpa [hmjEq] using hi0)

            have hEntryEmb :
                State.entryCorner stRec =
                  Embed.embedBV A (activeAxes m (Nat.succ s)) (State.entryCorner stNext) := by
              simpa using
                (Embed.embedState?_entryCorner_eq (Aold := A) (Anew := activeAxes m (Nat.succ s)) (st := stNext) (st' := stRec)
                  hEmb)
            have hCorner : unpackPlane (activeAxes m (Nat.succ s)) (State.entryCorner stRec) j = false := by
              have hjOld : j ∉ A := by simpa [A] using hj
              simpa [hEntryEmb] using
                (unpackPlane_embedBV_eq_false_of_not_mem_old (Aold := A) (Anew := activeAxes m (Nat.succ s))
                  (x := State.entryCorner stNext) (j := j) hjOld hjRec)
            simpa [hCorner] using hBit
        | inr hmjLe =>
            have hjNotRec : j ∉ activeAxes m (Nat.succ s) := by
              intro hjMem
              have hcond := (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ s) (j := j)).1 hjMem
              have : Nat.succ s ≤ s := Nat.le_trans hcond.2 hmjLe
              exact (Nat.not_succ_le_self s this).elim
            cases lo with
            | nil =>
                simp [decodeFromLevel] at hRec
            | cons d2 lo2 =>
                have hLo2 : ∀ d ∈ lo2, BV.toNat d.2 = 0 := by
                  intro d hd
                  exact hLoZero d (by simp [hd])
                exact ih (st := stRec) (d := d2) (lo := lo2) (pAcc := p1) (pOut := pOut) hRec hLo2 j hjNotRec i0 hi0
      · simp [decodeFromLevel, A, hk] at hDec

/-!
### Seam unit-step lemma (core of Theorem 5.4)

This is the “carry → dyadic boundary unit step” statement used at the pivot level:
decoding a head digit `w` with an all-max suffix gives the exit corner of child `w`,
decoding `w+1` with an all-zero suffix gives the entry corner of child `w+1`,
and the resulting lattice points are `L¹`-neighbors.
-/

private theorem seam_unit_step_of_decodeFromLevel_succDigit
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (d : Digit) (lo : Digits)
    (pAcc pOut₁ pOut₂ : PointBV m)
    (hDec₁ : decodeFromLevel (m := m) (Nat.succ s) st (d :: lo) pAcc = some pOut₁)
    (hDec₂ :
      decodeFromLevel (m := m) (Nat.succ s) st
          ((Digits.succDigit d).1 :: (lo.map Digits.zeroLike)) pAcc =
        some pOut₂)
    (hCarry : (Digits.succDigit d).2 = false)
    (hLoMax : ∀ d ∈ lo, BV.toNat d.2 = 2 ^ d.1 - 1) :
    l1Dist pOut₁ pOut₂ = 1 := by
  classical
  rcases d with ⟨kW, w⟩
  let A : List (Axis n) := activeAxes m (Nat.succ s)

  -- Width match forced by successful decoding.
  have hkW : kW = A.length := by
    by_contra hne
    have hNone : decodeFromLevel (m := m) (Nat.succ s) st (⟨kW, w⟩ :: lo) pAcc = none := by
      simp [decodeFromLevel, A, hne]
    have : (none : Option (PointBV m)) = some pOut₁ := by
      simpa [hNone] using hDec₁
    exact Option.noConfusion this
  cases hkW

  let k : Nat := A.length
  have hk : 0 < k := State.length_pos st
  let i : Nat := BV.toNat w
  have hwOfNat : BV.ofNat (k := k) i = w := by
    simpa [i] using (BV.ofNat_toNat (x := w))

  have hCarryW : (Digits.succDigit ⟨k, w⟩).2 = false := by
    simpa [A, k] using hCarry
  have ht : tsb i < k := by
    simpa [i] using (Digits.succDigit_carry_false_imp_tsb_lt (d := ⟨k, w⟩) hCarryW)
  let t : Fin k := ⟨tsb i, ht⟩
  let r : Nat := st.dPos.val.succ
  let g : Fin k := ⟨(t.val + r) % k, Nat.mod_lt _ hk⟩
  let ax : Axis n := A.get g

  -- Normalize head digits into `ofNat` form so we can use the head-XOR bridge lemma.
  have hSuccHead :
      (Digits.succDigit ⟨k, w⟩).1 = ⟨k, BV.ofNat (k := k) i.succ⟩ := by
    simpa [i] using (Digits.succDigit_eq_ofNat_succ_of_carry_false (d := ⟨k, w⟩) hCarryW)
  have hDec₁' :
      decodeFromLevel (m := m) (Nat.succ s) st (⟨k, BV.ofNat (k := k) i⟩ :: lo) pAcc = some pOut₁ := by
    simpa [hwOfNat] using hDec₁
  have hDec₂' :
      decodeFromLevel (m := m) (Nat.succ s) st
          (⟨k, BV.ofNat (k := k) i.succ⟩ :: (lo.map Digits.zeroLike)) pAcc =
        some pOut₂ := by
    -- Rewrite the successor head digit out of `succDigit`.
    simpa [hSuccHead, k] using (hDec₂ : decodeFromLevel (m := m) (Nat.succ s) st
      ((Digits.succDigit ⟨k, w⟩).1 :: (lo.map Digits.zeroLike)) pAcc = some pOut₂)

  -- Plane XOR at the head level is a rotated one-hot at `tsb i`.
  have hXorPlaneRaw :
      BV.xor (packPlane A pOut₁ s) (packPlane A pOut₂ s) =
        BV.rotL (k := k) r (BV.oneHotFin t) := by
    simpa [A, k, i, r, t] using
      (DecodeHeadXor.packPlane_xor_decodeFromLevel_ofNat_succ_heads (m := m)
        (s := s) (st := st) (i := i)
        (rest₁ := lo) (rest₂ := lo.map Digits.zeroLike)
        (pAcc := pAcc) (pOut₁ := pOut₁) (pOut₂ := pOut₂)
        hDec₁' hDec₂' ht)
  have hRotOneHot : BV.rotL (k := k) r (BV.oneHotFin t) = BV.oneHotFin g := by
    simpa [g, r, t] using (BV.rotL_oneHotFin_eq_of_pos (k := k) hk r t)
  have hXorPlane :
      BV.xor (packPlane A pOut₁ s) (packPlane A pOut₂ s) = BV.oneHotFin g :=
    hXorPlaneRaw.trans hRotOneHot

  -- Active-axis facts for the seam axis.
  have hAxMem : ax ∈ A := ListLemmas.get_mem (xs := A) g
  have hAxActive :
      Nat.succ s ≤ m ax := (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ s) (j := ax)).1 hAxMem |>.2
  have hsAx : s < m ax := Nat.lt_of_lt_of_le (Nat.lt_succ_self s) hAxActive
  have hposAx : pos? A ax = some g := by
    have hnd : A.Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ s)
    simpa [ax] using (Pos.pos?_get_of_nodup (xs := A) hnd g)

  -- Name the two head-plane bits on the seam axis.
  let b₁ : Bool := getBit (pOut₁ ax) s
  let b₂ : Bool := getBit (pOut₂ ax) s

  have hb₁ : b₁ = (packPlane A pOut₁ s) g := by
    simp [b₁, ax, packPlane]
  have hb₂ : b₂ = (packPlane A pOut₂ s) g := by
    simp [b₂, ax, packPlane]
  have hDiffPlane : BV.bxor b₁ b₂ = true := by
    have hAt := congrArg (fun w => w g) hXorPlane
    simpa [BV.xor, BV.oneHotFin, hb₁, hb₂] using hAt
  have hb₂_eq_not : b₂ = (!b₁) := by
    cases hb₁v : b₁ <;> cases hb₂v : b₂ <;> simp [BV.bxor, hb₁v, hb₂v] at hDiffPlane <;> simp [hb₁v, hb₂v]

  -- Child states `st₁` and `st₂` at the pivot level.
  set st₁ : State n A := stateUpdate A st w with hst₁
  set st₂ : State n A := stateUpdate A st (BV.ofNat (k := k) i.succ) with hst₂

  -- `toNat (ofNat i.succ) = i.succ` since `succDigit` does not overflow.
  have hiSucc : i.succ < 2 ^ k := by
    have hlt : i.succ < Digits.base k := by
      simpa [Digits.base, i] using
        (Digits.succDigit_carry_false_imp_toNat_succ_lt_base (d := ⟨k, w⟩) hCarryW)
    simpa [Digits.base, Nat.shiftLeft_eq] using hlt
  have hToNatSucc : BV.toNat (BV.ofNat (k := k) i.succ) = i.succ :=
    toNat_ofNat_eq_of_lt (k := k) (n := i.succ) hiSucc

  -- Entry-bit alignment: the entry-corner bit of `st₂` at `g` matches the decoded plane bit `b₁`.
  have hEntryBit : st₂.e g = b₁ := by
    have hTinv :
        Tinv st.e st.dPos.val (BV.gc w) = BV.xor st.e (BV.rotL (k := k) r (BV.gc w)) := by
      simpa [Tinv, r] using (BV.xor_comm (BV.rotL (k := k) r (BV.gc w)) st.e)
    have hst₂e : st₂.e = BV.xor st.e (BV.rotL (k := k) r (childEntry k i.succ)) := by
      simp [hst₂, stateUpdate, i, k, hToNatSucc, r, State.mk']
    have hRotEq :
        (BV.rotL (k := k) r (childEntry k i.succ)) g = (BV.rotL (k := k) r (BV.gc w)) g := by
      have h1 : (BV.rotL (k := k) r (childEntry k i.succ)) g = (childEntry k i.succ) t := by
        simpa [g, t] using (rotL_apply_at_add_mod (k := k) hk r t (childEntry k i.succ))
      have h2 : (BV.rotL (k := k) r (BV.gc w)) g = (BV.gc w) t := by
        simpa [g, t] using (rotL_apply_at_add_mod (k := k) hk r t (BV.gc w))
      have hChild : (childEntry k i.succ) t = (BV.gc w) t := by
        have := childEntry_succ_get_tsb_eq_gc_get_tsb (k := k) hk i ht
        simpa [t, i, hwOfNat] using this
      exact h1.trans (hChild.trans h2.symm)

    have hPlane₁ :
        packPlane A pOut₁ s = Tinv st.e st.dPos.val (BV.gc w) := by
      have h :=
        (DecodeHead.packPlane_decodeFromLevel_head (m := m) (s := s) (st := st)
          (w := BV.ofNat (k := k) i) (rest := lo) (pAcc := pAcc) (pOut := pOut₁) hDec₁')
      simpa [A, k, hwOfNat] using h
    have hb₁' : b₁ = (Tinv st.e st.dPos.val (BV.gc w)) g := by
      have : (packPlane A pOut₁ s) g = (Tinv st.e st.dPos.val (BV.gc w)) g := by
        simpa using congrArg (fun l => l g) hPlane₁
      simpa [b₁, hb₁] using this

    calc
      st₂.e g = (BV.xor st.e (BV.rotL (k := k) r (childEntry k i.succ))) g := by simpa [hst₂e]
      _ = BV.bxor (st.e g) ((BV.rotL (k := k) r (childEntry k i.succ)) g) := by rfl
      _ = BV.bxor (st.e g) ((BV.rotL (k := k) r (BV.gc w)) g) := by simpa [hRotEq]
      _ = (BV.xor st.e (BV.rotL (k := k) r (BV.gc w))) g := by rfl
      _ = (Tinv st.e st.dPos.val (BV.gc w)) g := by simpa [hTinv]
      _ = b₁ := by simpa [hb₁'] using rfl

  -- Glue: `entryCorner st₂ = exitCorner st₁ XOR oneHot g`.
  have hGlue : st₂.e = BV.xor (State.exitCorner st₁) (BV.oneHotFin g) := by
    have h := lemma_5_2 (st := st) (w := w) ht
    have hRot : BV.rotL (k := k) r (BV.oneHotFin t) = BV.oneHotFin g := hRotOneHot
    -- `lemma_5_2` yields the glue equation with a rotated one-hot at `tsb i`;
    -- rewrite it to the concrete seam index `g`.
    simpa [hst₁, hst₂, State.exitCorner, hRot, i, k, A, t, r] using h

  have hExitBit : (State.exitCorner st₁) g = (!b₁) := by
    have hAt := congrArg (fun w => w g) hGlue
    -- `hAt` says `b₁ = exitCornerBit XOR true`, so the exit bit is `!b₁`.
    have hAt' : b₁ = BV.bxor ((State.exitCorner st₁) g) true := by
      simpa [BV.xor, BV.oneHotFin, hEntryBit] using hAt
    cases hb : b₁ <;> cases hx : (State.exitCorner st₁) g <;> simp [BV.bxor, hb, hx] at hAt' <;> simp [hb, hx]

  -- Low-bit values below plane `s` on the seam axis.
  have hLowBits₁ : ∀ i0, i0 < s → getBit (pOut₁ ax) i0 = (State.exitCorner st₁) g := by
    intro i0 hi0
    have hBit :=
      getBit_decodeFromLevel_head_allMax_suffix_eq_exitCorner (m := m)
        (s := s) (st := st) (w := w) (lo := lo) (pAcc := pAcc) (pOut := pOut₁) (by simpa [A] using hDec₁)
        hLoMax ax hAxMem i0 hi0
    simpa [A, unpackPlane, hposAx, hst₁, State.exitCorner] using hBit
  have hLoZero : ∀ d ∈ lo.map Digits.zeroLike, BV.toNat d.2 = 0 := by
    intro d hd
    rcases List.mem_map.mp hd with ⟨d0, hd0, rfl⟩
    simp [Digits.zeroLike, BV.toNat, BV.zero]
  have hLowBits₂ : ∀ i0, i0 < s → getBit (pOut₂ ax) i0 = st₂.e g := by
    intro i0 hi0
    have hBit :=
      getBit_decodeFromLevel_head_allZero_suffix_eq_entryCorner (m := m)
        (s := s) (st := st) (w := BV.ofNat (k := k) i.succ) (lo := lo.map Digits.zeroLike)
        (pAcc := pAcc) (pOut := pOut₂) (by simpa [A] using hDec₂') hLoZero ax hAxMem i0 hi0
    simpa [A, unpackPlane, hposAx, State.entryCorner, hst₂] using hBit

  -- Other axes are equal (as naturals) because only the seam axis changes.
  have hEqOther : ∀ j : Axis n, j ≠ ax → pointToNat pOut₁ j = pointToNat pOut₂ j := by
    intro j hjAx
    have hEqBV : pOut₁ j = pOut₂ j := by
      funext tFin
      by_cases hjA : j ∈ A
      · by_cases hge : Nat.succ s ≤ tFin.val
        · have hPres₁ :
              pOut₁ j tFin = pAcc j tFin :=
            DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := ⟨k, w⟩ :: lo)
              (pAcc := pAcc) (pOut := pOut₁) (by simpa [A] using hDec₁)
              (j := j) (t := tFin) hge
          have hPres₂ :
              pOut₂ j tFin = pAcc j tFin :=
            DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := (Digits.succDigit ⟨k, w⟩).1 :: lo.map Digits.zeroLike)
              (pAcc := pAcc) (pOut := pOut₂) (by simpa [A] using hDec₂)
              (j := j) (t := tFin) hge
          simpa [hPres₁, hPres₂]
        · have htlt : tFin.val < Nat.succ s := Nat.lt_of_not_ge hge
          have htle : tFin.val ≤ s := Nat.lt_succ_iff.mp htlt
          cases lt_or_eq_of_le htle with
          | inl htltS =>
              have hCornerEq :
                  unpackPlane A (State.exitCorner st₁) j = unpackPlane A (State.entryCorner st₂) j := by
                rcases Pos.pos?_some_of_mem (xs := A) (a := j) hjA with ⟨tj, htj⟩
                have hget : A.get tj = j := Pos.get_of_pos?_some (xs := A) (a := j) (i := tj) htj
                have htjNe : tj ≠ g := by
                  intro hEq
                  apply hjAx
                  have : j = ax := by simpa [ax, hEq] using hget.symm
                  simpa [this]
                have honeHot : (BV.oneHotFin g) tj = false := by
                  simp [BV.oneHotFin, htjNe]
                have hAt : unpackPlane A st₂.e j = unpackPlane A (State.exitCorner st₁) j := by
                  have hEq := congrArg (fun l => l tj) hGlue
                  have hL : unpackPlane A st₂.e j = st₂.e tj := by simp [unpackPlane, htj]
                  have hR : unpackPlane A (State.exitCorner st₁) j = (State.exitCorner st₁) tj := by simp [unpackPlane, htj]
                  have hX : st₂.e tj = (State.exitCorner st₁) tj := by
                    -- At indices `tj ≠ g`, the one-hot bit is `false`, so the XOR is unchanged.
                    simpa [BV.xor, BV.oneHotFin, htjNe, BV.bxor] using hEq
                  simpa [hL, hR] using hX
                simpa [State.entryCorner] using hAt.symm

              have hLow₁ : getBit (pOut₁ j) tFin.val = unpackPlane A (State.exitCorner st₁) j :=
                getBit_decodeFromLevel_head_allMax_suffix_eq_exitCorner (m := m)
                  (s := s) (st := st) (w := w) (lo := lo) (pAcc := pAcc) (pOut := pOut₁) (by simpa [A] using hDec₁)
                  hLoMax j hjA tFin.val htltS
              have hLow₂ : getBit (pOut₂ j) tFin.val = unpackPlane A (State.entryCorner st₂) j :=
                getBit_decodeFromLevel_head_allZero_suffix_eq_entryCorner (m := m)
                  (s := s) (st := st) (w := BV.ofNat (k := k) i.succ) (lo := lo.map Digits.zeroLike) (pAcc := pAcc) (pOut := pOut₂)
                  (by simpa [A] using hDec₂') hLoZero j hjA tFin.val htltS
              have hbit₁ : pOut₁ j tFin = unpackPlane A (State.exitCorner st₁) j := by
                simpa [getBit, tFin.isLt] using hLow₁
              have hbit₂ : pOut₂ j tFin = unpackPlane A (State.entryCorner st₂) j := by
                simpa [getBit, tFin.isLt] using hLow₂
              simpa [hbit₁, hbit₂, hCornerEq]
          | inr hteq =>
              rcases Pos.pos?_some_of_mem (xs := A) (a := j) hjA with ⟨tj, htj⟩
              have hget : A.get tj = j := Pos.get_of_pos?_some (xs := A) (a := j) (i := tj) htj
              have htjNe : tj ≠ g := by
                intro hEq
                apply hjAx
                have : j = ax := by simpa [ax, hEq] using hget.symm
                simpa [this]
              have hAt := congrArg (fun l => l tj) hXorPlane
              have hbxor :
                  BV.bxor ((packPlane A pOut₁ s) tj) ((packPlane A pOut₂ s) tj) = false := by
                simpa [BV.xor, BV.oneHotFin, htjNe] using hAt
              have hEqPlane : (packPlane A pOut₁ s) tj = (packPlane A pOut₂ s) tj := by
                cases h1 : (packPlane A pOut₁ s) tj <;> cases h2 : (packPlane A pOut₂ s) tj <;>
                  simp [BV.bxor, h1, h2] at hbxor <;> simp [h1, h2]
              have hBit₁ : getBit (pOut₁ j) s = (packPlane A pOut₁ s) tj := by
                have : (packPlane A pOut₁ s) tj = getBit (pOut₁ j) s := by
                  -- `packPlane` at `tj` reads axis `A.get tj`, and `A.get tj = j`.
                  -- `simp` normalizes `A.get tj` to the bracket form `A[tj.1]`.
                  have hget' : A[tj.1] = j := by simpa using hget
                  have : getBit (pOut₁ A[tj.1]) s = getBit (pOut₁ j) s := by
                    -- rewrite the axis index inside `pOut₁`
                    -- (avoid relying on simp to close the reflexive goal)
                    rw [hget']
                  simpa [packPlane] using this
                exact this.symm
              have hBit₂ : getBit (pOut₂ j) s = (packPlane A pOut₂ s) tj := by
                have : (packPlane A pOut₂ s) tj = getBit (pOut₂ j) s := by
                  have hget' : A[tj.1] = j := by simpa using hget
                  have : getBit (pOut₂ A[tj.1]) s = getBit (pOut₂ j) s := by
                    rw [hget']
                  simpa [packPlane] using this
                exact this.symm
              have hBits : getBit (pOut₁ j) s = getBit (pOut₂ j) s := by
                simpa [hBit₁, hBit₂] using hEqPlane
              have hBits' : getBit (pOut₁ j) tFin.val = getBit (pOut₂ j) tFin.val := by
                -- rewrite `s` into `tFin.val`
                simpa [hteq.symm] using hBits
              simpa [getBit, tFin.isLt] using hBits'
      · have hZero₁ :
            getBit (pOut₁ j) tFin.val = false :=
          getBit_decodeFromLevel_head_allMax_suffix_eq_false_of_not_mem_activeAxes (m := m)
            (s := s) (st := st) (d := ⟨k, w⟩) (lo := lo) (pAcc := pAcc) (pOut := pOut₁) (by simpa [A] using hDec₁)
            hLoMax j hjA tFin.val tFin.isLt
        have hZero₂ :
            getBit (pOut₂ j) tFin.val = false :=
          getBit_decodeFromLevel_head_allZero_suffix_eq_false_of_not_mem_activeAxes (m := m)
            (s := s) (st := st) (d := ⟨k, BV.ofNat (k := k) i.succ⟩) (lo := lo.map Digits.zeroLike) (pAcc := pAcc) (pOut := pOut₂)
            (by simpa [A] using hDec₂') hLoZero j hjA tFin.val tFin.isLt
        have hbit₁ : pOut₁ j tFin = false := by
          simpa [getBit, tFin.isLt] using hZero₁
        have hbit₂ : pOut₂ j tFin = false := by
          simpa [getBit, tFin.isLt] using hZero₂
        simpa [hbit₁, hbit₂]
    simpa [pointToNat] using congrArg BV.toNat hEqBV

  -- Choose low/high ordering by inspecting the seam plane bit.
  by_cases hb : b₁ = false
  · have hb2 : b₂ = true := by simpa [hb, hb₂_eq_not]
    have hLowOnes : ∀ i0, i0 < s → getBit (pOut₁ ax) i0 = true := by
      intro i0 hi0
      have := hLowBits₁ i0 hi0
      simpa [hExitBit, hb] using this
    have hHighZeros : ∀ i0, i0 < s → getBit (pOut₂ ax) i0 = false := by
      intro i0 hi0
      have := hLowBits₂ i0 hi0
      simpa [hEntryBit, hb] using this

    have hxmod : pointToNat pOut₁ ax % 2 ^ (Nat.succ s) = 2 ^ s - 1 := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < Nat.succ s
      · have hj' : j < m ax := lt_of_lt_of_le hj hAxActive
        have hx : Nat.testBit (pointToNat pOut₁ ax) j = getBit (pOut₁ ax) j :=
          testBit_pointToNat_eq_getBit (p := pOut₁) (j := ax) (i := j) hj'
        by_cases hjs : j < s
        · have hgb : getBit (pOut₁ ax) j = true := hLowOnes j hjs
          simp [Nat.testBit_mod_two_pow, hj, hx, hgb, Nat.testBit_two_pow_sub_one, hjs]
        · have hjs' : j = s := Nat.eq_of_lt_succ_of_not_lt hj hjs
          cases hjs'
          have hgb : getBit (pOut₁ ax) s = false := by simpa [b₁] using hb
          have hns : ¬ s < s := Nat.lt_irrefl s
          simp [Nat.testBit_mod_two_pow, hj, hx, hgb, Nat.testBit_two_pow_sub_one, hns]
      · have hjs : ¬ j < s := by
          intro hlt
          exact hj (Nat.lt_trans hlt (Nat.lt_succ_self s))
        simp [Nat.testBit_mod_two_pow, hj, Nat.testBit_two_pow_sub_one, hjs]

    have hymod : pointToNat pOut₂ ax % 2 ^ (Nat.succ s) = 2 ^ s := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < Nat.succ s
      · have hj' : j < m ax := lt_of_lt_of_le hj hAxActive
        have hy : Nat.testBit (pointToNat pOut₂ ax) j = getBit (pOut₂ ax) j :=
          testBit_pointToNat_eq_getBit (p := pOut₂) (j := ax) (i := j) hj'
        by_cases hjs : j < s
        · have hgb : getBit (pOut₂ ax) j = false := hHighZeros j hjs
          have hne : j ≠ s := Nat.ne_of_lt hjs
          have hsne : s ≠ j := by
            intro hEq
            exact hne hEq.symm
          simp [Nat.testBit_mod_two_pow, hj, hy, hgb, Nat.testBit_two_pow, hsne]
        · have hjs' : j = s := Nat.eq_of_lt_succ_of_not_lt hj hjs
          cases hjs'
          have hgb : getBit (pOut₂ ax) s = true := by simpa [b₂] using hb2
          simp [Nat.testBit_mod_two_pow, hj, hy, hgb, Nat.testBit_two_pow]
      · have hsne : s ≠ j := by
          intro hEq
          apply hj
          simpa [hEq] using (Nat.lt_succ_self s)
        simp [Nat.testBit_mod_two_pow, hj, Nat.testBit_two_pow, hsne]

    have hdiv :
        pointToNat pOut₁ ax / 2 ^ (Nat.succ s) = pointToNat pOut₂ ax / 2 ^ (Nat.succ s) := by
      apply Nat.eq_of_testBit_eq
      intro j
      have hx := Nat.testBit_div_two_pow (n := Nat.succ s) (x := pointToNat pOut₁ ax) (i := j)
      have hy := Nat.testBit_div_two_pow (n := Nat.succ s) (x := pointToNat pOut₂ ax) (i := j)
      have hj1 : Nat.succ s + j < m ax ∨ m ax ≤ Nat.succ s + j := lt_or_ge (Nat.succ s + j) (m ax)
      cases hj1 with
      | inl hjlt =>
          let tFin : Fin (m ax) := ⟨Nat.succ s + j, hjlt⟩
          have hPres₁ :
              pOut₁ ax tFin = pAcc ax tFin :=
            DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := ⟨k, w⟩ :: lo) (pAcc := pAcc) (pOut := pOut₁) (by simpa [A] using hDec₁)
              (j := ax) (t := tFin) (Nat.le_add_right _ _)
          have hPres₂ :
              pOut₂ ax tFin = pAcc ax tFin :=
            DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := (Digits.succDigit ⟨k, w⟩).1 :: lo.map Digits.zeroLike) (pAcc := pAcc)
              (pOut := pOut₂) (by simpa [A] using hDec₂) (j := ax) (t := tFin) (Nat.le_add_right _ _)
          have hxBit : Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) = pAcc ax tFin := by
            have hx' : Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) = pOut₁ ax tFin := by
              simpa [pointToNat, BV.ofNat] using
                congrArg (fun (v : BV (m ax)) => v tFin) (BV.ofNat_toNat (x := pOut₁ ax))
            simpa [hx', hPres₁]
          have hyBit : Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) = pAcc ax tFin := by
            have hy' : Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) = pOut₂ ax tFin := by
              simpa [pointToNat, BV.ofNat] using
                congrArg (fun (v : BV (m ax)) => v tFin) (BV.ofNat_toNat (x := pOut₂ ax))
            simpa [hy', hPres₂]
          have hxShift :
              Nat.testBit (pointToNat pOut₁ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx
          have hyShift :
              Nat.testBit (pointToNat pOut₂ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hy
          have hEqHi :
              Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) =
                Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := by
            calc
              Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) = pAcc ax tFin := hxBit
              _ = Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := by
                simpa using hyBit.symm
          calc
            Nat.testBit (pointToNat pOut₁ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := hxShift
            _ = Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := hEqHi
            _ = Nat.testBit (pointToNat pOut₂ ax / 2 ^ (Nat.succ s)) j := by
              simpa using hyShift.symm
      | inr hjge =>
          have hlt₁ : pointToNat pOut₁ ax < 2 ^ (m ax) := by
            simpa [pointToNat, Nat.shiftLeft_eq] using (BV.toNat_lt_shiftLeft_one (x := pOut₁ ax))
          have hlt₂ : pointToNat pOut₂ ax < 2 ^ (m ax) := by
            simpa [pointToNat, Nat.shiftLeft_eq] using (BV.toNat_lt_shiftLeft_one (x := pOut₂ ax))
          have hpow : 2 ^ (m ax) ≤ 2 ^ (Nat.succ s + j) :=
            Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hjge
          have hlt₁' : pointToNat pOut₁ ax < 2 ^ (Nat.succ s + j) := lt_of_lt_of_le hlt₁ hpow
          have hlt₂' : pointToNat pOut₂ ax < 2 ^ (Nat.succ s + j) := lt_of_lt_of_le hlt₂ hpow
          have hxBit : Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) = false :=
            Nat.testBit_eq_false_of_lt hlt₁'
          have hyBit : Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) = false :=
            Nat.testBit_eq_false_of_lt hlt₂'
          have hxShift :
              Nat.testBit (pointToNat pOut₁ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx
          have hyShift :
              Nat.testBit (pointToNat pOut₂ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hy
          have hEqHi :
              Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) =
                Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := by
            calc
              Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) = false := hxBit
              _ = Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := by
                simpa using hyBit.symm
          calc
            Nat.testBit (pointToNat pOut₁ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := hxShift
            _ = Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := hEqHi
            _ = Nat.testBit (pointToNat pOut₂ ax / 2 ^ (Nat.succ s)) j := by
              simpa using hyShift.symm

    set a : Nat := pointToNat pOut₁ ax / 2 ^ (Nat.succ s)
    have hgLow : pointToNat pOut₁ ax = a * 2 ^ (Nat.succ s) + (2 ^ s - 1) := by
      have h := (Nat.div_add_mod' (pointToNat pOut₁ ax) (2 ^ (Nat.succ s))).symm
      simpa [a, hxmod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using h
    have hgHigh : pointToNat pOut₂ ax = a * 2 ^ (Nat.succ s) + 2 ^ s := by
      have h := (Nat.div_add_mod' (pointToNat pOut₂ ax) (2 ^ (Nat.succ s))).symm
      simpa [a, hdiv, hymod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using h

    exact lemma_5_3 (m := m) (g := ax) (s := Nat.succ s) (a := a) (hs := Nat.succ_pos s)
      (pLow := pOut₁) (pHigh := pOut₂) hgLow hgHigh hEqOther
  · have hb1 : b₁ = true := by
      cases hb1' : b₁ <;> simp [hb1'] at hb <;> simp [hb1']
    have hb2 : b₂ = false := by
      simpa [hb1, hb₂_eq_not]
    have hLowOnes : ∀ i0, i0 < s → getBit (pOut₂ ax) i0 = true := by
      intro i0 hi0
      have := hLowBits₂ i0 hi0
      simpa [hEntryBit, hb1] using this
    have hHighZeros : ∀ i0, i0 < s → getBit (pOut₁ ax) i0 = false := by
      intro i0 hi0
      have := hLowBits₁ i0 hi0
      simpa [hExitBit, hb1] using this

    have hxmod : pointToNat pOut₂ ax % 2 ^ (Nat.succ s) = 2 ^ s - 1 := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < Nat.succ s
      · have hj' : j < m ax := lt_of_lt_of_le hj hAxActive
        have hx : Nat.testBit (pointToNat pOut₂ ax) j = getBit (pOut₂ ax) j :=
          testBit_pointToNat_eq_getBit (p := pOut₂) (j := ax) (i := j) hj'
        by_cases hjs : j < s
        · have hgb : getBit (pOut₂ ax) j = true := hLowOnes j hjs
          simp [Nat.testBit_mod_two_pow, hj, hx, hgb, Nat.testBit_two_pow_sub_one, hjs]
        · have hjs' : j = s := Nat.eq_of_lt_succ_of_not_lt hj hjs
          cases hjs'
          have hgb : getBit (pOut₂ ax) s = false := by simpa [b₂] using hb2
          have hns : ¬ s < s := Nat.lt_irrefl s
          simp [Nat.testBit_mod_two_pow, hj, hx, hgb, Nat.testBit_two_pow_sub_one, hns]
      · have hjs : ¬ j < s := by
          intro hlt
          exact hj (Nat.lt_trans hlt (Nat.lt_succ_self s))
        simp [Nat.testBit_mod_two_pow, hj, Nat.testBit_two_pow_sub_one, hjs]

    have hymod : pointToNat pOut₁ ax % 2 ^ (Nat.succ s) = 2 ^ s := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < Nat.succ s
      · have hj' : j < m ax := lt_of_lt_of_le hj hAxActive
        have hy : Nat.testBit (pointToNat pOut₁ ax) j = getBit (pOut₁ ax) j :=
          testBit_pointToNat_eq_getBit (p := pOut₁) (j := ax) (i := j) hj'
        by_cases hjs : j < s
        · have hgb : getBit (pOut₁ ax) j = false := hHighZeros j hjs
          have hne : j ≠ s := Nat.ne_of_lt hjs
          have hsne : s ≠ j := by
            intro hEq
            exact hne hEq.symm
          simp [Nat.testBit_mod_two_pow, hj, hy, hgb, Nat.testBit_two_pow, hsne]
        · have hjs' : j = s := Nat.eq_of_lt_succ_of_not_lt hj hjs
          cases hjs'
          have hgb : getBit (pOut₁ ax) s = true := by simpa [b₁] using hb1
          simp [Nat.testBit_mod_two_pow, hj, hy, hgb, Nat.testBit_two_pow]
      · have hne : j ≠ s := by
          intro hEq
          apply hj
          simpa [hEq] using (Nat.lt_succ_self s)
        have hsne : s ≠ j := by
          intro hEq
          exact hne hEq.symm
        simp [Nat.testBit_mod_two_pow, hj, Nat.testBit_two_pow, hsne]

    have hdiv :
        pointToNat pOut₂ ax / 2 ^ (Nat.succ s) = pointToNat pOut₁ ax / 2 ^ (Nat.succ s) := by
      -- Same high-plane argument as above, just swapping roles.
      apply Nat.eq_of_testBit_eq
      intro j
      have hx := Nat.testBit_div_two_pow (n := Nat.succ s) (x := pointToNat pOut₂ ax) (i := j)
      have hy := Nat.testBit_div_two_pow (n := Nat.succ s) (x := pointToNat pOut₁ ax) (i := j)
      have hj1 : Nat.succ s + j < m ax ∨ m ax ≤ Nat.succ s + j := lt_or_ge (Nat.succ s + j) (m ax)
      cases hj1 with
      | inl hjlt =>
          let tFin : Fin (m ax) := ⟨Nat.succ s + j, hjlt⟩
          have hPres₁ :
              pOut₂ ax tFin = pAcc ax tFin :=
            DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := ⟨k, BV.ofNat (k := k) i.succ⟩ :: lo.map Digits.zeroLike) (pAcc := pAcc)
              (pOut := pOut₂) (by simpa [A] using hDec₂') (j := ax) (t := tFin) (Nat.le_add_right _ _)
          have hPres₂ :
              pOut₁ ax tFin = pAcc ax tFin :=
            DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := ⟨k, w⟩ :: lo) (pAcc := pAcc)
              (pOut := pOut₁) (by simpa [A] using hDec₁) (j := ax) (t := tFin) (Nat.le_add_right _ _)
          have hxBit : Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) = pAcc ax tFin := by
            have hx' : Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) = pOut₂ ax tFin := by
              simpa [pointToNat, BV.ofNat] using
                congrArg (fun (v : BV (m ax)) => v tFin) (BV.ofNat_toNat (x := pOut₂ ax))
            simpa [hx', hPres₁]
          have hyBit : Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) = pAcc ax tFin := by
            have hy' : Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) = pOut₁ ax tFin := by
              simpa [pointToNat, BV.ofNat] using
                congrArg (fun (v : BV (m ax)) => v tFin) (BV.ofNat_toNat (x := pOut₁ ax))
            simpa [hy', hPres₂]
          have hxShift :
              Nat.testBit (pointToNat pOut₂ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx
          have hyShift :
              Nat.testBit (pointToNat pOut₁ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hy
          have hEqHi :
              Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) =
                Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := by
            calc
              Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) = pAcc ax tFin := hxBit
              _ = Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := by
                simpa using hyBit.symm
          calc
            Nat.testBit (pointToNat pOut₂ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := hxShift
            _ = Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := hEqHi
            _ = Nat.testBit (pointToNat pOut₁ ax / 2 ^ (Nat.succ s)) j := by
              simpa using hyShift.symm
      | inr hjge =>
          have hlt₁ : pointToNat pOut₂ ax < 2 ^ (m ax) := by
            simpa [pointToNat, Nat.shiftLeft_eq] using (BV.toNat_lt_shiftLeft_one (x := pOut₂ ax))
          have hlt₂ : pointToNat pOut₁ ax < 2 ^ (m ax) := by
            simpa [pointToNat, Nat.shiftLeft_eq] using (BV.toNat_lt_shiftLeft_one (x := pOut₁ ax))
          have hpow : 2 ^ (m ax) ≤ 2 ^ (Nat.succ s + j) :=
            Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hjge
          have hlt₁' : pointToNat pOut₂ ax < 2 ^ (Nat.succ s + j) := lt_of_lt_of_le hlt₁ hpow
          have hlt₂' : pointToNat pOut₁ ax < 2 ^ (Nat.succ s + j) := lt_of_lt_of_le hlt₂ hpow
          have hxBit : Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) = false :=
            Nat.testBit_eq_false_of_lt hlt₁'
          have hyBit : Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) = false :=
            Nat.testBit_eq_false_of_lt hlt₂'
          have hxShift :
              Nat.testBit (pointToNat pOut₂ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hx
          have hyShift :
              Nat.testBit (pointToNat pOut₁ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hy
          have hEqHi :
              Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) =
                Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := by
            calc
              Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) = false := hxBit
              _ = Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := by
                simpa using hyBit.symm
          calc
            Nat.testBit (pointToNat pOut₂ ax / 2 ^ (Nat.succ s)) j =
                Nat.testBit (pointToNat pOut₂ ax) (Nat.succ s + j) := hxShift
            _ = Nat.testBit (pointToNat pOut₁ ax) (Nat.succ s + j) := hEqHi
            _ = Nat.testBit (pointToNat pOut₁ ax / 2 ^ (Nat.succ s)) j := by
              simpa using hyShift.symm

    set a : Nat := pointToNat pOut₂ ax / 2 ^ (Nat.succ s)
    have hgLow : pointToNat pOut₂ ax = a * 2 ^ (Nat.succ s) + (2 ^ s - 1) := by
      have h := (Nat.div_add_mod' (pointToNat pOut₂ ax) (2 ^ (Nat.succ s))).symm
      simpa [a, hxmod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using h
    have hgHigh : pointToNat pOut₁ ax = a * 2 ^ (Nat.succ s) + 2 ^ s := by
      have h := (Nat.div_add_mod' (pointToNat pOut₁ ax) (2 ^ (Nat.succ s))).symm
      simpa [a, hdiv, hymod, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_assoc] using h

    have hStep : l1Dist pOut₂ pOut₁ = 1 :=
      lemma_5_3 (m := m) (g := ax) (s := Nat.succ s) (a := a) (hs := Nat.succ_pos s)
        (pLow := pOut₂) (pHigh := pOut₁) hgLow hgHigh (fun j hj => (hEqOther j hj).symm)
    simpa [l1Dist, Nat.dist_comm] using hStep

/-- Theorem 5.4 (Lattice continuity): successor indices decode to `L¹`-neighbors. -/
theorem theorem_5_4
    {n : Nat} {m : Exponents n}
    (ds ds' : Digits)
    (hSucc : Digits.succ ds = some ds')
    (pOut₁ pOut₂ : PointBV m)
    (hDec₁ : decodeDigits? (m := m) ds = some pOut₁)
    (hDec₂ : decodeDigits? (m := m) ds' = some pOut₂) :
    l1Dist pOut₁ pOut₂ = 1 := by
  classical
  -- Decompose the variable-radix successor into the common prefix, pivot digit, and overflow suffix.
  rcases succ_decomp_pivot (ds := ds) (ds' := ds') hSucc with
    ⟨hi, pivot, lo, hds, hds', hLoMax, hCarry⟩

  -- Peel off the common prefix `hi` from both decodes, then apply the seam lemma at the pivot level.
  have hPrefix :
      ∀ {s : Nat} {st : State n (activeAxes m (Nat.succ s))}
        {hi : Digits} {pivot : Digit} {lo : Digits}
        {pAcc pOut₁ pOut₂ : PointBV m},
        decodeFromLevel (m := m) (Nat.succ s) st (hi ++ pivot :: lo) pAcc = some pOut₁ →
        decodeFromLevel (m := m) (Nat.succ s) st
            (hi ++ (Digits.succDigit pivot).1 :: (lo.map Digits.zeroLike)) pAcc =
          some pOut₂ →
        (∀ d ∈ lo, BV.toNat d.2 = 2 ^ d.1 - 1) →
        (Digits.succDigit pivot).2 = false →
        l1Dist pOut₁ pOut₂ = 1 := by
    intro s st hi pivot lo pAcc pOut₁ pOut₂ hDec₁ hDec₂ hLoMax hCarry
    induction hi generalizing s st pAcc pOut₁ pOut₂ with
    | nil =>
        simpa using
          (seam_unit_step_of_decodeFromLevel_succDigit (m := m)
            (s := s) (st := st) (d := pivot) (lo := lo)
            (pAcc := pAcc) (pOut₁ := pOut₁) (pOut₂ := pOut₂)
            hDec₁ hDec₂ hCarry hLoMax)
    | cons d0 hi ih =>
        -- There is at least one more digit after the head, so `s` cannot be `0`.
        cases s with
        | zero =>
            -- Level `1` decoding only succeeds on a singleton digit stream.
            cases d0 with
            | mk k w =>
              -- `hi ++ pivot :: lo` is nonempty, so the decoder would return `none`.
              simp [decodeFromLevel] at hDec₁
        | succ s' =>
            -- Unfold one decode step (head digit is shared), obtaining the same next state/accumulator.
            cases d0 with
            | mk k w =>
              -- Name the active axes at this level.
              let A : List (Axis n) := activeAxes m (Nat.succ (Nat.succ s'))
              have hk : k = A.length := by
                by_contra hne
                have hNone :
                    decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st
                        (⟨k, w⟩ :: (hi ++ pivot :: lo)) pAcc =
                      none := by
                  simp [decodeFromLevel, A, hne]
                have : (none : Option (PointBV m)) = some pOut₁ := by
                  simpa [hNone] using hDec₁
                exact Option.noConfusion this
              -- Replace `k` by `A.length` so the width check becomes definitional.
              cases hk

              -- Rewrite the two decode hypotheses into the explicit `cons` form.
              have hDec₁' :
                  decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st
                      (⟨(activeAxes m (Nat.succ (Nat.succ s'))).length, w⟩ :: (hi ++ pivot :: lo)) pAcc =
                    some pOut₁ := by
                simpa [List.cons_append, A] using hDec₁
              have hDec₂' :
                  decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st
                      (⟨(activeAxes m (Nat.succ (Nat.succ s'))).length, w⟩ ::
                        (hi ++ (Digits.succDigit pivot).1 :: lo.map Digits.zeroLike)) pAcc =
                    some pOut₂ := by
                simpa [List.cons_append, A] using hDec₂

              -- Unfold `decodeFromLevel` at this head digit.
              -- Unfold one step for the first decode and extract the recursive call.
              -- The head digit is shared, so we can reuse the same next state/accumulator for both sides.
              -- Peel one decode step: both sides share the same head digit `d0`.
              have hStep₁ := hDec₁'
              have hStep₂ := hDec₂'
              -- Unfold the decoder one step at plane index `Nat.succ s'`.
              simp [decodeFromLevel] at hStep₁ hStep₂
              -- The only successful branch is where the embedding succeeds; extract it from `hStep₁`.
              cases hEmb :
                  Embed.embedState? (Aold := activeAxes m (Nat.succ (Nat.succ s')))
                    (Anew := activeAxes m (Nat.succ s'))
                    (stateUpdate (A := activeAxes m (Nat.succ (Nat.succ s'))) st w) with
              | none =>
                  -- In this branch the decoder returns `none`, contradicting `hStep₁`.
                  have : (none : Option (PointBV m)) = some pOut₁ := by
                    -- `hStep₁` is the unfolded decode equation.
                    simpa [hEmb] using hStep₁
                  exact Option.noConfusion this
              | some st' =>
                  -- In the successful branch, both equations reduce to the recursive calls with the same `st'` and accumulator.
                  set p1 : PointBV m :=
                    writePlane (activeAxes m (Nat.succ (Nat.succ s')))
                      (Tinv st.e st.dPos.val (BV.gc w)) pAcc (Nat.succ s')
                  have hStep₁' :
                      decodeFromLevel (m := m) (Nat.succ s') st' (hi ++ pivot :: lo) p1 = some pOut₁ := by
                    simpa [hEmb, p1] using hStep₁
                  have hStep₂' :
                      decodeFromLevel (m := m) (Nat.succ s') st'
                          (hi ++ (Digits.succDigit pivot).1 :: lo.map Digits.zeroLike) p1 =
                        some pOut₂ := by
                    simpa [hEmb, p1] using hStep₂
                  -- Now finish by applying the IH to the remaining prefix `hi`.
                  exact ih (s := s') (st := st')
                    (pAcc := p1) (pOut₁ := pOut₁) (pOut₂ := pOut₂)
                    (hDec₁ := hStep₁') (hDec₂ := hStep₂')

  -- Unfold the top-level decoder wrappers and feed the prefix lemma.
  -- Decode only succeeds when `mMax m > 0` and the initial state exists.
  cases hS : mMax m with
  | zero =>
      -- `decodeDigits?` at `mMax = 0` only succeeds on `[]`, but then `Digits.succ [] = none`.
      cases ds with
      | nil =>
          have : False := by
            -- `Digits.succ [] = none`.
            simpa [Digits.succ, Digits.succAux] using hSucc
          exact False.elim this
      | cons d ds =>
          have : (none : Option (PointBV m)) = some pOut₁ := by
            -- `decodeDigits?` at `mMax = 0` only returns `some` on `[]`.
            simpa [decodeDigits?, hS] using hDec₁
          exact Option.noConfusion this
  | succ s0 =>
      have hDec₁' := hDec₁
      have hDec₂' := hDec₂
      -- Peel off the outer `mMax`-match in `decodeDigits?` (we are in the `Nat.succ` branch).
      simp [decodeDigits?, hS] at hDec₁' hDec₂'

      cases hInit : initState? (n := n) (activeAxes m (mMax m)) with
      | none =>
          -- `decodeDigits?` is `none` in this branch, contradicting `hDec₁`.
          have : False := by
            simpa [hInit] using hDec₁'
          exact False.elim this
      | some st0 =>
          -- Reduce both decodes to the level-indexed form with accumulator `pointZero`.
          have hLvl₁0 :
              decodeFromLevel (m := m) (mMax m) st0 ds (pointZero (m := m)) = some pOut₁ := by
            simpa [hInit] using hDec₁'
          have hLvl₂0 :
              decodeFromLevel (m := m) (mMax m) st0 ds' (pointZero (m := m)) = some pOut₂ := by
            simpa [hInit] using hDec₂'

          -- Transport the common initial state and both decode equalities to level `Nat.succ s0`.
          have hS_succ : mMax m = Nat.succ s0 := by
            simpa [Nat.succ_eq_add_one] using hS
          let S : Nat → Type :=
            fun k =>
              {st : State n (activeAxes m k) //
                decodeFromLevel (m := m) k st ds (pointZero (m := m)) = some pOut₁ ∧
                  decodeFromLevel (m := m) k st ds' (pointZero (m := m)) = some pOut₂}
          have pack : S (mMax m) := ⟨st0, ⟨hLvl₁0, hLvl₂0⟩⟩
          have pack' : S (Nat.succ s0) := Eq.ndrec pack hS_succ

          -- Rewrite digit streams using the pivot decomposition and apply `hPrefix`.
          subst hds
          subst hds'
          exact hPrefix (s := s0) (st := pack'.1) (hi := hi) (pivot := pivot) (lo := lo)
            (pAcc := pointZero (m := m)) (pOut₁ := pOut₁) (pOut₂ := pOut₂)
            (by simpa using pack'.2.1) (by simpa using pack'.2.2) hLoMax hCarry

/-
TODO: Seam/unit-step lemma for Theorem 5.4.

This proof is being rebuilt in smaller lemmas; keep it commented so the project stays green.
-/
/-
private theorem seam_unit_step_of_decodeFromLevel_succDigit
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (d : Digit) (lo : Digits)
    (pAcc pOut₁ pOut₂ : PointBV m)
    (hDec₁ : decodeFromLevel (m := m) (Nat.succ s) st (d :: lo) pAcc = some pOut₁)
    (hDec₂ :
      decodeFromLevel (m := m) (Nat.succ s) st ((Digits.succDigit d).1 :: (lo.map Digits.zeroLike)) pAcc =
        some pOut₂)
    (hCarry : (Digits.succDigit d).2 = false)
    (hLoMax : ∀ d ∈ lo, BV.toNat d.2 = 2 ^ d.1 - 1) :
    l1Dist pOut₁ pOut₂ = 1 := by
  classical
  rcases d with ⟨kW, w⟩
  let A : List (Axis n) := activeAxes m (Nat.succ s)
  have hkW : kW = A.length := by
    by_contra hne
    have hNone : decodeFromLevel (m := m) (Nat.succ s) st (⟨kW, w⟩ :: lo) pAcc = none := by
      simp [decodeFromLevel, A, hne]
    have : (none : Option (PointBV m)) = some pOut₁ := by
      simpa [hNone] using hDec₁
    exact Option.noConfusion this
  cases hkW
  let k : Nat := A.length
  have hk : 0 < k := State.length_pos st
  let i : Nat := BV.toNat w

  have hCarryW : (Digits.succDigit ⟨k, w⟩).2 = false := by
    simpa [k, A] using hCarry
  have ht : tsb i < k := by
    simpa [i] using (Digits.succDigit_carry_false_imp_tsb_lt (d := ⟨k, w⟩) hCarryW)
  let t : Fin k := ⟨tsb i, ht⟩
  let r : Nat := st.dPos.val.succ
  let g : Fin k := ⟨(t.val + r) % k, Nat.mod_lt _ hk⟩
  let ax : Axis n := A.get g

  -- Normalize the successor head digit to `ofNat (toNat w).succ`.
  have hSuccHead :
      (Digits.succDigit ⟨k, w⟩).1 = ⟨k, BV.ofNat (k := k) i.succ⟩ := by
    simpa [i] using (Digits.succDigit_eq_ofNat_succ_of_carry_false (d := ⟨k, w⟩) hCarryW)
  have hDec₂' :
      decodeFromLevel (m := m) (Nat.succ s) st
          (⟨k, BV.ofNat (k := k) i.succ⟩ :: (lo.map Digits.zeroLike)) pAcc =
        some pOut₂ := by
    -- Rewrite the successor head digit, then reduce.
    -- `simp` doesn't always rewrite the whole head digit automatically, so we do it explicitly.
    simpa [hSuccHead] using (hDec₂ : decodeFromLevel (m := m) (Nat.succ s) st
      ((Digits.succDigit ⟨k, w⟩).1 :: (lo.map Digits.zeroLike)) pAcc = some pOut₂)
  have hwOfNat : BV.ofNat (k := k) i = w := by
    simpa [i] using (BV.ofNat_toNat (x := w))
  have hDec₁' :
      decodeFromLevel (m := m) (Nat.succ s) st (⟨k, BV.ofNat (k := k) i⟩ :: lo) pAcc =
        some pOut₁ := by
    simpa [hwOfNat] using hDec₁

  -- Plane XOR at the head level is a rotated one-hot at `tsb i`.
  have hXorPlaneRaw :
      BV.xor (packPlane A pOut₁ s) (packPlane A pOut₂ s) =
        BV.rotL (k := k) r (BV.oneHotFin t) := by
    simpa [A, k, i, r, t] using
      (DecodeHeadXor.packPlane_xor_decodeFromLevel_ofNat_succ_heads (m := m)
        (s := s) (st := st) (i := i)
        (rest₁ := lo) (rest₂ := lo.map Digits.zeroLike)
        (pAcc := pAcc) (pOut₁ := pOut₁) (pOut₂ := pOut₂)
        hDec₁' hDec₂' ht)
  have hRotOneHot : BV.rotL (k := k) r (BV.oneHotFin t) = BV.oneHotFin g := by
    simpa [g, r, t] using (BV.rotL_oneHotFin_eq_of_pos (k := k) hk r t)
  have hXorPlane :
      BV.xor (packPlane A pOut₁ s) (packPlane A pOut₂ s) = BV.oneHotFin g :=
    hXorPlaneRaw.trans hRotOneHot

  -- The seam axis is active at this level, so bit-plane `s` exists on it.
  have hAxMem : ax ∈ A := ListLemmas.get_mem (xs := A) g
  have hAxActive : Nat.succ s ≤ m ax := (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ s) (j := ax)).1 hAxMem |>.2
  have hsAx : s < m ax := Nat.lt_of_lt_of_le (Nat.lt_succ_self s) hAxActive

  -- Convenience: name the two head-plane bits on the seam axis.
  let b₁ : Bool := getBit (pOut₁ ax) s
  let b₂ : Bool := getBit (pOut₂ ax) s

  have hb₁ : b₁ = (packPlane A pOut₁ s) g := by
    -- `packPlane` at index `g` reads exactly the bit of axis `A.get g = ax` at plane `s`.
    simp [b₁, ax, packPlane, getBit, hsAx]
  have hb₂ : b₂ = (packPlane A pOut₂ s) g := by
    simp [b₂, ax, packPlane, getBit, hsAx]

  have hDiffPlane : BV.bxor b₁ b₂ = true := by
    have := congrArg (fun w => w g) hXorPlane
    -- evaluate `oneHot` at its hot index
    simpa [BV.xor, BV.oneHotFin, b₁, b₂, hb₁, hb₂] using this

  have hb₂_eq_not : b₂ = (!b₁) := by
    cases hb₁v : b₁ <;> cases hb₂v : b₂ <;> simp [BV.bxor, hb₁v, hb₂v] at hDiffPlane <;> simp [hb₁v, hb₂v]

  -- Build the two child states at this level.
  set st₁ : State n A := stateUpdate A st w with hst₁
  set st₂ : State n A := stateUpdate A st (BV.ofNat (k := k) i.succ) with hst₂

  -- `toNat (ofNat i.succ) = i.succ` since `succDigit` does not overflow.
  have hiSucc : i.succ < 2 ^ k := by
    -- `i.succ < base k = 2^k`
    have hlt : i.succ < Digits.base k := by
      -- specialize the generic lemma to our digit
      simpa [Digits.base, i] using
        (Digits.succDigit_carry_false_imp_toNat_succ_lt_base (d := ⟨k, w⟩) hCarryW)
    simpa [Digits.base, Nat.shiftLeft_eq] using hlt
  have hToNatSucc : BV.toNat (BV.ofNat (k := k) i.succ) = i.succ :=
    toNat_ofNat_eq_of_lt (k := k) (n := i.succ) hiSucc

  -- The entry corner bit of `st₂` on the seam axis agrees with the plane bit `b₁`.
  have hEntryBit : st₂.e g = b₁ := by
    -- Reduce both to rotated bits at the preimage index `t`.
    have hTinv :
        Tinv st.e st.dPos.val (BV.gc w) = BV.xor st.e (BV.rotL (k := k) r (BV.gc w)) := by
      -- `Tinv = rotL ⊕ e`, commute XOR.
      simpa [Tinv, r] using (BV.xor_comm (BV.rotL (k := k) r (BV.gc w)) st.e)
    have hst₂e : st₂.e = BV.xor st.e (BV.rotL (k := k) r (childEntry k i.succ)) := by
      -- Unfold `stateUpdate` at the successor word.
      simp [hst₂, stateUpdate, i, k, hToNatSucc, r, State.mk']
    have hRotEq :
        (BV.rotL (k := k) r (childEntry k i.succ)) g = (BV.rotL (k := k) r (BV.gc w)) g := by
      -- `rotL` at `g` is the original at `t`.
      have h1 : (BV.rotL (k := k) r (childEntry k i.succ)) g = (childEntry k i.succ) t := by
        simpa [g, t] using (rotL_apply_at_add_mod (k := k) hk r t (childEntry k i.succ))
      have h2 : (BV.rotL (k := k) r (BV.gc w)) g = (BV.gc w) t := by
        simpa [g, t] using (rotL_apply_at_add_mod (k := k) hk r t (BV.gc w))
      -- Compare at the preimage index using the `childEntry` lemma and `ofNat_toNat`.
      have hChild :
          (childEntry k i.succ) t = (BV.gc w) t := by
        have := childEntry_succ_get_tsb_eq_gc_get_tsb (k := k) hk i ht
        simpa [t, i, hwOfNat] using this
      exact h1.trans (hChild.trans h2.symm)

    -- Now evaluate `st₂.e` and the decoded plane bit `b₁`.
    have hPlane₁ : (packPlane A pOut₁ s) = Tinv st.e st.dPos.val (BV.gc w) := by
      -- Use the head-plane lemma with the normalized `ofNat (toNat w)` word, then rewrite back.
      have h :=
        (DecodeHead.packPlane_decodeFromLevel_head (m := m) (s := s) (st := st) (w := BV.ofNat (k := k) i)
          (rest := lo) (pAcc := pAcc) (pOut := pOut₁) hDec₁')
      simpa [A, k, hwOfNat] using h
    -- `b₁` is the `g`-component of the packed plane.
    have hb₁' : b₁ = (Tinv st.e st.dPos.val (BV.gc w)) g := by
      -- rewrite `b₁` into `packPlane` at index `g`, then use `hPlane₁`
      have : (packPlane A pOut₁ s) g = (Tinv st.e st.dPos.val (BV.gc w)) g := by
        simpa using congrArg (fun l => l g) hPlane₁
      -- relate `(packPlane ...) g` to `b₁`
      simpa [b₁, hb₁] using this

    -- Put everything together.
    -- `st₂.e g = st.e g XOR rotL(childEntry) g = st.e g XOR rotL(gc w) g = Tinv ... g = b₁`.
    calc
      st₂.e g
          = (BV.xor st.e (BV.rotL (k := k) r (childEntry k i.succ))) g := by simpa [hst₂e]
      _ = BV.bxor (st.e g) ((BV.rotL (k := k) r (childEntry k i.succ)) g) := by rfl
      _ = BV.bxor (st.e g) ((BV.rotL (k := k) r (BV.gc w)) g) := by simpa [hRotEq]
      _ = (BV.xor st.e (BV.rotL (k := k) r (BV.gc w))) g := by rfl
      _ = (Tinv st.e st.dPos.val (BV.gc w)) g := by simpa [hTinv]
      _ = b₁ := by simpa [hb₁'] using rfl

  -- Entry/exit corner glue gives the low-bit corner values along the seam axis.
  have hGlue : st₂.e = BV.xor (State.exitCorner st₁) (BV.oneHotFin g) := by
    -- Lemma 5.2, rewritten with `exitCorner`.
    have h :=
      lemma_5_2 (st := st) (w := w) ht
    -- `lemma_5_2` is exactly the `st₂.e` equation, but with the rotated one-hot.
    -- Rewrite the rotated one-hot to `oneHotFin g`, and the left state updates to `st₁/st₂`.
    have hRot : BV.rotL (k := k) r (BV.oneHotFin t) = BV.oneHotFin g := hRotOneHot
    -- `stateUpdate` shorthands
    simpa [hst₁, hst₂, State.exitCorner, hRot, i, k] using h

  have hExitBit : (State.exitCorner st₁) g = (!b₁) := by
    have := congrArg (fun w => w g) hGlue
    -- `xor` at the hot index flips the bit
    simpa [BV.xor, BV.oneHotFin, hEntryBit, Bool.bnot_eq_not] using this

  -- Low-bit values on the seam axis for the two output points.
  -- Below plane `s`, the all-max suffix decodes to `exitCorner st₁`, and the all-zero suffix decodes to `entryCorner st₂`.
  have hLowBits₁ : ∀ i0, i0 < s → getBit (pOut₁ ax) i0 = (State.exitCorner st₁) g := by
    intro i0 hi0
    cases s with
    | zero =>
        cases (Nat.not_lt_zero _ hi0)
    | succ s' =>
        -- Extract the recursive call and apply the suffix-corner lemma.
        have hDec₁Step : decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st (⟨k, w⟩ :: lo) pAcc = some pOut₁ := by
          simpa [A] using hDec₁
        -- Unfold one step to get the recursive decode for `lo`.
        let l : BV k := Tinv st.e st.dPos.val (BV.gc w)
        let p1 : PointBV m := writePlane A l pAcc (Nat.succ s')
        let stNext : State n A := stateUpdate (A := A) st w
        have hDec' : decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st (⟨k, w⟩ :: lo) pAcc = some pOut₁ := hDec₁Step
        simp [decodeFromLevel, A, l, p1, stNext] at hDec'
        split at hDec'
        · exact Option.noConfusion hDec'
        · rename_i stRec hEmb
          have hRec :
              decodeFromLevel (m := m) (Nat.succ s') stRec lo p1 = some pOut₁ := hDec'
          -- Build the `allMaxForDecode` predicate from the per-digit `toNat` hypothesis.
          have hAllMax : Digits.allMaxForDecode m (Nat.succ s') lo :=
            Digits.allMaxForDecode_of_decodeFromLevel_toNat_eq_two_pow_sub_one (m := m)
              (s := Nat.succ s') (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut₁) hRec hLoMax
          -- Apply the corner lemma at the recursive level.
          have hBit :=
            DecodeSuffix.getBit_decodeFromLevel_allMax_eq_exitCorner (m := m)
              (s := Nat.succ s') (st := stRec) (ds := lo) (pAcc := p1) (pOut := pOut₁) hAllMax hRec ax
              (ActiveAxes.mem_activeAxes_of_mem_activeAxes_succ (m := m) (s := Nat.succ s') (j := ax) hAxMem)
              i0 (Nat.lt_of_lt_of_le hi0 (Nat.le_succ _))
          -- Relate the exit corner across embedding.
          have hOld : A.Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ (Nat.succ s'))
          have hNew : (activeAxes m (Nat.succ s')).Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ s')
          have hExitEmb :
              State.exitCorner stRec = Embed.embedBV A (activeAxes m (Nat.succ s')) (State.exitCorner st₁) := by
            -- `st₁ = stateUpdate A st w` and `stNext = st₁`.
            have : stNext = st₁ := by simpa [stNext, hst₁]
            subst this
            simpa [Embed.embedState?_exitCorner_eq (Aold := A) (Anew := activeAxes m (Nat.succ s')) (hOld := hOld) (hNew := hNew)
              (st := st₁) (st' := stRec) hEmb]
          -- Evaluate `unpackPlane` on an old axis.
          have hAxNew : ax ∈ activeAxes m (Nat.succ s') :=
            ActiveAxes.mem_activeAxes_of_mem_activeAxes_succ (m := m) (s := Nat.succ s') (j := ax) hAxMem
          have hCorner :
              unpackPlane (activeAxes m (Nat.succ s')) (State.exitCorner stRec) ax =
                unpackPlane A (State.exitCorner st₁) ax := by
            simpa [hExitEmb] using
              (unpackPlane_embedBV_eq_of_mem (Aold := A) (Anew := activeAxes m (Nat.succ s')) (x := State.exitCorner st₁)
                (j := ax) hAxMem hAxNew)
          -- Convert `unpackPlane ... ax` to the `g` component using nodup.
          have hpos : pos? A ax = some g := by
            have hnd : A.Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ (Nat.succ s'))
            simpa [ax] using (Pos.pos?_get_of_nodup (xs := A) hnd g)
          -- finish
          simpa [unpackPlane, hpos] using hBit.trans hCorner

  have hLowBits₂ : ∀ i0, i0 < s → getBit (pOut₂ ax) i0 = st₂.e g := by
    intro i0 hi0
    cases s with
    | zero =>
        cases (Nat.not_lt_zero _ hi0)
    | succ s' =>
        -- As above, but for all-zero suffix and entry corner.
        have hDec₂Step :
            decodeFromLevel (m := m) (Nat.succ (Nat.succ s')) st (⟨k, BV.ofNat (k := k) i.succ⟩ :: lo.map Digits.zeroLike) pAcc =
              some pOut₂ := by
          simpa [A] using hDec₂'
        let l : BV k := Tinv st.e st.dPos.val (BV.gc (BV.ofNat (k := k) i.succ))
        let p1 : PointBV m := writePlane A l pAcc (Nat.succ s')
        let stNext : State n A := stateUpdate (A := A) st (BV.ofNat (k := k) i.succ)
        have hDec' := hDec₂Step
        simp [decodeFromLevel, A, l, p1, stNext] at hDec'
        split at hDec'
        · exact Option.noConfusion hDec'
        · rename_i stRec hEmb
          have hRec :
              decodeFromLevel (m := m) (Nat.succ s') stRec (lo.map Digits.zeroLike) p1 = some pOut₂ := hDec'
          have hZero : ∀ d ∈ (lo.map Digits.zeroLike), BV.toNat d.2 = 0 := by
            intro d hd
            rcases List.mem_map.mp hd with ⟨d0, hd0, rfl⟩
            simp [Digits.zeroLike, BV.toNat]
          have hAllZero : Digits.allZeroForDecode m (Nat.succ s') (lo.map Digits.zeroLike) :=
            Digits.allZeroForDecode_of_decodeFromLevel_toNat_eq_zero (m := m)
              (s := Nat.succ s') (st := stRec) (ds := lo.map Digits.zeroLike) (pAcc := p1) (pOut := pOut₂) hRec hZero
          have hBit :=
            DecodeSuffix.getBit_decodeFromLevel_allZero_eq_entryCorner (m := m)
              (s := Nat.succ s') (st := stRec) (ds := lo.map Digits.zeroLike) (pAcc := p1) (pOut := pOut₂) hAllZero hRec ax
              (ActiveAxes.mem_activeAxes_of_mem_activeAxes_succ (m := m) (s := Nat.succ s') (j := ax) hAxMem)
              i0 (Nat.lt_of_lt_of_le hi0 (Nat.le_succ _))
          have hEntryEmb :
              State.entryCorner stRec = Embed.embedBV A (activeAxes m (Nat.succ s')) (State.entryCorner st₂) := by
            have : stNext = st₂ := by simpa [stNext, hst₂]
            subst this
            simpa using (Embed.embedState?_entryCorner_eq (Aold := A) (Anew := activeAxes m (Nat.succ s')) (st := st₂) (st' := stRec) hEmb)
          have hAxNew : ax ∈ activeAxes m (Nat.succ s') :=
            ActiveAxes.mem_activeAxes_of_mem_activeAxes_succ (m := m) (s := Nat.succ s') (j := ax) hAxMem
          have hCorner :
              unpackPlane (activeAxes m (Nat.succ s')) (State.entryCorner stRec) ax =
                unpackPlane A (State.entryCorner st₂) ax := by
            simpa [hEntryEmb] using
              (unpackPlane_embedBV_eq_of_mem (Aold := A) (Anew := activeAxes m (Nat.succ s')) (x := State.entryCorner st₂)
                (j := ax) hAxMem hAxNew)
          have hpos : pos? A ax = some g := by
            have hnd : A.Nodup := ActiveAxes.nodup_activeAxes (m := m) (s := Nat.succ (Nat.succ s'))
            simpa [ax] using (Pos.pos?_get_of_nodup (xs := A) hnd g)
          simpa [State.entryCorner, unpackPlane, hpos] using hBit.trans hCorner

  -- Choose the low-half/high-half ordering by inspecting `b₁`.
  by_cases hb : b₁ = false
  · -- `pOut₁` has plane bit `0`, so it is the low-half endpoint.
    have hb2 : b₂ = true := by simpa [hb, hb₂_eq_not]
    -- Low-bit patterns on the seam axis:
    have hLowOnes : ∀ i0, i0 < s → getBit (pOut₁ ax) i0 = true := by
      intro i0 hi0
      have := hLowBits₁ i0 hi0
      -- `exitCorner` bit is `!b₁ = true`
      simpa [hExitBit, hb] using this
    have hHighZeros : ∀ i0, i0 < s → getBit (pOut₂ ax) i0 = false := by
      intro i0 hi0
      have := hLowBits₂ i0 hi0
      simpa [hEntryBit, hb] using this
    -- Convert these `getBit` facts into `testBit` facts for the natural coordinates.
    have hxmod : pointToNat pOut₁ ax % 2 ^ (Nat.succ s) = 2 ^ s - 1 := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < Nat.succ s
      · have hj' : j < m ax := lt_of_lt_of_le hj hAxActive
        have hx : Nat.testBit (pointToNat pOut₁ ax) j = getBit (pOut₁ ax) j :=
          testBit_pointToNat_eq_getBit (p := pOut₁) (j := ax) (i := j) hj'
        have hxlo : getBit (pOut₁ ax) j = decide (j < s) := by
          by_cases hjs : j < s
          · -- low bits are `true`
            have := hLowOnes j hjs
            simpa [decide_true, hjs] using this
          · have hjs' : j = s := Nat.eq_of_lt_succ_of_not_lt hj hjs
            -- plane `s` bit is `false` in this branch
            subst hjs'
            simpa [getBit, hsAx, hb, decide_false] using hb
        -- use `testBit_mod_two_pow` and `testBit_two_pow_sub_one`
        have : Nat.testBit (pointToNat pOut₁ ax % 2 ^ (Nat.succ s)) j =
            Nat.testBit (2 ^ s - 1) j := by
          simp [Nat.testBit_mod_two_pow, hj, hx, hxlo, Nat.testBit_two_pow_sub_one]
        exact this
      · -- above the modulus, both sides have `testBit = false`
        have : Nat.testBit (pointToNat pOut₁ ax % 2 ^ (Nat.succ s)) j = false := by
          simp [Nat.testBit_mod_two_pow, hj]
        have : Nat.testBit (2 ^ s - 1) j = false := by
          simp [Nat.testBit_two_pow_sub_one, hj]
        simpa [this]

    have hymod : pointToNat pOut₂ ax % 2 ^ (Nat.succ s) = 2 ^ s := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < Nat.succ s
      · have hj' : j < m ax := lt_of_lt_of_le hj hAxActive
        have hy : Nat.testBit (pointToNat pOut₂ ax) j = getBit (pOut₂ ax) j :=
          testBit_pointToNat_eq_getBit (p := pOut₂) (j := ax) (i := j) hj'
        have hylo : getBit (pOut₂ ax) j = decide (s = j) := by
          by_cases hjs : j < s
          · -- low bits are `false`
            have := hHighZeros j hjs
            have : decide (s = j) = false := by
              exact (decide_eq_false_iff_not).2 (Nat.ne_of_gt hjs)
            simpa [this] using this
          · have hjs' : j = s := Nat.eq_of_lt_succ_of_not_lt hj hjs
            subst hjs'
            -- plane `s` bit is `true` in this branch
            simpa [getBit, hsAx, hb2, decide_true] using hb2
        have : Nat.testBit (pointToNat pOut₂ ax % 2 ^ (Nat.succ s)) j =
            Nat.testBit (2 ^ s) j := by
          simp [Nat.testBit_mod_two_pow, hj, hy, hylo, Nat.testBit_two_pow]
        exact this
      ·
        have : Nat.testBit (pointToNat pOut₂ ax % 2 ^ (Nat.succ s)) j = false := by
          simp [Nat.testBit_mod_two_pow, hj]
        have : Nat.testBit (2 ^ s) j = false := by
          simp [Nat.testBit_two_pow, hj]
        simpa [this]

    -- Quotients agree because the two points match on all planes `≥ s+1` (decoder preserves those planes).
    have hdiv :
        pointToNat pOut₁ ax / 2 ^ (Nat.succ s) = pointToNat pOut₂ ax / 2 ^ (Nat.succ s) := by
      apply Nat.eq_of_testBit_eq
      intro j
      -- shift-right characterization of `testBit` under division by powers of two
      have hx := Nat.testBit_div_two_pow (n := Nat.succ s) (x := pointToNat pOut₁ ax) (i := j)
      have hy := Nat.testBit_div_two_pow (n := Nat.succ s) (x := pointToNat pOut₂ ax) (i := j)
      -- reduce to equality of the high bits
      have hj1 : s.succ + j < m ax ∨ m ax ≤ s.succ + j := lt_or_ge (s.succ + j) (m ax)
      cases hj1 with
      | inl hjlt =>
          let tFin : Fin (m ax) := ⟨s.succ + j, hjlt⟩
          have hPres₁ :
              pOut₁ ax tFin = pAcc ax tFin := by
            -- `decodeFromLevel (succ s)` preserves planes `≥ succ s`
            exact DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := ⟨k, w⟩ :: lo) (pAcc := pAcc) (pOut := pOut₁) (by simpa [A] using hDec₁)
              (j := ax) (t := tFin) (by decide : Nat.succ s ≤ tFin.val)
          have hPres₂ :
              pOut₂ ax tFin = pAcc ax tFin := by
            exact DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := (Digits.succDigit ⟨k, w⟩).1 :: lo.map Digits.zeroLike) (pAcc := pAcc)
              (pOut := pOut₂) (by simpa [A] using hDec₂) (j := ax) (t := tFin)
              (by decide : Nat.succ s ≤ tFin.val)
          have hEqBit : pOut₁ ax tFin = pOut₂ ax tFin := by
            simpa [hPres₁, hPres₂]
          -- translate to `testBit` via `ofNat_toNat`
          have hxbit : Nat.testBit (pointToNat pOut₁ ax) (s.succ + j) = pOut₁ ax tFin := by
            simpa [pointToNat, BV.ofNat] using congrArg (fun (v : BV (m ax)) => v tFin) (BV.ofNat_toNat (x := pOut₁ ax))
          have hybit : Nat.testBit (pointToNat pOut₂ ax) (s.succ + j) = pOut₂ ax tFin := by
            simpa [pointToNat, BV.ofNat] using congrArg (fun (v : BV (m ax)) => v tFin) (BV.ofNat_toNat (x := pOut₂ ax))
          -- assemble
          simpa [hx, hy, hxbit, hybit, hEqBit]
      | inr hjge =>
          -- Out-of-range bits are false because `pointToNat` values are `< 2^(m ax) ≤ 2^(s.succ+j)`.
          have hxlt : pointToNat pOut₁ ax < 2 ^ (m ax) := by
            simpa [pointToNat, Nat.shiftLeft_eq] using (BV.toNat_lt_shiftLeft_one (x := pOut₁ ax))
          have hylt : pointToNat pOut₂ ax < 2 ^ (m ax) := by
            simpa [pointToNat, Nat.shiftLeft_eq] using (BV.toNat_lt_shiftLeft_one (x := pOut₂ ax))
          have hpow : 2 ^ (m ax) ≤ 2 ^ (s.succ + j) :=
            Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hjge
          have hx' : pointToNat pOut₁ ax < 2 ^ (s.succ + j) := lt_of_lt_of_le hxlt hpow
          have hy' : pointToNat pOut₂ ax < 2 ^ (s.succ + j) := lt_of_lt_of_le hylt hpow
          have hxbit : Nat.testBit (pointToNat pOut₁ ax) (s.succ + j) = false :=
            Nat.testBit_eq_false_of_lt hx'
          have hybit : Nat.testBit (pointToNat pOut₂ ax) (s.succ + j) = false :=
            Nat.testBit_eq_false_of_lt hy'
          simpa [hx, hy, hxbit, hybit]

    -- Now the distance on the seam axis is exactly the dyadic boundary unit jump.
    have hDistAx : Nat.dist (pointToNat pOut₁ ax) (pointToNat pOut₂ ax) = 1 := by
      -- rewrite both coordinates in quotient/mod form with the shared quotient
      set a : Nat := pointToNat pOut₁ ax / 2 ^ (Nat.succ s)
      have hx : pointToNat pOut₁ ax = a * 2 ^ (Nat.succ s) + (2 ^ s - 1) := by
        have := (Nat.div_add_mod' (pointToNat pOut₁ ax) (2 ^ (Nat.succ s))).symm
        -- `2^(s+1) > 0`, so this is the usual division algorithm.
        simpa [a, hxmod, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      have hy : pointToNat pOut₂ ax = a * 2 ^ (Nat.succ s) + 2 ^ s := by
        have := (Nat.div_add_mod' (pointToNat pOut₂ ax) (2 ^ (Nat.succ s))).symm
        -- rewrite the quotient using `hdiv`, and the remainder using `hymod`.
        simpa [a, hdiv, hymod, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
      -- apply the dyadic boundary distance lemma
      -- note: `Nat.succ s > 0`
      have := dyadic_half_boundary_dist_one a (Nat.succ s) (Nat.succ_pos s)
      -- rewrite endpoints into the `hx`/`hy` form
      simpa [hx, hy, Nat.sub_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

    -- Finish the L¹-distance by summing over axes.
    have hEqOther : ∀ j : Axis n, j ≠ ax → pointToNat pOut₁ j = pointToNat pOut₂ j := by
      intro j hj
      -- Planes `≥ s+1` are preserved from `pAcc`, so high bits match.
      -- At plane `s`, only axis `ax` differs (the plane XOR is one-hot at `g`).
      -- Below plane `s`, the suffix-corner labels differ only on `ax`.
      -- For the L¹ computation we only need equality of the whole `BV` coordinates.
      -- We prove it pointwise by splitting on the bit index.
      have hEqBV : pOut₁ j = pOut₂ j := by
        funext tFin
        by_cases htge : Nat.succ s ≤ tFin.val
        · -- preserved by decoding
          have hPres₁ :=
            DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := ⟨k, w⟩ :: lo) (pAcc := pAcc) (pOut := pOut₁) (by simpa [A] using hDec₁)
              j tFin htge
          have hPres₂ :=
            DecodePlanes.decodeFromLevel_preserves_ge (m := m)
              (s := Nat.succ s) (st := st) (ds := (Digits.succDigit ⟨k, w⟩).1 :: lo.map Digits.zeroLike) (pAcc := pAcc)
              (pOut := pOut₂) (by simpa [A] using hDec₂) j tFin htge
          simpa [hPres₁, hPres₂]
        · have htlt : tFin.val < Nat.succ s := Nat.lt_of_not_ge htge
          -- At planes `< s+1`, `j ≠ ax` implies the written/decoded bits agree.
          -- We only need the bit at plane `tFin.val`; handle `tFin.val = s` vs `< s`.
          have ht' : tFin.val = s ∨ tFin.val < s := by
            exact eq_or_lt_of_le (Nat.lt_succ_iff.mp htlt)
          cases ht' with
          | inl hEqPlane =>
              -- Plane `s`: use the packed plane XOR.
              subst hEqPlane
              by_cases hjA : j ∈ A
              · rcases Pos.pos?_some_of_mem (xs := A) (a := j) hjA with ⟨tj, htj⟩
                have hget : A.get tj = j :=
                  Pos.get_of_pos?_some (xs := A) (a := j) (i := tj) htj
                have htjNe : tj ≠ g := by
                  intro hEq
                  apply hj
                  -- `j = A.get tj = A.get g = ax`
                  have : j = ax := by simpa [ax, hEq] using hget.symm
                  simpa [this]
                have hbitXor :=
                  congrArg (fun l => l tj) hXorPlane
                have honeHotFalse : BV.oneHotFin g tj = false := by
                  simp [BV.oneHotFin, htjNe]
                -- `bxor` is false, so the two bits are equal.
                have : (packPlane A pOut₁ s) tj = (packPlane A pOut₂ s) tj := by
                  -- expand the xor bit and use a truth table
                  have : BV.bxor ((packPlane A pOut₁ s) tj) ((packPlane A pOut₂ s) tj) = false := by
                    simpa [BV.xor, honeHotFalse] using hbitXor
                  cases h1 : (packPlane A pOut₁ s) tj <;> cases h2 : (packPlane A pOut₂ s) tj <;>
                    simp [BV.bxor, h1, h2] at this <;> simp [h1, h2]
                -- translate to the point bit using `hget`
                have htBit : getBit (pOut₁ j) s = getBit (pOut₂ j) s := by
                  -- `packPlane` reads `getBit` from the corresponding axis
                  have h₁ : (packPlane A pOut₁ s) tj = getBit (pOut₁ j) s := by
                    simpa [packPlane, hget] using rfl
                  have h₂ : (packPlane A pOut₂ s) tj = getBit (pOut₂ j) s := by
                    simpa [packPlane, hget] using rfl
                  simpa [h₁, h₂] using this
                -- now `tFin.val = s`
                simpa [getBit, tFin.isLt, Nat.lt_of_lt_of_le (Nat.lt_succ_self s) (by
                  -- `j ∈ A` implies `s < m j`
                  have hs : Nat.succ s ≤ m j :=
                    (ActiveAxes.mem_activeAxes_iff (m := m) (s := Nat.succ s) (j := j)).1 hjA |>.2
                  exact hs)] using htBit
              · -- inactive at this plane: `writePlane` does not touch it, so both are preserved from `pAcc`.
                have hPres₁ :=
                  DecodeHeadUpper.decodeFromLevel_eq_writePlane_on_ge (m := m) (s := s) (st := st) (w := w) (rest := lo)
                    (pAcc := pAcc) (pOut := pOut₁) (by simpa [A] using hDec₁) j tFin (Nat.le_refl _)
                have hPres₂ :=
                  DecodeHeadUpper.decodeFromLevel_eq_writePlane_on_ge (m := m) (s := s) (st := st) (w := (Digits.succDigit ⟨k, w⟩).1.2) (rest := lo.map Digits.zeroLike)
                    (pAcc := pAcc) (pOut := pOut₂) (by simpa [A] using hDec₂) j tFin (Nat.le_refl _)
                -- Both sides are the same `pAcc` bit because `j` is not written at plane `s`.
                simpa using hPres₁.trans hPres₂.symm
          | inr hLtPlane =>
              -- Below plane `s`: both points decode to the same corner bit for `j ≠ ax`.
              -- (The exit/entry corners differ only on `ax`).
              -- We use the low-bit corner lemmas above; they already give constants on `ax`,
              -- and for `j ≠ ax` the constants agree because `st₂.e = exitCorner st₁ XOR oneHot g`.
              have hjAx : j ≠ ax := hj
              -- Compare the two corner labels at axis `j`.
              have hCornerEq :
                  unpackPlane A (State.exitCorner st₁) j = unpackPlane A (State.entryCorner st₂) j := by
                -- Evaluate `st₂.e = exitCorner st₁ XOR oneHot g` at axis `j`.
                have hpos : pos? A j = none ∨ ∃ tj, pos? A j = some tj := by
                  cases h : pos? A j with
                  | none => exact Or.inl h
                  | some tj => exact Or.inr ⟨tj, h⟩
                -- Use `unpackPlane_xor` and `oneHot` behavior to show the bit is unchanged for `j ≠ ax`.
                -- We only need this at the Bool level, so case split on membership.
                by_cases hjA : j ∈ A
                · -- `j` is in `A`: its index is some `tj`, and `tj ≠ g` because `j ≠ ax`.
                  rcases Pos.pos?_some_of_mem (xs := A) (a := j) hjA with ⟨tj, htj⟩
                  have hget : A.get tj = j :=
                    Pos.get_of_pos?_some (xs := A) (a := j) (i := tj) htj
                  have htjNe : tj ≠ g := by
                    intro hEq
                    apply hjAx
                    -- `j = A.get tj = A.get g = ax`
                    have : j = ax := by simpa [ax, hEq] using hget.symm
                    simpa [this]
                  have honeHot : (BV.oneHotFin g) tj = false := by
                    simp [BV.oneHotFin, htjNe]
                  -- From `hGlue` we know `entryCorner st₂ = exitCorner st₁ XOR oneHot`.
                  have hAt : unpackPlane A st₂.e j = unpackPlane A (State.exitCorner st₁) j := by
                    have hEq := congrArg (fun l => l tj) hGlue
                    -- unpackPlane at `j` is the `tj` component.
                    have hL : unpackPlane A st₂.e j = st₂.e tj := by simp [unpackPlane, htj]
                    have hR : unpackPlane A (State.exitCorner st₁) j = (State.exitCorner st₁) tj := by simp [unpackPlane, htj]
                    have hX : st₂.e tj = (State.exitCorner st₁) tj := by
                      -- bxor with `false` does nothing
                      simpa [BV.xor, honeHot, BV.bxor] using hEq
                    simpa [hL, hR] using hX
                  simpa [State.entryCorner] using hAt.symm
                · -- if `j ∉ A`, all these `unpackPlane` values are `false`
                  have hExit : unpackPlane A (State.exitCorner st₁) j = false := by
                    exact unpackPlane_oneHotFin_eq_false_of_not_mem (A := A) (g := g) (j := j) hjA
                  have hEnt : unpackPlane A (State.entryCorner st₂) j = false := by
                    -- `entryCorner st₂ = st₂.e`, and `unpackPlane` returns `false` when `j ∉ A`.
                    exact unpackPlane_oneHotFin_eq_false_of_not_mem (A := A) (g := g) (j := j) hjA
                  simpa [hExit, hEnt]

              -- Now apply the low-bit characterization at axis `j`.
              -- Since both sides are equal, the bits agree.
              -- (We only need the bit at `tFin.val < s`).
              have hjBit₁ : getBit (pOut₁ j) tFin.val = unpackPlane A (State.exitCorner st₁) j := by
                -- Use the already-proved low-bit formula on `ax`? (Not available for general `j`).
                -- Fall back to definitional extensionality: bits below `s` are determined by the suffix corner.
                -- This suffices because `hCornerEq` shows the two corner bits coincide.
                -- For non-seam axes we can keep the proof lightweight using `getBit_decodeFromLevel_allMax_eq_exitCorner`
                -- exactly as for `ax` above.
                -- (We reuse the extracted recursion proof inside `hLowBits₁` by calling it with `j`.)
                -- To avoid duplicating the whole extraction, use the `ax`-specialized lemma and `hCornerEq`.
                -- For now, reduce to the already-established constant corner equality.
                -- (Since `tFin.val < s` and `j ≠ ax`, both points read the same corner bit.)
                -- This is a direct consequence of `hCornerEq`.
                simpa using hCornerEq.symm
              -- The previous line is only a placeholder to keep the proof concise; the actual equality is supplied by `hCornerEq`.
              -- Close the branch by rewriting with `hjBit₁`.
              -- Since we never used `hjBit₁` explicitly, finish by reflexivity on the preserved bit.
              simpa

      -- finally `toNat` equality
      simpa [pointToNat] using congrArg BV.toNat hEqBV

    -- Combine the `Nat.dist` on `ax` with equalities elsewhere.
    exact (lemma_5_3 (m := m) (g := ax) (s := Nat.succ s) (a := pointToNat pOut₁ ax / 2 ^ (Nat.succ s))
      (pLow := pOut₁) (pHigh := pOut₂) (hs := Nat.succ_pos s)
      (hgLow := by
        -- derived from `hx` above
        -- (we reuse `hx` by unfolding `a`)
        simpa [pointToNat] using rfl)
      (hgHigh := by simpa [pointToNat] using rfl)
      (hEq := fun j hj => hEqOther j hj))

  · -- If `b₁ = true`, swap the roles of `pOut₁` and `pOut₂`.
    have hb' : b₂ = false := by simpa [hb, hb₂_eq_not]
    -- Symmetry of `l1Dist`.
    have hs : l1Dist pOut₂ pOut₁ = 1 := by
      -- Apply the previous branch with swapped points by rewriting `hb' : b₂ = false`.
      -- Since `l1Dist` is symmetric, it suffices.
      simpa [l1Dist, Nat.dist_comm, Fintype.sum_comm] using (seam_unit_step_of_decodeFromLevel_succDigit
        (s := s) (st := st) (d := ⟨k, BV.ofNat (k := k) i.succ⟩) (lo := lo.map Digits.zeroLike)
        (pAcc := pAcc) (pOut₁ := pOut₂) (pOut₂ := pOut₁) (hDec₁ := hDec₂') (hDec₂ := by
          -- successor of successor is irrelevant; this branch is not used
          simpa using hDec₁) (hCarry := by
          -- no carry after swap is not needed here
          simpa using hCarryW) (hLoMax := by
          intro d hd
          rcases List.mem_map.mp hd with ⟨d0, hd0, rfl⟩
          simp [Digits.zeroLike]))
    -- Use symmetry to conclude the original order.
    simpa [l1Dist, Nat.dist_comm] using hs
-/

end DiscreteProof

end AnisoHilbert
