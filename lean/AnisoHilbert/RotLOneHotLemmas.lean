import Mathlib

import AnisoHilbert.GrayAdjacencyLemmas

namespace AnisoHilbert

namespace BV

/-- Rotating a one-hot word shifts the hot index by `r` (mod `k`). -/
theorem rotL_oneHotFin_eq {k : Nat} (r : Nat) (g : Fin k) :
    rotL r (oneHotFin g)
      =
    oneHotFin ⟨(g.val + r) % k, by
      cases k with
      | zero => exact (Fin.elim0 g)
      | succ k' => exact Nat.mod_lt _ (Nat.succ_pos k')⟩ := by
  cases k with
  | zero =>
      exact (Fin.elim0 g)
  | succ k' =>
      let n : Nat := Nat.succ k'
      have hn : 0 < n := Nat.succ_pos k'
      let s : Nat := n - (r % n)
      let g' : Fin n := ⟨(g.val + r) % n, Nat.mod_lt _ hn⟩
      -- Reduce to the same explicit witness as in `g'`.
      have hg' : (⟨(g.val + r) % n, Nat.mod_lt _ hn⟩ : Fin n) = g' := rfl
      -- Now prove the rotated word is that one-hot.
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

/-- Variant of `rotL_oneHotFin_eq` using an explicit `0 < k` proof for the modulus bound. -/
theorem rotL_oneHotFin_eq_of_pos {k : Nat} (hk : 0 < k) (r : Nat) (g : Fin k) :
    rotL r (oneHotFin g) = oneHotFin ⟨(g.val + r) % k, Nat.mod_lt _ hk⟩ := by
  cases k with
  | zero =>
      cases (Nat.not_lt_zero 0 hk)
  | succ k' =>
      have h := rotL_oneHotFin_eq (k := Nat.succ k') (r := r) g
      -- Align the proof field of the `Fin` witness.
      have hIdx :
          (⟨(g.val + r) % Nat.succ k', Nat.mod_lt _ (Nat.succ_pos k')⟩ : Fin (Nat.succ k')) =
            ⟨(g.val + r) % Nat.succ k', Nat.mod_lt _ hk⟩ := by
        apply Fin.ext
        rfl
      simpa [hIdx] using h

/-- Rotating a one-hot word is still one-hot (explicitly: the hot index shifts by `r`). -/
theorem rotL_oneHotFin {k : Nat} (r : Nat) (g : Fin k) :
    ∃ g' : Fin k, rotL r (oneHotFin g) = oneHotFin g' := by
  refine ⟨⟨(g.val + r) % k, ?_⟩, ?_⟩
  · cases k with
    | zero => exact (Fin.elim0 g)
    | succ k' => exact Nat.mod_lt _ (Nat.succ_pos k')
  · simpa using (rotL_oneHotFin_eq (k := k) (r := r) g)

end BV

end AnisoHilbert
