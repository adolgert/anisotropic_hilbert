import AnisoHilbert.DecodeHeadPlaneLemmas
import AnisoHilbert.AdjacencyLemmas
import AnisoHilbert.GrayAdjacencyLemmas

namespace AnisoHilbert

/-!
A small “bridge lemma” for the seam argument.

At a fixed level `succ s`, if two decodes succeed (possibly with different
suffix digit streams) then the XOR-difference between the *packed* plane `s`
of their output points is exactly the rotated XOR-difference of the Gray-coded
head digits.

This is the conceptual step:

* `DecodeHead.packPlane_decodeFromLevel_head` identifies the plane written at
  this level as `Tinv st.e st.dPos.val (gc w)`.
* `BV.xor_Tinv` shows that applying `Tinv` to both sides cancels the `e`-XOR
  and rotates XOR-differences by `rotL (d+1)`.

A later lemma will specialize this further using the fact that consecutive Gray
codes differ in exactly one bit.
-/

namespace DecodeHeadXor

open BV
open DecodeHead

/--
If decoding from level `succ s` succeeds on head digits `w₁` and `w₂` (with any
suffixes), then the XOR-difference of the resulting packed plane `s` is the
rotated XOR-difference of the Gray codes of those head digits.

This lemma is deliberately agnostic about *which* bit differs; that comes from
Gray-code adjacency.
-/
theorem packPlane_xor_decodeFromLevel_heads
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (w₁ w₂ : BV (activeAxes m (Nat.succ s)).length)
    (rest₁ rest₂ : Digits)
    (pAcc pOut₁ pOut₂ : PointBV m)
    (hDec₁ :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w₁⟩ :: rest₁) pAcc = some pOut₁)
    (hDec₂ :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length, w₂⟩ :: rest₂) pAcc = some pOut₂) :
    xor (packPlane (activeAxes m (Nat.succ s)) pOut₁ s)
        (packPlane (activeAxes m (Nat.succ s)) pOut₂ s)
      =
    rotL (st.dPos.val.succ) (xor (gc w₁) (gc w₂)) := by
  -- Identify each packed plane with a `Tinv … (gc w)` using the head-plane lemma.
  have hP₁ :
      packPlane (activeAxes m (Nat.succ s)) pOut₁ s =
        Tinv st.e st.dPos.val (gc w₁) :=
    DecodeHead.packPlane_decodeFromLevel_head (m := m)
      (s := s) (st := st) (w := w₁) (rest := rest₁)
      (pAcc := pAcc) (pOut := pOut₁) hDec₁

  have hP₂ :
      packPlane (activeAxes m (Nat.succ s)) pOut₂ s =
        Tinv st.e st.dPos.val (gc w₂) :=
    DecodeHead.packPlane_decodeFromLevel_head (m := m)
      (s := s) (st := st) (w := w₂) (rest := rest₂)
      (pAcc := pAcc) (pOut := pOut₂) hDec₂

  -- Turn the goal into a pure `Tinv`-XOR computation.
  calc
    xor (packPlane (activeAxes m (Nat.succ s)) pOut₁ s)
        (packPlane (activeAxes m (Nat.succ s)) pOut₂ s)
        = xor (Tinv st.e st.dPos.val (gc w₁)) (Tinv st.e st.dPos.val (gc w₂)) := by
            simp [hP₁, hP₂]
    _ = rotL (st.dPos.val.succ) (xor (gc w₁) (gc w₂)) := by
            simpa using (BV.xor_Tinv (e := st.e) (d := st.dPos.val) (x := gc w₁) (y := gc w₂))

theorem packPlane_xor_decodeFromLevel_ofNat_succ_heads
    {n : Nat} {m : Exponents n}
    (s : Nat)
    (st : State n (activeAxes m (Nat.succ s)))
    (i : Nat)
    (rest₁ rest₂ : Digits)
    (pAcc pOut₁ pOut₂ : PointBV m)
    (hDec₁ :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length,
          BV.ofNat (k := (activeAxes m (Nat.succ s)).length) i⟩ :: rest₁) pAcc = some pOut₁)
    (hDec₂ :
      decodeFromLevel (m := m) (Nat.succ s) st
        (⟨(activeAxes m (Nat.succ s)).length,
          BV.ofNat (k := (activeAxes m (Nat.succ s)).length) i.succ⟩ :: rest₂) pAcc = some pOut₂)
    (ht : tsb i < (activeAxes m (Nat.succ s)).length) :
    xor (packPlane (activeAxes m (Nat.succ s)) pOut₁ s)
        (packPlane (activeAxes m (Nat.succ s)) pOut₂ s)
      =
    rotL (st.dPos.val.succ) (oneHotFin ⟨tsb i, ht⟩) := by
  have h :=
    packPlane_xor_decodeFromLevel_heads (m := m)
      (s := s) (st := st)
      (w₁ := BV.ofNat (k := (activeAxes m (Nat.succ s)).length) i)
      (w₂ := BV.ofNat (k := (activeAxes m (Nat.succ s)).length) i.succ)
      (rest₁ := rest₁) (rest₂ := rest₂)
      (pAcc := pAcc) (pOut₁ := pOut₁) (pOut₂ := pOut₂)
      hDec₁ hDec₂

  have hgc :
      xor (gc (ofNat (k := (activeAxes m (Nat.succ s)).length) i))
          (gc (ofNat (k := (activeAxes m (Nat.succ s)).length) i.succ))
        =
      oneHotFin ⟨tsb i, ht⟩ := by
    simpa using
      (xor_gc_ofNat_succ_eq_oneHotFin (k := (activeAxes m (Nat.succ s)).length) i ht)

  simpa [hgc] using h

end DecodeHeadXor

end AnisoHilbert
