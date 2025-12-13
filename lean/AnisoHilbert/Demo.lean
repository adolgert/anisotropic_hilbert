import AnisoHilbert.Representation
import AnisoHilbert.Step

open AnisoHilbert

namespace AnisoHilbert.Demo

/-- Example: n = 2, exponents (x=2, y=1). Axis 0 is x, axis 1 is y. -/
def mExample : Exponents 2
| ⟨0, _⟩ => 2
| ⟨1, _⟩ => 1

/-- Convenience: convert `Fin` lists to underlying `Nat` ids for printing. -/
def axisIds {n : Nat} (xs : List (Axis n)) : List Nat :=
  xs.map (fun j => j.val)

#eval axisIds (activeAxes mExample 2)  -- expected: [0]
#eval axisIds (activeAxes mExample 1)  -- expected (by key): [1, 0]

/-- Convert an `Option (Fin k)` to an `Option Nat` for printing. -/
def finOptVal {k : Nat} : Option (Fin k) → Option Nat
| none => none
| some i => some i.val

#eval finOptVal (pos? (activeAxes mExample 1) ⟨0, by decide⟩)  -- x's position in [1,0] is 1

/-- Make a tiny point: x = 1 (01₂ with 2 bits), y = 1 (1₂ with 1 bit). -/
def x01 : BV 2
| ⟨0, _⟩ => true   -- bit 0
| ⟨1, _⟩ => false  -- bit 1

def y1 : BV 1
| ⟨0, _⟩ => true

def pExample : PointBV mExample
| ⟨0, _⟩ => x01
| ⟨1, _⟩ => y1

/-- Convert a BV to a Bool list (LSB-first) for printing. -/
def bvToList {k : Nat} (v : BV k) : List Bool :=
  (List.finRange k).map (fun i => v i)

-- At level s = 2, only axis 0 is active. Packing bit-plane i=1 yields [false].
#eval bvToList (packPlane (activeAxes mExample 2) pExample 1)

end AnisoHilbert.Demo

namespace AnisoHilbert.DemoStep

open AnisoHilbert

/-- A square 2D example: both axes have precision 3 (so A = [0,1] at every level). -/
def m33 : Exponents 2
| ⟨0, _⟩ => 3
| ⟨1, _⟩ => 3

def A33 : List (Axis 2) := activeAxes m33 1

/-- Point p = [5,6] (binary 101 and 110) from Hamilton's worked example figure. -/
def p56 : PointBV m33
| ⟨0, _⟩ => BV.ofNat (k := 3) 5
| ⟨1, _⟩ => BV.ofNat (k := 3) 6

/-- Initial HilbertIndex state corresponds to (e,d) = (0,0) in Algorithm 2. -/
def st0 : State 2 A33 :=
  State.mk' (A := A33) (e := BV.zero) (dPos := ⟨0, by decide⟩)

/-- One step at bit-plane i=2 (the MSB for m=3). -/
def step2 := hilbertStep (A := A33) st0 p56 2

-- Print the extracted digit `w` (as a Nat) and the updated local direction index and entry mask.
#eval BV.toNat step2.w
#eval step2.stNext.dPos.val
#eval BV.toNat step2.stNext.e

-- Optionally also inspect the packed plane `l` and transformed word `lT`.
#eval BV.toNat step2.l
#eval BV.toNat step2.lT

end AnisoHilbert.DemoStep
