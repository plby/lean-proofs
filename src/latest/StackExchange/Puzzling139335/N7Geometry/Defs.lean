import StackExchange.Puzzling139335.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The normalized seven-incidence placements

All maps below are explicit functions on the actual Euclidean plane. The
subsequent source bounds follow from square containment of these maps.
-/

namespace Puzzling139335.N7Geometry

noncomputable section

/-- Cosine of thirty degrees. -/
def c : ℝ := Real.sqrt 3 / 2

/-- The horizontal coordinate of the third intrinsic support point. -/
def u : ℝ := 1 - c

/-- Horizontal reflection taking the lower outer piece to the upper one. -/
def Q (p : Plane) : Plane := !₂[p 0, 1 - p 1]

/-- The normalized third placement, sending the source side pair to the right side. -/
def T (p : Plane) : Plane :=
  !₂[1 / 2 + p 0 / 2 + c * p 1, u + c * p 0 - p 1 / 2]

/-- First possible placement of the singleton corner piece. -/
def Uplus (p : Plane) : Plane :=
  !₂[1 / 2 + p 0 / 2 - c * p 1, u + c * p 0 + p 1 / 2]

/-- The other singleton placement exchanges the two target coordinates. -/
def Uminus (p : Plane) : Plane :=
  !₂[u + c * p 0 + p 1 / 2, 1 / 2 + p 0 / 2 - c * p 1]

/-- The square-side point missed by all normalized placements. -/
def leftMidpoint : Plane := !₂[0, (1 / 2 : ℝ)]

@[simp] theorem leftMidpoint_zero : leftMidpoint 0 = 0 := rfl
@[simp] theorem leftMidpoint_one : leftMidpoint 1 = (1 / 2 : ℝ) := rfl

theorem leftMidpoint_mem_unitSquare : leftMidpoint ∈ unitSquare := by
  norm_num [leftMidpoint, unitSquare]

end

end Puzzling139335.N7Geometry
