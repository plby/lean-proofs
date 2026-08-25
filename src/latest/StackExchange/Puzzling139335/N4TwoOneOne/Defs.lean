import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.ThreeCorners.Rays
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Coordinates for the reflected-singleton degree-(2,1,1,0) case

The source owns the bottom two corners. The singleton images use the same
upper source corner and occupy the top right and top left corners. The maps
below are actual maps of the Euclidean plane, not assumptions about hull
angles or projected boundary lengths.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

noncomputable section

/-- Projection onto the outward normal of the incoming source-corner face. -/
def eCoord (θ : ℝ) (p : Plane) : ℝ := Real.cos θ * p 0 + Real.sin θ * p 1

/-- Projection onto the outward normal of the outgoing source-corner face. -/
def fCoord (θ : ℝ) (p : Plane) : ℝ := -Real.sin θ * p 0 + Real.cos θ * p 1

/-- The right singleton placement in the normalized orientation. -/
def rightMap (θ u v : ℝ) (p : Plane) : Plane :=
  !₂[1 - u + eCoord θ p, 1 - v + fCoord θ p]

/-- Its reflection in the vertical square midline. -/
def leftMap (θ u v : ℝ) (p : Plane) : Plane :=
  !₂[u - eCoord θ p, 1 - v + fCoord θ p]

/-- The common intrinsic corner sent to the upper square corners. -/
def sourceCorner (θ u v : ℝ) : Plane :=
  !₂[u * Real.cos θ - v * Real.sin θ,
      u * Real.sin θ + v * Real.cos θ]

/-- Endpoint of the actual incoming source arm of length `R`. -/
def incomingEnd (θ u v R : ℝ) : Plane :=
  !₂[(sourceCorner θ u v) 0 + R * Real.sin θ,
      (sourceCorner θ u v) 1 - R * Real.cos θ]

/-- Endpoint of the actual outgoing source arm of length `T`. -/
def outgoingEnd (θ u v T : ℝ) : Plane :=
  !₂[(sourceCorner θ u v) 0 - T * Real.cos θ,
      (sourceCorner θ u v) 1 - T * Real.sin θ]

@[simp] theorem rightMap_zero_coord (θ u v : ℝ) (p : Plane) :
    rightMap θ u v p 0 = 1 - u + eCoord θ p := rfl

@[simp] theorem rightMap_one_coord (θ u v : ℝ) (p : Plane) :
    rightMap θ u v p 1 = 1 - v + fCoord θ p := rfl

@[simp] theorem leftMap_zero_coord (θ u v : ℝ) (p : Plane) :
    leftMap θ u v p 0 = u - eCoord θ p := rfl

@[simp] theorem leftMap_one_coord (θ u v : ℝ) (p : Plane) :
    leftMap θ u v p 1 = 1 - v + fCoord θ p := rfl

end

end Puzzling139335.N4TwoOneOne
