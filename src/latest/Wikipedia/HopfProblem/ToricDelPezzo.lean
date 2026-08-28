import Wikipedia.HopfProblem.ToricBlowdownPunctured
import Wikipedia.HopfProblem.ToricBlowdownExceptionalBoundary

/-!
# The central toric surface as the three-point blow-up of the projective plane

The complex-analytic blow-up of a surface at a point is locally the
incidence-model blow-up of the affine plane. We record this standard
local-model definition over the three affine charts of the actual complex
projective plane, and prove it for the constructed compact ray surface.
The centers are the three independent coordinate points.

This identifies the surface in the description of `dP₆` in §4 of the source.
No separate intersection-theoretic calculation of the canonical degree or
ampleness is asserted here.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

open ToricCharts

local notation "I₂" => modelWithCornersSelf ℂ (CoordinateSpace 2)

/-- A holomorphic proper map is the blow-up at the projective coordinate
points when every complete inverse image of a standard affine patch is
biholomorphic over that patch to the incidence blow-up of `ℂ²` at zero.
The three patches cover `ℙ²` and each contains exactly one center. -/
def IsCoordinatePointBlowup {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (CoordinateSpace 2) Y] (f : Y → ProjectivePlane.Space) : Prop :=
  ContMDiff I₂ I₂ ω f ∧ IsProperMap f ∧
    ∀ k : Fin 3, ∃ U : TopologicalSpace.Opens Y,
      (U : Set Y) = f ⁻¹' ProjectivePlane.affineTarget k ∧
      ∃ e : Diffeomorph I₂ I₂ AffineBlowup.Space U ω,
        ∀ x, f (e x : Y) = ProjectivePlane.affineMap k (AffineBlowup.projection x)

namespace ToricComponent

open ToricFan ToricSpace

/-- The actual compact toric ray surface is the blow-up of the actual
complex projective plane at its three coordinate points. No global
surface or blow-up comparison is assumed as a hypothesis. -/
theorem zeroRay_isCoordinatePointBlowup : IsCoordinatePointBlowup blowdown := by
  refine ⟨blowdown_holomorphic, blowdown_isProperMap, fun k => ?_⟩
  refine ⟨blowupOpenSet k, (blowdown_preimage_affineTarget k).symm,
    blowupBiholomorph k, ?_⟩
  exact blowdown_blowupMap k

/-- In particular the blow-up is at three independent, not collinear,
points, the standard three-point model of the degree-six del Pezzo surface. -/
theorem zeroRay_three_independent_point_blowup :
    Projectivization.Independent ProjectivePlane.coordinatePoint ∧
      IsCoordinatePointBlowup blowdown :=
  ⟨ProjectivePlane.coordinatePoint_independent, zeroRay_isCoordinatePointBlowup⟩

/-- Outside the three odd boundary curves the blow-down is the already
constructed biholomorphism with `ℙ²` minus its three centers. -/
theorem blowdownPuncturedSpace_eq_compl_exceptional_curves :
    (blowdownPuncturedSpace : Set (rayDivisor 0)) =
      (⋃ k : Fin 3, CuspQuotient.componentBoundary (exceptionalRay k))ᶜ := by
  change blowdown ⁻¹' ProjectivePlane.coordinatePointsᶜ = _
  rw [preimage_compl, blowdown_preimage_coordinatePoints]

end ToricComponent

end Wikipedia.HopfProblem
