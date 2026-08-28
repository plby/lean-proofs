import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCover
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryAffineColumns

/-!
# The two genuine elliptic intersection columns

The actual quarter-time maps land in the geometrically identified overlap
components.  Their literal upper-chart fibre maps contain the full common
deck frame and the original fixed-time logarithmic translation.  Only
after this pointwise identification are homotopy invariance and the proved
invariance of Wang-boundary classes applied.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Elliptic Homology
open SpecialPeriods.Threefold.EllipticGeometry
open SingularMayerVietoris PeriodTorusHigherHomology

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The first column occupies the middle component for order three and the right for order four. -/
def ellipticLowerColumnIndex (j : Kind) : Fin 3 :=
  if attachingMeridianIndex j then 2 else 0

/-- The second column occupies the left component for order three and the middle for order four. -/
def ellipticUpperColumnIndex (j : Kind) : Fin 3 :=
  if attachingMeridianIndex j then 0 else 1

theorem ellipticLowerColumnIndex_overlap (j : Kind) :
    intersectionIndex (ellipticLowerColumnIndex j) =
      canonicalQuarterOverlapIndex (attachingMeridianIndex j) := by
  cases j <;> decide

theorem ellipticUpperColumnIndex_overlap (j : Kind) :
    intersectionIndex (ellipticUpperColumnIndex j) =
      canonicalThreeQuarterOverlapIndex (attachingMeridianIndex j) := by
  cases j <;> decide

/-- The exact first projected overlap point with the actual intersection indexing. -/
def ellipticLowerColumnPoint (j : Kind) :
    overlapBase (intersectionIndex (ellipticLowerColumnIndex j)) :=
  ⟨(canonicalQuarterOverlapPoint (attachingMeridianIndex j)).val, by
    rw [ellipticLowerColumnIndex_overlap]
    exact (canonicalQuarterOverlapPoint (attachingMeridianIndex j)).property⟩

/-- The exact second projected overlap point in that same indexing. -/
def ellipticUpperColumnPoint (j : Kind) :
    overlapBase (intersectionIndex (ellipticUpperColumnIndex j)) :=
  ⟨(canonicalThreeQuarterOverlapPoint (attachingMeridianIndex j)).val, by
    rw [ellipticUpperColumnIndex_overlap]
    exact (canonicalThreeQuarterOverlapPoint (attachingMeridianIndex j)).property⟩

/-- Genuine component membership for the whole first fibre map. -/
theorem ellipticLowerColumn_mem (j : Kind) (x : RealTorus₄) :
    ellipticLowerColumn j x ∈ intersectionPiece Dsp (ellipticLowerColumnIndex j) := by
  change (Dsp).projection (ellipticLowerColumn j x).val ∈
    overlapBase (intersectionIndex (ellipticLowerColumnIndex j))
  rw [ellipticLowerColumn_coe, (Dsp).projection_quotient]
  change triangleRegularProject
    (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4)) ∈ _
  rw [nativeShiftedSquareLift_quarter_project, ellipticLowerColumnIndex_overlap]
  exact (canonicalQuarterOverlapPoint (attachingMeridianIndex j)).property

/-- Genuine component membership for the whole second fibre map. -/
theorem ellipticUpperColumn_mem (j : Kind) (x : RealTorus₄) :
    ellipticUpperColumn j x ∈ intersectionPiece Dsp (ellipticUpperColumnIndex j) := by
  change (Dsp).projection (ellipticUpperColumn j x).val ∈
    overlapBase (intersectionIndex (ellipticUpperColumnIndex j))
  rw [ellipticUpperColumn_coe, (Dsp).projection_quotient]
  change triangleRegularProject
    (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4)) ∈ _
  rw [nativeShiftedSquareLift_threeQuarter_project, ellipticUpperColumnIndex_overlap]
  exact (canonicalThreeQuarterOverlapPoint (attachingMeridianIndex j)).property

/-- The exact first deck frame in the actual intersection-component chart. -/
theorem ellipticLowerColumn_frame (j : Kind) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4) =
      ellipticBoundaryFrame j • upperLiftOnOverlap normalizedSlitBaseLift
        (intersectionIndex (ellipticLowerColumnIndex j)) (ellipticLowerColumnPoint j) := by
  cases j <;> exact nativeShiftedSquareLift_quarter_frame _

/-- The exact second deck frame is the same full frame. -/
theorem ellipticUpperColumn_frame (j : Kind) :
    nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4) =
      ellipticBoundaryFrame j • upperLiftOnOverlap normalizedSlitBaseLift
        (intersectionIndex (ellipticUpperColumnIndex j)) (ellipticUpperColumnPoint j) := by
  cases j <;> exact nativeShiftedSquareLift_threeQuarter_frame _

/-- At any fixed time the retained actual gauge is exactly translation by its value at zero. -/
theorem nativeGaugeCylinder_fibre_translation (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    nativeGaugeCylinder j τ (t, x) = x + nativeGaugeCylinder j τ (t, 0) := by
  simp only [nativeGaugeCylinder_apply, zero_add]

/-- The exact actual homology coefficient of the first column, with its frame retained. -/
theorem ellipticLowerColumn_homology (j : Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    Homology.intersectionHomologyEquiv Dsp normalizedSlitBaseLift n
        (singularHomologyMap (ellipticLowerColumn j) n a) =
      componentCoordinates (ellipticLowerColumnIndex j)
        (triangleHomologyEquiv (ellipticBoundaryFrame j)⁻¹ n a) := by
  have h := intersectionHomology_component_affine Dsp normalizedSlitBaseLift
    (ellipticLowerColumn j) (ellipticLowerColumnIndex j) (ellipticLowerColumn_mem j)
    (ellipticLowerColumnPoint j)
    (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 1 / 4))
    (ellipticBoundaryFrame j) (ellipticLowerColumn_frame j)
    (ContinuousMap.id RealTorus₄)
    (nativeGaugeCylinder j (ellipticBoundaryPhase j) (1 / 4, 0))
    (fun x => by
      rw [ellipticLowerColumn_coe, nativeGaugeCylinder_fibre_translation]
      rfl) n a
  rw [singularHomologyMap_id, LinearMap.id_apply] at h
  exact h

/-- The corresponding exact coefficient of the second actual column. -/
theorem ellipticUpperColumn_homology (j : Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    Homology.intersectionHomologyEquiv Dsp normalizedSlitBaseLift n
        (singularHomologyMap (ellipticUpperColumn j) n a) =
      componentCoordinates (ellipticUpperColumnIndex j)
        (triangleHomologyEquiv (ellipticBoundaryFrame j)⁻¹ n a) := by
  have h := intersectionHomology_component_affine Dsp normalizedSlitBaseLift
    (ellipticUpperColumn j) (ellipticUpperColumnIndex j) (ellipticUpperColumn_mem j)
    (ellipticUpperColumnPoint j)
    (nativeShiftedSquareLift j (ellipticBoundaryPhase j) (1, 3 / 4))
    (ellipticBoundaryFrame j) (ellipticUpperColumn_frame j)
    (ContinuousMap.id RealTorus₄)
    (nativeGaugeCylinder j (ellipticBoundaryPhase j) (3 / 4, 0))
    (fun x => by
      rw [ellipticUpperColumn_coe, nativeGaugeCylinder_fibre_translation]
      rfl) n a
  rw [singularHomologyMap_id, LinearMap.id_apply] at h
  exact h

/-- The actual first column is the unaltered Wang class in its proved component. -/
theorem ellipticLowerColumn_wangBoundary (j : Kind) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus (flatTorusAffine j j.twist)) (n + 1)) :
    Homology.intersectionHomologyEquiv Dsp normalizedSlitBaseLift n
        (singularHomologyMap (ellipticLowerColumn j) n
          (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a)) =
      componentCoordinates (ellipticLowerColumnIndex j)
        (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a) := by
  rw [ellipticLowerColumn_homology, ellipticBoundaryFrame_inv_wangBoundary]

/-- The actual second column is the same unaltered Wang class in its other proved component. -/
theorem ellipticUpperColumn_wangBoundary (j : Kind) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus (flatTorusAffine j j.twist)) (n + 1)) :
    Homology.intersectionHomologyEquiv Dsp normalizedSlitBaseLift n
        (singularHomologyMap (ellipticUpperColumn j) n
          (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a)) =
      componentCoordinates (ellipticUpperColumnIndex j)
        (MappingTorusHomology.wangBoundary (flatTorusAffine j j.twist) n a) := by
  rw [ellipticUpperColumn_homology, ellipticBoundaryFrame_inv_wangBoundary]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
