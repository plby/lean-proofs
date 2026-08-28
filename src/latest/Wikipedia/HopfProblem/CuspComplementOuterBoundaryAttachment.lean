import Wikipedia.HopfProblem.CuspBoundaryToricExtensionComparison
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspHeightHomotopy
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry

/-!
# The original cusp attachment at every allowed boundary height

The whole rank-four cusp mapping torus maps into the original overlap
domain at every allowed logarithmic height. Applying the unchanged cusp
overlap gives exactly the existing regular-family boundary map at that
height. The two ambient inclusions therefore agree point for point, with
the full original real-period coordinate and monodromy marking retained.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspComplement.OuterBoundary

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.Threefold.Homology
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Cusp
open CuspBoundaryToricExtension

/-- Every actual boundary point lies in the source of the original cusp-to-regular overlap. -/
theorem boundaryToFull_mem_overlap_source (h : Height specialData.radius)
    (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    boundaryToFull specialData h q ∈ specialCuspOverlap.source := by
  rw [specialCuspOverlap_source]
  exact (specialPuncturedHomeomorph.symm (boundaryInclusion specialData h q)).property

/-- The original native cusp overlap is exactly the actual regular boundary map at this height. -/
theorem specialCuspOverlap_boundaryToFull (h : Height specialData.radius)
    (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    specialCuspOverlap (boundaryToFull specialData h q) =
      TrianglePeriodFamily.Boundary.Cusp.heightBoundaryMap h q := by
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective monodromy q
  rw [boundaryToFull_mk, TrianglePeriodFamily.Boundary.Cusp.heightBoundaryMap_mk]
  rw [boundaryCylinder_apply, specialCuspOverlap_family, CuspGlobalOverlap.familyMap_quotient]
  rfl

/-- The cusp and regular boundary markings give the same point of the original threefold. -/
theorem boundaryToFull_ambient_eq_regular (h : Height specialData.radius)
    (q : ThreefoldOverlapMappingTorus.Cusp.Boundary) :
    CuspGeometry.inclusion (boundaryToFull specialData h q) =
      inclusion none (TrianglePeriodFamily.Boundary.Cusp.heightBoundaryMap h q) := by
  let p : PuncturedPiece none :=
    specialPuncturedHomeomorph.symm (boundaryInclusion specialData h q)
  have hi := puncturedPieceToRegular_inclusion none p
  have he := puncturedPieceToRegular_cusp p
  exact hi.symm.trans (congrArg (inclusion none)
    (he.trans (specialCuspOverlap_boundaryToFull h q)))

/-- Equality of the actual ambient continuous maps, not only of their homotopy classes. -/
theorem boundary_maps_agree (h : Height specialData.radius) :
    (originalPieceInclusion (some none)).comp (boundaryToFull specialData h) =
      originalRegularInclusion.comp (TrianglePeriodFamily.Boundary.Cusp.heightBoundaryMap h) := by
  apply ContinuousMap.ext
  intro q
  exact boundaryToFull_ambient_eq_regular h q

/-- The common ambient point retains the original full real-period fibre on every cylinder. -/
theorem boundaryToFull_ambient_mk (h : Height specialData.radius) (t : ℝ) (x : RealTorus₄) :
    CuspGeometry.inclusion
        (boundaryToFull specialData h (MappingTorus.mk monodromy (t, x))) =
      inclusion none (boundaryRegularData.quotient
        (TrianglePeriodFamily.Boundary.Cusp.baseLift h t, x)) := by
  rw [boundaryToFull_ambient_eq_regular,
    TrianglePeriodFamily.Boundary.Cusp.heightBoundaryMap_mk]

end Wikipedia.HopfProblem.CuspComplement.OuterBoundary
