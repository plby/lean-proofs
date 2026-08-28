import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspImage
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientRegularChartsTopology

/-!
# High cusp images lie in the actual regular locus

A transformation fixing a point of a high horodisc returns the horodisc
to itself, so the proved precise-invariance theorem makes it a cusp
power.  The actual integer translations act freely.  Thus these
horodiscs and their full quotient images avoid both elliptic orbits.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- Every point of a sufficiently high horodisc has trivial stabilizer
for the actual full triangle action. -/
theorem horodisc_subset_triangleRegularLocus (Y : ℝ) (hY : width ≤ Y) :
    (horodisc Y : Set ℍ) ⊆ triangleRegularLocus := by
  intro z hz
  apply (mem_triangleRegularLocus_iff z).mpr
  intro g hg
  have hgC := triangle_horodisc_overlap_mem_cusp Y hY g
    ⟨z, ⟨z, hz, hg⟩, hz⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgC
  have hfixed : triangleGeometricRepresentation (triangleCuspGenerator ^ n) z = z := by
    rw [hn]
    exact hg
  have hzero : triangleGeometricRepresentation (triangleCuspGenerator ^ (0 : ℤ)) z = z := by
    simp
  have hn0 := triangleGeometricRepresentation_cusp_orbit_injective z
    (hfixed.trans hzero.symm)
  rw [← hn, hn0, zpow_zero]

/-- The genuine high cusp image is an open subset of the regular part
of the full quotient, not a neighborhood containing an elliptic branch. -/
theorem cuspImage_subset_regularDomain (Y : ℝ) (hY : width ≤ Y) :
    (cuspImage Y : Set TriangleOrbitSpace) ⊆ triangleOrbitRegularDomain := by
  rintro q ⟨z, hz, rfl⟩
  exact (triangleOrbitProjection_mem_regularDomain_iff z).mpr
    (horodisc_subset_triangleRegularLocus Y hY hz)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
