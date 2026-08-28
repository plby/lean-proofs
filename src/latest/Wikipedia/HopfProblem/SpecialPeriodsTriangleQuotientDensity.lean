import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientRegularChartsTopology
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Density of the actual regular triangle quotient

The exceptional points upstairs form the countable union of the two proved
elliptic orbits.  Its complement is dense in the upper half-plane, and the
actual quotient projection transports this density to the regular open
part of the full quotient.
-/

noncomputable section

open Set UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The actual points with trivial triangle-group stabilizer are dense. -/
theorem triangleRegularLocus_dense : Dense triangleRegularLocus := by
  rw [triangleRegularLocus_eq_compl_ellipticSet]
  have hd : Dense (((↑) : ℍ → ℂ) '' triangleEllipticSet)ᶜ :=
    (triangleEllipticSet_countable.image ((↑) : ℍ → ℂ)).dense_compl ℂ
  have hp := hd.preimage UpperHalfPlane.isOpenEmbedding_coe.isOpenMap
  simpa only [preimage_compl, preimage_image_eq _ UpperHalfPlane.coe_injective] using hp

/-- The actual regular open subspace is dense in the full triangle quotient. -/
theorem triangleOrbitRegularDomain_dense :
    Dense (triangleOrbitRegularDomain : Set TriangleOrbitSpace) := by
  rw [triangleOrbitRegularDomain_eq_image]
  exact triangleOrbitProjection_surjective.denseRange.dense_image
    triangleOrbitProjection_continuous triangleRegularLocus_dense

end Wikipedia.HopfProblem.SpecialPeriods
