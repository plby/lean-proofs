import Wikipedia.SmoothSixDPoincare.SurgeryBeltAvoidance
import Wikipedia.SmoothSixDPoincare.SurgeryComplementContractions

/-!
# Propagating circle contractions to the whole new surgery boundary

The old attaching sphere has codimension at least three, while the new belt
has codimension at least two. Remove the old sphere, compare the actual
complements, and move an arbitrary new-boundary circle off the belt.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

variable {N F R X Y G H : Type*}
  [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace H X] [IsManifold J ∞ X] [T2Space X]

/-- In the indicated dimension range, old-boundary contractions imply whole new-boundary
contractions, not merely contractions in a deleted complement. -/
theorem newBoundary_circle_nullhomotopies (n : ℕ)
    [Fact (Module.finrank ℝ N = n + 1)] (hn : 0 < n)
    (d : SurgeryBoundaryPair N F R X Y)
    (hattach : ContMDiff (𝓡 n) J ∞ d.attachingSphere)
    (hdim : 2 + n < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, X),
      ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, Y), ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  have hnormal : 1 < Module.finrank ℝ N := by
    rw [show Module.finrank ℝ N = n + 1 from Fact.out]
    omega
  exact d.circle_nullhomotopies_of_beltComplement hnormal
    (d.beltComplement_circle_nullhomotopies_of_sphere_dimension n hattach hdim hnull)

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
