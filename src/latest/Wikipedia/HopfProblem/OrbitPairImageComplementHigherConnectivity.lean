import Wikipedia.HopfProblem.OrbitPairSphereNullhomotopyCriterion
import Wikipedia.SmoothSixDPoincare.ImageComplementNullhomotopy

/-!
# Native higher homotopy vanishing in actual image complements

The dimension inequality includes the cylinder direction. An ambient
sphere contraction is moved into the genuine open complement, and exact
disk extension makes it based before pulling it back to a native cube.
Thus the conclusion concerns the original native homotopy group.
-/

noncomputable section

open Set ContinuousMap
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.ImageComplementConnectivity

open Wikipedia.SmoothSixDPoincare

variable {E G H K Y N : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem pi_subsingleton {n : ℕ} (hn : 0 < n) (g : C(Y, N))
    (hg : ContMDiff I J ∞ g)
    (hdim : n + 1 + Module.finrank ℝ E < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere n, N),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    (x : ImageComplement.domain g) : Subsingleton (π_ n (ImageComplement.domain g) x) := by
  let : Nonempty (Hemisphere.Sphere n) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  apply SphereNullhomotopy.pi_subsingleton_of_sphere_nullhomotopies hn
  intro f
  exact ImageComplement.nullhomotopic_of_ambient_nullhomotopic (I := 𝓡 n) g hg
    (by simpa only [finrank_euclideanSpace_fin] using hdim) f (hnull _)

end Wikipedia.HopfProblem.OrbitPair.ImageComplementConnectivity
