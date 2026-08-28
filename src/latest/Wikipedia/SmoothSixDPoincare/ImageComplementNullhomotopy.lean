import Wikipedia.SmoothSixDPoincare.ImageComplementHomotopy
import Wikipedia.SmoothSixDPoincare.Hemisphere
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# High-codimension image removal preserves circle contractions

An ambient contraction can be based at a point of the original map, hence
at a point already in the complement. Cylinder avoidance then moves that
contraction entirely into the actual complement. In particular, removing
a smooth circle from a five-dimensional manifold preserves the required
circle-nullhomotopy property. This is not a codimension-two removal theorem.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ImageComplement

variable {E E' G H H' K X Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [T2Space X] [CompactSpace X] [Nonempty X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

include I in
/-- Base the contraction at an actual image point before removing the obstacle. -/
theorem nullhomotopic_of_ambient_nullhomotopic (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f : C(X, domain g))
    (hambient : ∃ c, ((inclusion g).comp f).Homotopic (ContinuousMap.const X c)) :
    ∃ c, f.Homotopic (ContinuousMap.const X c) := by
  classical
  obtain ⟨c, hc⟩ := hambient
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  have hconst : (ContinuousMap.const X ((f x₀ : domain g) : N)).Homotopic
      (ContinuousMap.const X c) :=
    hc.comp (Homotopic.refl (ContinuousMap.const X x₀))
  refine ⟨f x₀, homotopic_of_ambient_homotopic (I := I) g hg hdim f
    (ContinuousMap.const X (f x₀)) ?_⟩
  exact hc.trans hconst.symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [T2Space X] [CompactSpace X] [Nonempty X] in
/-- Circle contractions survive removal of a smooth image
of codimension at least three. -/
theorem circle_nullhomotopies (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : 2 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, N),
      ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, domain g), ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : Nonempty (Hemisphere.Sphere 1) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  intro f
  apply nullhomotopic_of_ambient_nullhomotopic (I := 𝓡 1) g hg _ f (hnull _)
  simpa only [finrank_euclideanSpace_fin] using hdim

end Wikipedia.SmoothSixDPoincare.ImageComplement
