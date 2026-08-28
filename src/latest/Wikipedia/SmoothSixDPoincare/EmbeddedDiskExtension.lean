import Wikipedia.SmoothSixDPoincare.SphereBoundaryDerivativeRepair
import Wikipedia.SmoothSixDPoincare.TwoDimensionalEmbedding
import Wikipedia.SmoothSixDPoincare.Hemisphere

/-!
# Actual embedded disk extensions with an exact prescribed sphere boundary

First repair the transverse boundary derivative, without changing any sphere
value. Then apply the relative compact embedding construction to the entire
closed disk. The result is a globally smooth ambient map whose restriction
to the actual closed Euclidean disk is a closed embedding with injective
native derivatives, and whose boundary is exactly the original circle map.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- A smooth ambient extension of a smooth embedded immersive circle can be replaced by a
genuine embedded disk with exactly the same boundary in target dimension at least five. -/
theorem exists_embedded_disk_extension_of_smooth_extension
    {f : Hemisphere.Ambient 2 → N} (hf : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ f)
    {γ : Hemisphere.Sphere 1 → N} (hext : ∀ x : Hemisphere.Sphere 1, f x.1 = γ x)
    (hγinj : Function.Injective γ)
    (hγderiv : ∀ x, Function.Injective (mfderiv (𝓡 1) J γ x))
    (hdim : 5 ≤ Module.finrank ℝ G) :
    ∃ g : C(Hemisphere.Ambient 2, N), ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) J ∞ g ∧
      (∀ x : Hemisphere.Sphere 1, g x.1 = γ x) ∧
      Topology.IsClosedEmbedding (fun x : Hemisphere.Ball 2 => g x.1) ∧
      ∀ x : Hemisphere.Ball 2, Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J g x.1) := by
  let : Fact (Module.finrank ℝ (Hemisphere.Ambient 2) = 1 + 1) :=
    ⟨by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]⟩
  have hd : 1 + Module.finrank ℝ (Hemisphere.Ambient 2) < Module.finrank ℝ G := by
    simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]
    omega
  obtain ⟨f₁, hf₁, hboundary₁, hderiv₁⟩ :=
    SphereBoundary.exists_extension_immersive_on_sphere (n := 1) hf hext hγderiv hd
  let K : Set (Hemisphere.Ambient 2) := Metric.closedBall 0 1
  let C : Set (Hemisphere.Ambient 2) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_closedBall 0 1
  have hC : IsClosed C := Metric.isClosed_sphere
  have hfixed : InjOn f₁ (K ∩ C) := by
    intro x hx y hy hxy
    let xs : Hemisphere.Sphere 1 := ⟨x, hx.2⟩
    let ys : Hemisphere.Sphere 1 := ⟨y, hy.2⟩
    have hboundaryeq : γ xs = γ ys :=
      (hboundary₁ xs).symm.trans (hxy.trans (hboundary₁ ys))
    exact congrArg Subtype.val (hγinj hboundaryeq)
  have hderiv : ∀ x ∈ K ∩ C,
      Function.Injective (mfderiv 𝓘(ℝ, Hemisphere.Ambient 2) J f₁ x) :=
    fun x hx => hderiv₁ ⟨x, hx.2⟩
  obtain ⟨g, hg, hhom, hemb, hderivg⟩ :=
    ManifoldImmersion.exists_relative_compact_embedding_twoDimensional f₁ hf₁
      (by simp only [Hemisphere.Ambient, finrank_euclideanSpace_fin]) hdim hK hC hfixed hderiv
  refine ⟨g, hg, ?_, hemb, fun x => hderivg x.1 x.property⟩
  intro x
  exact (hhom.fst_eq_snd x.property).symm.trans (hboundary₁ x)

end Wikipedia.SmoothSixDPoincare
