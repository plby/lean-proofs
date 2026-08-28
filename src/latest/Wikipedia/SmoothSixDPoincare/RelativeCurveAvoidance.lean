import Wikipedia.SmoothSixDPoincare.RelativeCurveEmbedding
import Wikipedia.SmoothSixDPoincare.CleanNeighborhoodAvoidance
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Embedded connecting curves avoiding obstacles, relative to endpoint neighborhoods

The curve is made embedded and immersive, then moved off the obstacle away
from a prescribed allowed-contact set. Its whole clean closed neighborhood
stays fixed. Finite obstacles are realized as genuine zero-dimensional smooth
manifolds using the library's discrete atlas, not treated as an assumed avoidance
principle.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- Construct an embedded immersive curve off a compact smooth obstacle, fixing its
prescribed clean neighborhood even when the boundary itself meets that obstacle. -/
theorem exists_relative_curve_avoidance_of_clean_neighborhood
    {F H' Y : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [LindelofSpace (ℝ × Y)]
    (f : C(ℝ, N)) (g : C(Y, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : 3 ≤ Module.finrank ℝ G) (hobstacle : 1 + Module.finrank ℝ F < Module.finrank ℝ G)
    {K C B : Set ℝ} (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hfixed : InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hclean : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ range g) :
    ∃ f' : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun t : K => f' t) ∧
      (∀ t ∈ K, Injective (mfderiv 𝓘(ℝ, ℝ) J f' t)) ∧
      ∀ t ∈ K \ B, f' t ∉ range g := by
  obtain ⟨f₁, hf₁, hhom₁, hemb₁, hderiv₁⟩ :=
    exists_relative_compact_curve_embedding f hf hdim hK hC hfixed hderiv
  have hinj₁ : InjOn f₁ K := by
    intro t ht s hs hts
    exact congrArg Subtype.val (hemb₁.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) hts)
  have hclean₁ : ∀ t ∈ K ∩ C, t ∉ B → f₁ t ∉ range g := by
    intro t ht htB
    rw [← hhom₁.fst_eq_snd ht.2]
    exact hclean t ht htB
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobs : Module.finrank ℝ ℝ + Module.finrank ℝ F < Module.finrank ℝ G := by
    simpa only [Module.finrank_self] using hobstacle
  obtain ⟨f₂, hf₂, hhom₂, hemb₂, hderiv₂, havoid⟩ :=
    exists_embedded_avoidance_relative_neighborhood f₁ g hf₁ hg hself hobs
      hK hC hBC hinj₁ hderiv₁ hclean₁
  exact ⟨f₂, hf₂, hhom₁.trans hhom₂, hemb₂, hderiv₂, havoid⟩

/-- A finite set of other intersection points can be avoided by the embedded curve,
while keeping its prescribed endpoint neighborhoods exactly unchanged. -/
theorem exists_relative_curve_avoiding_finite (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hdim : 3 ≤ Module.finrank ℝ G)
    {S : Set N} (hS : S.Finite) {K C B : Set ℝ}
    (hK : IsCompact K) (hC : IsClosed C) (hBC : B ⊆ interior C)
    (hfixed : InjOn f (K ∩ C))
    (hderiv : ∀ t ∈ K ∩ C, Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hclean : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ S) :
    ∃ f' : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f' ∧ f.HomotopicRel f' C ∧
      Topology.IsClosedEmbedding (fun t : K => f' t) ∧
      (∀ t ∈ K, Injective (mfderiv 𝓘(ℝ, ℝ) J f' t)) ∧
      ∀ t ∈ K \ B, f' t ∉ S := by
  let : Fintype S := hS.fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z S := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ S := IsManifold.of_discreteTopology _
  let g : C(S, N) := ⟨Subtype.val, continuous_subtype_val⟩
  have hg : ContMDiff 𝓘(ℝ, Z) J ∞ g := contMDiff_of_discreteTopology
  have hrange : range g = S := by ext y; simp [g]
  have hobs : 1 + Module.finrank ℝ Z < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin]
    omega
  have hclean' : ∀ t ∈ K ∩ C, t ∉ B → f t ∉ range g := by
    simpa only [hrange] using hclean
  obtain ⟨f', hf', hrel, hemb, hi, havoid⟩ :=
    exists_relative_curve_avoidance_of_clean_neighborhood f g hf hg hdim hobs
      hK hC hBC hfixed hderiv hclean'
  refine ⟨f', hf', hrel, hemb, hi, ?_⟩
  simpa only [hrange] using havoid

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
