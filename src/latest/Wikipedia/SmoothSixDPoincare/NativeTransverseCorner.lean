import Wikipedia.SmoothSixDPoincare.EmbeddedSubmanifoldCrossing
import Wikipedia.SmoothSixDPoincare.ParametrizedTransverseCorner

/-!
# A clean corner constructed directly from native transverse embeddings

The source parametrizations, crossing chart, and planar corner map are all
constructed. The corner map is smooth and embedded on an open neighborhood of
the origin, including both axes, and its off-axis points avoid both full native
submanifold images. This is a local corner, not a complete Whitney boundary
neighborhood or a framed Whitney disk.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]

/-- At each transverse intersection, actual native embeddings give a constructed clean corner,
with arbitrary nonzero coordinate directions for its two boundary arcs. -/
theorem exists_native_clean_corner {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hembG : IsEmbedding G) (x : N) (y : P) (hxy : G y = F x)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {u : D} {v : Z} (hu : u ≠ 0) (hv : v ≠ 0)
    {O : Set M} (hO : IsOpen O) (hxO : F x ∈ O) :
    ∃ W : Set (ℝ × ℝ), IsOpen W ∧ (0 : ℝ × ℝ) ∈ W ∧ ∃ k : (ℝ × ℝ) → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧ InjOn k W ∧ MapsTo k W O ∧
      k 0 = F x ∧
      (∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
      (∀ p ∈ W, (k p ∈ range F ↔ p.2 = 0) ∧ (k p ∈ range G ↔ p.1 = 0)) ∧
      (∀ s, (s, 0) ∈ W → k (s, 0) = F (NativeParametrization.centered (D := D) x (s • u))) ∧
      (∀ t, (0, t) ∈ W → k (0, t) = G (NativeParametrization.centered (D := Z) y (t • v))) := by
  let c := NativeParametrization.centered (D := D) x
  let d := NativeParametrization.centered (D := Z) y
  have hc0 : (0 : D) ∈ c.source := NativeParametrization.zero_mem_centered_source x
  have hd0 : (0 : Z) ∈ d.source := NativeParametrization.zero_mem_centered_source y
  have hcx : c 0 = x := NativeParametrization.centered_zero x
  have hdy : d 0 = y := NativeParametrization.centered_zero y
  have hxy' : G (d 0) = F (c 0) := by rw [hcx, hdy]; exact hxy
  have ht' : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))) := by
    rw [hcx, hdy]
    exact ht
  have hxO' : F (c 0) ∈ O := by rw [hcx]; exact hxO
  obtain ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter, hi, hclean, hlo, hhi⟩ :=
    exists_native_clean_corner_of_parametrizations hF hG hembF hembG c d hc0 hd0
      hxy' hdim ht' hu hv hO hxO'
  exact ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter.trans (congrArg F hcx),
    hi, hclean, hlo, hhi⟩

end Wikipedia.SmoothSixDPoincare
