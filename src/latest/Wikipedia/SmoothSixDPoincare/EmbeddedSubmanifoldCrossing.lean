import Wikipedia.SmoothSixDPoincare.ParametrizedSubmanifoldCrossing
import Wikipedia.SmoothSixDPoincare.CenteredParametrization

/-!
# Constructed crossing charts for native embedded submanifolds

Both sheet parametrizations are constructed from their original smooth atlases.
Their genuine native transversality gives a simultaneous chart, then the
embedding topologies exclude all other branches of the full submanifolds.
Membership in either full image is exactly vanishing of its complementary
chart coordinate. No coordinate patch, local normal form, or clean neighborhood
is an input hypothesis.
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

/-- The full native embedded submanifolds have constructed clean product coordinates
at each transverse intersection, inside any prescribed open neighborhood. -/
theorem exists_clean_crossingChart {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hembG : IsEmbedding G) (x : N) (y : P) (hxy : G y = F x)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {O : Set M} (hO : IsOpen O) (hxO : F x ∈ O) :
    ∃ a : ℝ, 0 < a ∧ ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
      closedBall (0 : D) a ×ˢ closedBall (0 : Z) a ⊆ Φ.source ∧
      Φ.source ⊆ (NativeParametrization.centered (D := D) x).source ×ˢ
        (NativeParametrization.centered (D := Z) y).source ∧
      Φ.target ⊆ O ∧ Φ (0, 0) = F x ∧
      (∀ u, (u, 0) ∈ Φ.source → Φ (u, 0) = F (NativeParametrization.centered (D := D) x u)) ∧
      (∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (NativeParametrization.centered (D := Z) y v)) ∧
      (∀ q ∈ Φ.source, (Φ q ∈ range F ↔ q.2 = 0) ∧ (Φ q ∈ range G ↔ q.1 = 0)) := by
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
  obtain ⟨a, ha, Φ, hprod, hsource, htarget, hcenter, hleft, hright, himages⟩ :=
    exists_clean_crossingChart_of_parametrizations hF hG hembF hembG c d hc0 hd0
      hxy' hdim ht' hO hxO'
  exact ⟨a, ha, Φ, hprod, hsource, htarget, hcenter.trans (congrArg F hcx),
    hleft, hright, himages⟩

end Wikipedia.SmoothSixDPoincare
