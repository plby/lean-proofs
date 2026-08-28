import Wikipedia.NoExoticSixSphere.SphereResolutionWhitneyComparison
import Wikipedia.NoExoticSixSphere.ConvexReferenceProductChart

/-!
# The actual frame-sum formula at all sufficiently small resolution scales

The convex reference chart and its globally clean two-crossing sheet chart
are constructed, not assumed. Their positive chart radius supplies one
threshold. Every original resolution below it has source-twisted frame value
equal to the two input frame values plus one, for every positive opening.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereSumNeck DoubleCrossingSpherePair ProductChartCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (Θ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : C(Sphere 3, M))
  (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
  (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
  (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))
  (hleft : ∀ v, (v, 0) ∈ Θ.source → Θ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Θ.source → Θ (0, v) = G (sourceChart v))

include r in
theorem exists_small_resolution_frame_sum (h0 : (0 : Vector 3 × Vector 3) ∈ Θ.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ δ →
      ∀ (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) 1)
        (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
          closedBall (0 : Vector 3) (ε * 4) ⊆ Θ.source),
        e.immersedSphereFrameParity ν (gluedSphere Θ ε a F G)
            (contMDiff_gluedSphere Θ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG)
            (injective_mfderiv_gluedSphere Θ F G hε hprod ha hleft hright hF hG hFi hGi) =
          e.immersedSphereFrameParity ν F hF hFi + e.immersedSphereFrameParity ν G hG hGi + 1 := by
  obtain ⟨Φ, _, hc, hball, _, _⟩ := exists_convex_reference_chart Θ h0
  obtain ⟨b, hb, Γ, hbΓ, hΓ, hleftΓ, hrightΓ, hcleanΓ⟩ :=
    exists_clean_chart Φ hball
  refine ⟨b / 4, div_pos hb (by norm_num), ?_⟩
  intro ε hε hbound a ha hprod
  have hscale : ε * 4 ≤ b := by linarith
  have hprodΓ : closedBall (0 : Vector 3) (ε * 4) ×ˢ
      closedBall (0 : Vector 3) (ε * 4) ⊆ Γ.source := by
    intro p hp
    exact hbΓ ⟨closedBall_subset_closedBall hscale hp.1,
      closedBall_subset_closedBall hscale hp.2⟩
  exact e.immersedSphereFrameParity_resolution_eq_inputs_add_one ν r Θ F G hF hG hFi hGi
    Φ hball hc Γ hε ha hprod hleft hright hprodΓ hleftΓ hrightΓ hcleanΓ hΓ

end NoExoticSixSphere.EuclideanEmbedding
