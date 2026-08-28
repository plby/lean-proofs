import Wikipedia.NoExoticSixSphere.DoubleCrossingSphereFrameComparison
import Wikipedia.NoExoticSixSphere.SphereUniversalTangentRemainder

/-!
# Transferring the checked Whitney comparison to the original resolution

The reference and original resolutions use the same source scale and
opening. Their reduced remainder operators are literally equal by the
source-only formula. The actual reference calculation therefore supplies
the original untwisted frame sum, and the paired source-twist comparison
gives the source-twisted sum with its extra one.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel SphereSumNeck DoubleCrossingSpherePair

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
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (hball : closedBall (0 : Vector 3 × Vector 3) 2 ⊆ Φ.source) (hc : Convex ℝ Φ.source)
  (Γ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Ioc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Θ.source)
  (hleft : ∀ v, (v, 0) ∈ Θ.source → Θ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Θ.source → Θ (0, v) = G (sourceChart v))
  (hprodΓ : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Γ.source)
  (hleftΓ : ∀ v, (v, 0) ∈ Γ.source → Γ (v, 0) = chartLeft Φ hball (sourceChart v))
  (hrightΓ : ∀ v, (0, v) ∈ Γ.source → Γ (0, v) = chartRight Φ hball (sourceChart v))
  (hcleanΓ : ∀ q ∈ Γ.source,
    (∀ x, chartLeft Φ hball x = Γ q ↔ q.2 = 0 ∧ x = sourceChart q.1) ∧
    (∀ x, chartRight Φ hball x = Γ q ↔ q.1 = 0 ∧ x = sourceChart q.2))
  (hΓ : Γ.target ⊆ Φ.target)

include r hc hprodΓ hleftΓ hrightΓ hcleanΓ hΓ in
theorem resolution_tangentRemainder_parity_eq_whitney :
    Monomorphism.sphereParityOfDimension 1 rfl rfl
        (e.tangentResolutionFrameRemainder ν Θ F G hε ha hprod hleft hright hF hG hFi hGi) =
      e.sphereDerivativeParity ν (WhitneySphere.chartMap Φ)
        (WhitneySphere.contMDiff_chartMap Φ (unitProduct_subset_source Φ hball))
        (WhitneySphere.injective_mfderiv_chartMap Φ (unitProduct_subset_source Φ hball)) := by
  have he := e.tangentResolutionFrameRemainder_eq_of_formula ν Θ F G hε ha hprod
    hleft hright hF hG hFi hGi
    (e.tangentResolutionFrameRemainder ν Γ (chartLeft Φ hball) (chartRight Φ hball)
      hε ha hprodΓ hleftΓ hrightΓ (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball)
      (injective_mfderiv_chartLeft Φ hball) (injective_mfderiv_chartRight Φ hball))
    (e.tangentResolutionFrameRemainder_eq_universal ν Γ (chartLeft Φ hball) (chartRight Φ hball)
      hε ha hprodΓ hleftΓ hrightΓ (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball)
      (injective_mfderiv_chartLeft Φ hball) (injective_mfderiv_chartRight Φ hball))
  rw [he]
  exact e.reference_tangentRemainder_parity_eq_whitney ν r Φ hball hc Γ
    hε ha hprodΓ hleftΓ hrightΓ hcleanΓ hΓ

include r hc hprodΓ hleftΓ hrightΓ hcleanΓ hΓ in
theorem sphereDerivativeParity_resolution_eq_inputs_add_whitney :
    e.sphereDerivativeParity ν (gluedSphere Θ ε a F G)
        (contMDiff_gluedSphere Θ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG)
        (injective_mfderiv_gluedSphere Θ F G hε hprod ha hleft hright hF hG hFi hGi) =
      e.sphereDerivativeParity ν F hF hFi + e.sphereDerivativeParity ν G hG hGi +
        e.sphereDerivativeParity ν (WhitneySphere.chartMap Φ)
          (WhitneySphere.contMDiff_chartMap Φ (unitProduct_subset_source Φ hball))
          (WhitneySphere.injective_mfderiv_chartMap Φ (unitProduct_subset_source Φ hball)) := by
  rw [e.resolutionFrameParity_tangent_decomposition ν Θ F G hε ha hprod
    hleft hright hF hG hFi hGi]
  rw [e.resolution_tangentRemainder_parity_eq_whitney ν r Θ F G hF hG hFi hGi Φ hball hc Γ
    hε ha hprod hleft hright hprodΓ hleftΓ hrightΓ hcleanΓ hΓ]

include r hc hprodΓ hleftΓ hrightΓ hcleanΓ hΓ in
theorem immersedSphereFrameParity_resolution_eq_inputs_add_one :
    e.immersedSphereFrameParity ν (gluedSphere Θ ε a F G)
        (contMDiff_gluedSphere Θ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG)
        (injective_mfderiv_gluedSphere Θ F G hε hprod ha hleft hright hF hG hFi hGi) =
      e.immersedSphereFrameParity ν F hF hFi + e.immersedSphereFrameParity ν G hG hGi + 1 := by
  have hsum := e.sphereDerivativeParity_resolution_eq_inputs_add_whitney ν r Θ F G hF hG
    hFi hGi Φ hball hc Γ hε ha hprod hleft hright hprodΓ hleftΓ hrightΓ hcleanΓ hΓ
  have hFG := e.immersedSphereFrameParity_sum_eq_derivativeParity ν F G hF hG hFi hGi
  have hKW := e.immersedSphereFrameParity_sum_eq_derivativeParity ν
    (gluedSphere Θ ε a F G) (WhitneySphere.chartMap Φ)
    (contMDiff_gluedSphere Θ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG)
    (WhitneySphere.contMDiff_chartMap Φ (unitProduct_subset_source Φ hball))
    (injective_mfderiv_gluedSphere Θ F G hε hprod ha hleft hright hF hG hFi hGi)
    (WhitneySphere.injective_mfderiv_chartMap Φ (unitProduct_subset_source Φ hball))
  rw [hsum, add_assoc, ZModModule.add_self, add_zero, ← hFG,
    e.immersedSphereFrameParity_whitney ν r Φ (unitProduct_subset_source Φ hball)] at hKW
  simpa only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two] using eq_sub_of_add_eq hKW

end NoExoticSixSphere.EuclideanEmbedding
