import Wikipedia.NoExoticSixSphere.DoubleCrossingSpherePairResolution
import Wikipedia.NoExoticSixSphere.NullhomotopicImmersedFrameValue
import Wikipedia.NoExoticSixSphere.WhitneySphereFrameValue
import Wikipedia.NoExoticSixSphere.SphereTangentResolutionRemainder
import Wikipedia.NoExoticSixSphere.ImmersedFrameDerivativeComparison

/-!
# The reference resolution remainder has the Whitney derivative-frame parity

Both embedded inputs contract in the enclosing convex chart and have no
self-intersections. Their actual resolution contracts there and has odd
double-point parity. Corrected-parity invariance computes the source-twisted
values; the checked paired comparison then gives the required untwisted
Whitney value. The source twist is never assigned a numerical value.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace DoubleCrossingSpherePair

open GLOrthonormalization

theorem unitProduct_subset_source {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Vector 6) M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
      (Vector 3 × Vector 3) M ∞)
    (hball : closedBall (0 : Vector 3 × Vector 3) 2 ⊆ Φ.source) :
    closedBall (0 : Vector 3) 1 ×ˢ closedBall (0 : Vector 3) 1 ⊆ Φ.source := by
  intro p hp
  apply hball
  rw [← closedBall_prod_same]
  exact ⟨closedBall_subset_closedBall (by norm_num) hp.1,
    closedBall_subset_closedBall (by norm_num) hp.2⟩

end DoubleCrossingSpherePair

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SphereSumNeck DoubleCrossingSpherePair

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (hball : closedBall (0 : Vector 3 × Vector 3) 2 ⊆ Φ.source)
  (hc : Convex ℝ Φ.source)

include r hc in
theorem immersedSphereFrameParity_referenceLeft :
    e.immersedSphereFrameParity ν (chartLeft Φ hball) (contMDiff_chart_left Φ hball)
      (injective_mfderiv_chartLeft Φ hball) = 0 := by
  have h := e.immersedSphereFrameParity_eq_unordered_of_nullhomotopic ν r (chartLeft Φ hball)
    (contMDiff_chart_left Φ hball) (injective_mfderiv_chartLeft Φ hball)
    (chartLeft_selfTransverse Φ hball) (Φ 0) ⟨leftContraction Φ hball hc⟩
  exact h.trans (SphereSelfIntersections.unorderedParity_zero_of_injective _
    (injective_chartLeft Φ hball))

include r hc in
theorem immersedSphereFrameParity_referenceRight :
    e.immersedSphereFrameParity ν (chartRight Φ hball) (contMDiff_chart_right Φ hball)
      (injective_mfderiv_chartRight Φ hball) = 0 := by
  have h := e.immersedSphereFrameParity_eq_unordered_of_nullhomotopic ν r (chartRight Φ hball)
    (contMDiff_chart_right Φ hball) (injective_mfderiv_chartRight Φ hball)
    (chartRight_selfTransverse Φ hball) (Φ 0) ⟨rightContraction Φ hball hc⟩
  exact h.trans (SphereSelfIntersections.unorderedParity_zero_of_injective _
    (injective_chartRight Φ hball))

include r hc in
theorem reference_inputs_derivativeParity_sum_zero :
    e.sphereDerivativeParity ν (chartLeft Φ hball) (contMDiff_chart_left Φ hball)
        (injective_mfderiv_chartLeft Φ hball) +
      e.sphereDerivativeParity ν (chartRight Φ hball) (contMDiff_chart_right Φ hball)
        (injective_mfderiv_chartRight Φ hball) = 0 := by
  have h := e.immersedSphereFrameParity_sum_eq_derivativeParity ν
    (chartLeft Φ hball) (chartRight Φ hball)
    (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball)
    (injective_mfderiv_chartLeft Φ hball) (injective_mfderiv_chartRight Φ hball)
  rw [e.immersedSphereFrameParity_referenceLeft ν r Φ hball hc,
    e.immersedSphereFrameParity_referenceRight ν r Φ hball hc, add_zero] at h
  exact h.symm

variable (Γ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Ioc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Γ.source)
  (hleft : ∀ v, (v, 0) ∈ Γ.source → Γ (v, 0) = chartLeft Φ hball (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Γ.source → Γ (0, v) = chartRight Φ hball (sourceChart v))
  (hclean : ∀ q ∈ Γ.source,
    (∀ x, chartLeft Φ hball x = Γ q ↔ q.2 = 0 ∧ x = sourceChart q.1) ∧
    (∀ x, chartRight Φ hball x = Γ q ↔ q.1 = 0 ∧ x = sourceChart q.2))
  (hΓ : Γ.target ⊆ Φ.target)

include r hc hclean hΓ in
theorem immersedSphereFrameParity_referenceResolution :
    e.immersedSphereFrameParity ν (resolution Φ hball Γ hε ha hprod hleft hright)
      (contMDiff_resolution Φ hball Γ hε ha hprod hleft hright)
      (injective_mfderiv_resolution Φ hball Γ hε ha hprod hleft hright) = 1 := by
  have h := e.immersedSphereFrameParity_eq_unordered_of_nullhomotopic ν r
    (resolution Φ hball Γ hε ha hprod hleft hright)
    (contMDiff_resolution Φ hball Γ hε ha hprod hleft hright)
    (injective_mfderiv_resolution Φ hball Γ hε ha hprod hleft hright)
    (selfTransverse_resolution Φ hball Γ hε ha hprod hleft hright hclean) (Φ 0)
    ⟨resolutionContraction Φ hball Γ hε ha hprod hleft hright hc hΓ⟩
  exact h.trans (unorderedParity_resolution Φ hball Γ hε ha hprod hleft hright hclean)

include r hc hclean hΓ in
theorem reference_resolution_derivativeParity_eq_whitney :
    e.sphereDerivativeParity ν (resolution Φ hball Γ hε ha hprod hleft hright)
        (contMDiff_resolution Φ hball Γ hε ha hprod hleft hright)
        (injective_mfderiv_resolution Φ hball Γ hε ha hprod hleft hright) =
      e.sphereDerivativeParity ν (WhitneySphere.chartMap Φ)
        (WhitneySphere.contMDiff_chartMap Φ (unitProduct_subset_source Φ hball))
        (WhitneySphere.injective_mfderiv_chartMap Φ (unitProduct_subset_source Φ hball)) := by
  have h := e.immersedSphereFrameParity_sum_eq_derivativeParity ν
    (resolution Φ hball Γ hε ha hprod hleft hright) (WhitneySphere.chartMap Φ)
    (contMDiff_resolution Φ hball Γ hε ha hprod hleft hright)
    (WhitneySphere.contMDiff_chartMap Φ (unitProduct_subset_source Φ hball))
    (injective_mfderiv_resolution Φ hball Γ hε ha hprod hleft hright)
    (WhitneySphere.injective_mfderiv_chartMap Φ (unitProduct_subset_source Φ hball))
  rw [e.immersedSphereFrameParity_referenceResolution ν r Φ hball hc Γ
    hε ha hprod hleft hright hclean hΓ,
    e.immersedSphereFrameParity_whitney ν r Φ (unitProduct_subset_source Φ hball),
    ZModModule.add_self] at h
  exact (eq_neg_of_add_eq_zero_left h.symm).trans (ZMod.neg_eq_self_mod_two _)

include r hc hclean hΓ in
theorem reference_tangentRemainder_parity_eq_whitney :
    Monomorphism.sphereParityOfDimension 1 rfl rfl
        (e.tangentResolutionFrameRemainder ν Γ (chartLeft Φ hball) (chartRight Φ hball)
          hε ha hprod hleft hright (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball)
          (injective_mfderiv_chartLeft Φ hball) (injective_mfderiv_chartRight Φ hball)) =
      e.sphereDerivativeParity ν (WhitneySphere.chartMap Φ)
        (WhitneySphere.contMDiff_chartMap Φ (unitProduct_subset_source Φ hball))
        (WhitneySphere.injective_mfderiv_chartMap Φ (unitProduct_subset_source Φ hball)) := by
  have h := e.resolutionFrameParity_tangent_decomposition ν Γ
    (chartLeft Φ hball) (chartRight Φ hball) hε ha hprod hleft hright
    (contMDiff_chart_left Φ hball) (contMDiff_chart_right Φ hball)
    (injective_mfderiv_chartLeft Φ hball) (injective_mfderiv_chartRight Φ hball)
  rw [e.reference_inputs_derivativeParity_sum_zero ν r Φ hball hc, zero_add] at h
  exact h.symm.trans (e.reference_resolution_derivativeParity_eq_whitney ν r Φ hball hc Γ
    hε ha hprod hleft hright hclean hΓ)

end EuclideanEmbedding

end NoExoticSixSphere
