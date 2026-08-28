import Wikipedia.NoExoticSixSphere.GenericLocalContribution
import Wikipedia.NoExoticSixSphere.SmoothCurveExtension
import Wikipedia.NoExoticSixSphere.ResidualBallChart

/-!
# Actual local parity contributions inside a prescribed open domain

The ball stays in the original domain of smoothness. Its boundary operators
are the original operators, not a substitute family. A smooth representative
is used only on a neighborhood where it agrees exactly with the original map;
the residual chart and its ball are constructed inside that neighborhood.
-/

noncomputable section

open Set Function Metric Topology Filter
open scoped ContDiff Manifold

namespace NoExoticSixSphere.GenericLocalParity

open GLOrthonormalization CorankOne CorankOneCoordinates OperatorRank Stiefel

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def HasLocalContributionOn (D : X → Vector 3 →L[ℝ] Vector 6) (U : Set X) (x : X) : Prop :=
  ∃ b : Vector 4 → X, b 0 = x ∧
    MapsTo b (closedBall (0 : Vector 4) 1) U ∧
    ContDiffOn ℝ ∞ b (closedBall (0 : Vector 4) 1) ∧
    IsClosedEmbedding (fun z : closedBall (0 : Vector 4) 1 ↦ b z.val) ∧
    (∀ z ∈ closedBall (0 : Vector 4) 1, ¬ Injective (D (b z)) ↔ z = 0) ∧
    ∃ F : C(Sphere 3, Monomorphism.Space 6 3),
      (∀ s, (F s).val = D (b s.val)) ∧ Monomorphism.sphereParity 1 F = 1

def HasChartedLocalContributionOn (D : X → Vector 3 →L[ℝ] Vector 6)
    (U : Set X) (x : X) : Prop :=
  ∃ b : PartialDiffeomorph (𝓡 4) 𝓘(ℝ, X) (Vector 4) X ∞,
    closedBall (0 : Vector 4) 1 ⊆ b.source ∧ b 0 = x ∧
    MapsTo b (closedBall (0 : Vector 4) 1) U ∧
    (∀ z ∈ closedBall (0 : Vector 4) 1, ¬ Injective (D (b z)) ↔ z = 0) ∧
    ∃ F : C(Sphere 3, Monomorphism.Space 6 3),
      (∀ s, (F s).val = D (b s.val)) ∧ Monomorphism.sphereParity 1 F = 1

theorem hasChartedLocalContributionOn_of_regular_residual [FiniteDimensional ℝ X]
    (D : X → Vector 3 →L[ℝ] Vector 6) {U : Set X} (hU : IsOpen U)
    (hD : ContDiffOn ℝ ∞ D U) (x : X) (hx : x ∈ U)
    (hres : ∃ c : RankTwoCoordinates (Vector 3) (Vector 6),
      D x ∈ domain c ∧ residual (operatorEquiv c (D x)) = 0 ∧
      Bijective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)) :
    HasChartedLocalContributionOn D U x := by
  obtain ⟨G, hG, he⟩ := SmoothCurveExtension.exists_global hU hx hD
  obtain ⟨N, hN, hNopen, hxN⟩ := _root_.mem_nhds_iff.mp (he.and (hU.mem_nhds hx))
  have hND (y : X) (hy : y ∈ N) : G y = D y := (hN hy).1
  have hNU : N ⊆ U := fun _ hy ↦ (hN hy).2
  have he₀ := he.eq_of_nhds
  obtain ⟨c, hc, hz, hb⟩ := hres
  have hR : (fun y ↦ residual (operatorEquiv c (G y))) =ᶠ[𝓝 x]
      (fun y ↦ residual (operatorEquiv c (D y))) := by
    filter_upwards [he] with y hy
    rw [hy]
  have hGc : inCoordinates c G x ∈ chart := by
    change operatorEquiv c (G x) ∈ chart
    rw [he₀]
    exact hc
  have hzero : residual (inCoordinates c G x) = 0 := by
    change residual (operatorEquiv c (G x)) = 0
    rw [he₀]
    exact hz
  obtain ⟨d, hdx, hdN⟩ := ResidualCoordinates.exists_data_on (inCoordinates c G) hNopen
    (contDiff_inCoordinates c G hG).contDiffOn x hxN hGc
      ((hR.fderiv_eq (𝕜 := ℝ)).symm ▸ hb)
  obtain ⟨ε, hε, hball⟩ := d.exists_radius hdx hzero
  have hmem (z : Vector 4) (hz : z ∈ closedBall (0 : Vector 4) 1) :
      d.ballMap ε z ∈ N := hdN (d.ballMap_mem_source hε hball hz)
  refine ⟨d.ballChart ε hε, d.closedBall_subset_ballChart_source hε hball,
    d.ballMap_zero ε hdx hzero, fun z hz ↦ hNU (hmem z hz), ?_,
    originalLink c G d hG.continuous hε hball, ?_,
    originalLink_parity c G d hG.continuous hε hball⟩
  · intro z hz
    change ¬ Injective (D (d.ballMap ε z)) ↔ z = 0
    rw [← hND _ (hmem z hz)]
    exact ((injective_operatorEquiv_iff c (G (d.ballMap ε z))).not).symm.trans
      (d.singular_ballMap_iff hε hball hz)
  · intro s
    exact hND (d.link ε s) (hdN (d.link_mem_source hε hball s))

theorem HasChartedLocalContributionOn.to_local {D : X → Vector 3 →L[ℝ] Vector 6}
    {U : Set X} {x : X} (h : HasChartedLocalContributionOn D U x) :
    HasLocalContributionOn D U x := by
  obtain ⟨b, hball, hcenter, hU, hsing, F, hF, hparity⟩ := h
  have hbs : ContDiffOn ℝ ∞ b (closedBall (0 : Vector 4) 1) :=
    b.contMDiffOn_toFun.contDiffOn.mono hball
  have hbe : IsClosedEmbedding (fun z : closedBall (0 : Vector 4) 1 ↦ b z.val) := by
    apply hbs.continuousOn.domRestrict.isClosedEmbedding
    intro z w he
    exact Subtype.ext (b.injOn (hball z.property) (hball w.property) he)
  exact ⟨b, hcenter, hU, hbs, hbe, hsing, F, hF, hparity⟩

theorem hasLocalContributionOn_of_regular_residual [FiniteDimensional ℝ X]
    (D : X → Vector 3 →L[ℝ] Vector 6) {U : Set X} (hU : IsOpen U)
    (hD : ContDiffOn ℝ ∞ D U) (x : X) (hx : x ∈ U)
    (hres : ∃ c : RankTwoCoordinates (Vector 3) (Vector 6),
      D x ∈ domain c ∧ residual (operatorEquiv c (D x)) = 0 ∧
      Bijective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y))) x)) :
    HasLocalContributionOn D U x :=
  (hasChartedLocalContributionOn_of_regular_residual D hU hD x hx hres).to_local

end NoExoticSixSphere.GenericLocalParity
