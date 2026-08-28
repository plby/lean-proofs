import Wikipedia.HopfProblem.DegreeCollapsePassageDerivativeClass
import Wikipedia.HopfProblem.DegreeCollapseNormalDeterminantCorrection

/-!
# Normal frame changes reverse the actual attaching contribution

Positive longitudinal rates do not affect the sign. A negative determinant
in the chosen terminal sheet factor reverses the contribution even when
the two rates differ, and the shared source and target frames are arbitrary.
-/

noncomputable section

open Set Function Metric ContinuousMap
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)

variable {U N : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

def passageNormalProduct (c : ℝ) (hc : c ≠ 0) (C : U ≃L[ℝ] U) :
    (ℝ × U) ≃L[ℝ] (ℝ × U) :=
  (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv.prodCongr C

theorem passageNormalProduct_det (c : ℝ) (hc : c ≠ 0) (C : U ≃L[ℝ] U) :
    (passageNormalProduct c hc C).toLinearMap.det = c * C.toLinearMap.det := by
  have hscale : (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toLinearMap =
      c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    ext x
    rfl
  change LinearMap.det ((LinearEquiv.smulOfNeZero ℝ ℝ c hc).toLinearMap.prodMap
    C.toLinearMap) = _
  rw [LinearMap.det_prodMap, hscale, LinearMap.det_smul, Module.finrank_self,
    pow_one, LinearMap.det_id, mul_one]

theorem relative_normal_frame_det
    (P : P₃ ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N)
    (Q₀ Q₁ : (ℝ × U) ≃L[ℝ] (ℝ × U)) :
    (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap.det =
      Q₀.toLinearMap.det⁻¹ * Q₁.toLinearMap.det := by
  have heq : (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap =
      P.symm.toLinearMap.comp ((Q₀.symm.toLinearMap.comp Q₁.toLinearMap).comp
        P.toLinearMap) := by
    apply LinearMap.ext
    intro z
    change P.symm (Q₀.symm (B.symm (B (Q₁ (P z))))) = P.symm (Q₀.symm (Q₁ (P z)))
    rw [B.symm_apply_apply]
  rw [heq]
  have hconj := LinearMap.det_conj (Q₀.symm.toLinearMap.comp Q₁.toLinearMap) P.symm.toLinearEquiv
  calc
    _ = (Q₀.symm.toLinearMap.comp Q₁.toLinearMap).det := hconj
    _ = _ := by
      rw [LinearMap.det_comp]
      exact congrArg (fun t : ℝ => t * Q₁.toLinearMap.det)
        (LinearEquiv.det_coe_symm Q₀.toLinearEquiv)

theorem passage_normal_relative_det_neg
    (P : P₃ ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (C : U ≃L[ℝ] U) (hC : C.toLinearMap.det < 0) :
    (((P.trans (passageNormalProduct c₁ hc₁.ne' C)).trans B).trans
      ((P.trans (passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ U))).trans B).symm).toLinearMap.det < 0 := by
  rw [relative_normal_frame_det, passageNormalProduct_det, passageNormalProduct_det]
  change (c₀ * (LinearMap.id : U →ₗ[ℝ] U).det)⁻¹ * (c₁ * C.toLinearMap.det) < 0
  rw [LinearMap.det_id, mul_one]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hc₀) (mul_neg_of_pos_of_neg hc₁ hC)

theorem passage_normal_contributions_opposite
    {Y : Type} [TopologicalSpace Y] (a : C(sphere (0 : N) 1, Y))
    (P : P₃ ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N)
    {c₀ c₁ : ℝ} (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (C : U ≃L[ℝ] U) (hC : C.toLinearMap.det < 0) :
    let L₀ := (P.trans (passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ U))).trans B
    let L₁ := (P.trans (passageNormalProduct c₁ hc₁.ne' C)).trans B
    singularHomologyMap
      (a.comp (LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective)) 2 =
      -singularHomologyMap
        (a.comp (LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective)) 2 := by
  dsimp only
  exact attaching_contributions_opposite_of_relative_det_neg a _ _
    (passage_normal_relative_det_neg P B hc₀ hc₁ C hC)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
