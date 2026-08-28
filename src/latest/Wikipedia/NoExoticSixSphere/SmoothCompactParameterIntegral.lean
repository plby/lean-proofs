import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Smooth compact parameter integrals

Joint smoothness gives a uniform derivative bound on a compact parameter
interval and a compact source neighborhood. Differentiation under the actual
Bochner integral is therefore justified. Iterating this argument proves
smoothness without assuming differentiability of the integral.
-/

noncomputable section

open Set Function Filter MeasureTheory
open scoped ContDiff Topology

namespace NoExoticSixSphere.CompactParameterIntegral

variable {X F : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem hasFDerivAt_setIntegral (f : X × ℝ → F) (g : X × ℝ → X →L[ℝ] F)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x t, HasFDerivAt (fun y ↦ f (y, t)) (g (x, t)) x) (a b : ℝ) (x : X) :
    HasFDerivAt (fun y ↦ ∫ t in Icc a b, f (y, t))
      (∫ t in Icc a b, g (x, t)) x := by
  have hcompact : IsCompact (Metric.closedBall x 1 ×ˢ Icc a b) :=
    (isCompact_closedBall x 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall x 1) (bound := fun _ : ℝ ↦ C)
    (Metric.closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall fun y ↦
      (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hf.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
      isCompact_Icc
  · exact (hg.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro y hy
    exact hC (y, t) ⟨hy, ht⟩
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · exact Eventually.of_forall fun t y _ ↦ hfg y t

theorem contDiff_setIntegral_nat (a b : ℝ) (n : ℕ) :
    ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : X × ℝ → F), ContDiff ℝ ∞ f →
        ContDiff ℝ n (fun x ↦ ∫ t in Icc a b, f (x, t)) := by
  induction n with
  | zero =>
      intro F _ _ _ f hf
      apply contDiff_zero.mpr
      exact continuous_parametric_integral_of_continuous
        (f := fun x t ↦ f (x, t)) hf.continuous isCompact_Icc
  | succ n ih =>
      intro F _ _ _ f hf
      let g : X × ℝ → X →L[ℝ] F := fun q ↦
        (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ X ℝ)
      have hg : ContDiff ℝ ∞ g := (hf.fderiv_right (by simp)).clm_comp contDiff_const
      have hfg (x : X) (t : ℝ) : HasFDerivAt (fun y ↦ f (y, t)) (g (x, t)) x :=
        ((hf.differentiable (by simp) (x, t)).hasFDerivAt).comp x
          (hasFDerivAt_prodMk_left x t)
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x ↦ ∫ t in Icc a b, g (x, t), ih (X →L[ℝ] F) g hg, ?_⟩
      exact fun x ↦ hasFDerivAt_setIntegral f g hf.continuous hg.continuous hfg a b x

theorem contDiff_setIntegral (f : X × ℝ → F) (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in Icc a b, f (x, t)) :=
  contDiff_infty.mpr fun n ↦ contDiff_setIntegral_nat a b n F f hf

theorem contDiff_intervalIntegral (f : X × ℝ → F) (hf : ContDiff ℝ ∞ f)
    (a b : ℝ) (hab : a ≤ b) :
    ContDiff ℝ ∞ (fun x ↦ ∫ t in a..b, f (x, t)) := by
  have he : (fun x ↦ ∫ t in a..b, f (x, t)) =
      fun x ↦ ∫ t in Icc a b, f (x, t) := by
    funext x
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  rw [he]
  exact contDiff_setIntegral f hf a b

end NoExoticSixSphere.CompactParameterIntegral
