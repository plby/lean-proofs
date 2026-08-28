import Wikipedia.NoExoticSixSphere.RankSixHemisphereSpinor
import Wikipedia.NoExoticSixSphere.RankSixSpinorPhase
import Wikipedia.NoExoticSixSphere.ContinuousProjectionHomotopy
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Unit spinor sections along intervals and loops

Continuous projection transport gives a nonzero section along an interval.
After normalization, a circle phase corrects its endpoint to close whenever
the original complex-structure path closes.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.RankSixComplexProjection

theorem exists_interval_unitSection (J : C(I, OrthogonalComplexStructures.Space 6)) :
    ∃ q : C(I, UnitSpinor), ∀ t, projection (J t) (q t) = (q t : Spinor) := by
  let P (s t : I) : Spinor →L[ℝ] Spinor := realProjection (J (s * t))
  have hP : ∀ s t, IsIdempotentElem (P s t) := fun s t ↦ realProjection_idempotent _
  have hc : Continuous (fun z : I × I ↦ P z.1 z.2) :=
    continuous_realProjection.comp (J.continuous.comp continuous_mul)
  obtain ⟨R⟩ := nonempty_continuousRangeTransport_of_homotopy P hP hc 0 1
  obtain ⟨v, hv, hfix⟩ := exists_nonzero_fixed (J 0)
  let w (t : I) : Spinor := R.toFun t v
  have hw : Continuous w := R.continuous.clm_apply continuous_const
  have hne (t : I) : w t ≠ 0 := by
    intro he
    apply hv
    apply (R.invertible t).injective
    exact he.trans (map_zero _).symm
  have hf (t : I) : projection (J t) (w t) = w t := by
    have ht := congrArg (fun T : Spinor →L[ℝ] Spinor ↦ T v) (R.intertwines t)
    change projection (J (1 * t)) (w t) = R.toFun t (projection (J (0 * t)) v) at ht
    simpa only [one_mul, zero_mul, hfix] using ht
  let q : C(I, UnitSpinor) := {
    toFun t := ⟨NormedSpace.normalize (w t), by
      simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize (hne t)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (hw.norm.inv₀ (fun t ↦ norm_ne_zero_iff.mpr (hne t))).smul hw }
  refine ⟨q, fun t ↦ ?_⟩
  change realProjection (J t) (‖w t‖⁻¹ • w t) = ‖w t‖⁻¹ • w t
  rw [map_smul]
  exact congrArg (fun v : Spinor ↦ ‖w t‖⁻¹ • v) (hf t)

theorem phaseSmul_one (q : UnitSpinor) : phaseSmul 1 q = q := by
  apply Subtype.ext
  exact one_smul ℂ (q : Spinor)

theorem exists_closed_interval_unitSection (J : C(I, OrthogonalComplexStructures.Space 6))
    (hJ : J 1 = J 0) :
    ∃ q : C(I, UnitSpinor), (∀ t, projection (J t) (q t) = (q t : Spinor)) ∧ q 1 = q 0 := by
  obtain ⟨q, hq⟩ := exists_interval_unitSection J
  have hq₁ : projection (J 0) (q 1) = (q 1 : Spinor) := by rw [← hJ]; exact hq 1
  let c := unitPhase (J 0) (q 0) (q 1) (hq 0) hq₁
  let a : C(I, Circle) :=
    ⟨fun t ↦ Circle.exp ((t : ℝ) * Complex.arg c), by fun_prop⟩
  have ha₀ : a 0 = 1 := by change Circle.exp ((0 : ℝ) * Complex.arg c) = 1; simp
  have ha₁ : a 1 = c := by
    change Circle.exp ((1 : ℝ) * Complex.arg c) = c
    rw [one_mul, Circle.exp_arg]
  let r : C(I, UnitSpinor) := ⟨fun t ↦ phaseSmul (a t) (q t),
    continuous_phaseSmul.comp (a.continuous.prodMk q.continuous)⟩
  refine ⟨r, fun t ↦ phaseSmul_fixed (J t) (q t) (hq t) (a t), ?_⟩
  change phaseSmul (a 1) (q 1) = phaseSmul (a 0) (q 0)
  rw [ha₀, ha₁, phaseSmul_one]
  exact unitPhase_smul (J 0) (q 0) (q 1) (hq 0) hq₁

end NoExoticSixSphere.RankSixComplexProjection
