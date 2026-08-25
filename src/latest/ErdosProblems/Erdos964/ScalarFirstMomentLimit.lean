import ErdosProblems.Erdos964.ScalarFirstMomentError
import ErdosProblems.Erdos964.ScalarTransformRounding

/-!
# The limit of the concrete first scalar main term
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem tendsto_log_pred_div_log :
    Tendsto (fun R : ℕ => Real.log (R - 1 : ℕ) / Real.log R) atTop (𝓝 1) := by
  have hlog : Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hbound : ∀ᶠ R : ℕ in atTop,
      ‖Real.log (R - 1 : ℕ) / Real.log R - 1‖ ≤ Real.log 2 / Real.log R := by
    filter_upwards [eventually_ge_atTop 2] with R hR
    have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
    have hb := scalar_transform_log_endpoint_bounds R 1 (by decide) (by omega)
    simp only [Nat.div_one, Nat.cast_one, Real.log_one, sub_zero] at hb
    have hid : Real.log (R - 1 : ℕ) / Real.log R - 1 =
        (Real.log (R - 1 : ℕ) - Real.log R) / Real.log R := by field_simp
    rw [Real.norm_eq_abs, hid, abs_div, abs_of_pos hL,
      abs_of_nonpos (sub_nonpos.mpr hb.2.1)]
    exact div_le_div_of_nonneg_right (by linarith [hb.2.2.2]) hL.le
  exact squeeze_zero' (Eventually.of_forall (fun R => norm_nonneg _)) hbound
    (hlog.const_div_atTop (Real.log 2))

theorem tendsto_scalarCandidateFirstMain (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    Tendsto (fun R : ℕ => scalarCandidateFirstMain M R / (Real.log R) ^ 3) atTop
      (𝓝 ((scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3) * (19 / 15))) := by
  let A := scalarSieveEulerConstant M * coprimeHarmonicDensity M ^ 3
  let G : ℕ → ℝ := fun R => A * scalarFirstMomentPolynomial (Real.log (R - 1 : ℕ) / Real.log R)
  have hlog : Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hG : Tendsto G atTop (𝓝 (A * (19 / 15))) := by
    have hcont : Continuous scalarFirstMomentPolynomial := by
      unfold scalarFirstMomentPolynomial
      fun_prop
    have h := (hcont.continuousAt.tendsto.comp tendsto_log_pred_div_log).const_mul A
    simpa only [scalarFirstMomentPolynomial_one, G, Function.comp_apply] using h
  have herror : Tendsto (fun R : ℕ =>
      scalarCandidateFirstMain M R / (Real.log R) ^ 3 - G R) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    rw [Metric.tendsto_nhds]
    intro δ hδ
    let ε := δ / 676
    have hε : 0 < ε := by dsimp only [ε]; positivity
    obtain ⟨C, hC, hbound⟩ := exists_scalarCandidateFirstMain_polynomial_error M hM h2M h3M ε hε
    have htail : Tendsto (fun R : ℕ => 338 * C / (Real.log R) ^ 3) atTop (𝓝 0) :=
      ((tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp hlog).const_div_atTop (338 * C)
    have hsmall := (tendsto_order.mp htail).2 (δ / 2) (by linarith)
    filter_upwards [eventually_ge_atTop 2, hsmall] with R hR hsmallR
    have hL : 0 < Real.log R := Real.log_pos (by exact_mod_cast (show 1 < R by omega))
    have hid : scalarCandidateFirstMain M R / (Real.log R) ^ 3 - G R =
        (scalarCandidateFirstMain M R - A * (Real.log R) ^ 3 *
          scalarFirstMomentPolynomial (Real.log (R - 1 : ℕ) / Real.log R)) / (Real.log R) ^ 3 := by
      dsimp only [G]
      field_simp
    have hnorm : ‖scalarCandidateFirstMain M R / (Real.log R) ^ 3 - G R‖ ≤
        338 * ε + 338 * C / (Real.log R) ^ 3 := by
      rw [Real.norm_eq_abs, hid, abs_div, abs_of_pos (pow_pos hL 3)]
      calc
        _ ≤ 338 * (ε * (Real.log R) ^ 3 + C) / (Real.log R) ^ 3 :=
          div_le_div_of_nonneg_right (hbound R hR) (by positivity)
        _ = _ := by field_simp
    simp only [sub_zero, Real.dist_eq, Real.norm_eq_abs, abs_abs]
    have hfinal : ‖scalarCandidateFirstMain M R / (Real.log R) ^ 3 - G R‖ < δ := by
      dsimp only [ε] at hnorm
      linarith
    simpa only [Real.norm_eq_abs] using hfinal
  have h := herror.add hG
  simp only [zero_add] at h
  apply h.congr'
  exact Eventually.of_forall (fun R => by ring)

end Erdos964
