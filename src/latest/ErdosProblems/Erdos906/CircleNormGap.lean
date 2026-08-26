import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.MeasureTheory.Integral.CircleAverage

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Complex Function MeasureTheory Metric Real Set

namespace CofiniteDerivatives

/-- The excess of the circular average of the norm over the norm at the center. -/
noncomputable def normCircleGap (c : ℂ) (r : ℝ) : ℝ :=
  circleAverage (fun z : ℂ ↦ ‖z‖) c r - ‖c‖

/-- The norm pulled back along a parametrized circle is continuous. -/
theorem continuous_norm_circleMap (c : ℂ) (r : ℝ) :
    Continuous (fun θ : ℝ ↦ ‖circleMap c r θ‖) :=
  continuous_norm.comp (continuous_circleMap c r)

/-- The norm pulled back along a parametrized circle is measurable. -/
theorem measurable_norm_circleMap (c : ℂ) (r : ℝ) :
    Measurable (fun θ : ℝ ↦ ‖circleMap c r θ‖) :=
  (continuous_norm_circleMap c r).measurable

/-- The norm is integrable on every parametrized circle. -/
theorem circleIntegrable_norm (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z : ℂ ↦ ‖z‖) c r :=
  continuous_norm.continuousOn.circleIntegrable'

/-- Multiplying the norm by a real scalar commutes with circular averaging. -/
theorem circleAverage_mul_norm (a : ℝ) (c : ℂ) (r : ℝ) :
    circleAverage (fun z : ℂ ↦ a * ‖z‖) c r =
      a * circleAverage (fun z : ℂ ↦ ‖z‖) c r := by
  simpa only [smul_eq_mul] using!
    (circleAverage_fun_smul (a := a) (f := fun z : ℂ ↦ ‖z‖) (c := c) (R := r))

/-- The centered circular norm statistic commutes with multiplication by a scalar. -/
theorem circleAverage_mul_norm_sub (a : ℝ) (c : ℂ) (r : ℝ) :
    circleAverage (fun z : ℂ ↦ a * ‖z‖) c r - a * ‖c‖ =
      a * normCircleGap c r := by
  rw [circleAverage_mul_norm]
  simp only [normCircleGap]
  ring

private theorem circleMap_add_antipode (c : ℂ) (r θ : ℝ) :
    circleMap c r θ + circleMap c r (θ + π) = 2 * c := by
  simp [circleMap, add_mul, Complex.exp_add]
  ring

private theorem norm_antipodal_pair_le (c : ℂ) (r θ : ℝ) :
    2 * ‖c‖ ≤ ‖circleMap c r θ‖ + ‖circleMap c r (θ + π)‖ := by
  calc
    2 * ‖c‖ = ‖(2 : ℂ) * c‖ := by simp
    _ = ‖circleMap c r θ + circleMap c r (θ + π)‖ := by
      rw [circleMap_add_antipode]
    _ ≤ ‖circleMap c r θ‖ + ‖circleMap c r (θ + π)‖ := norm_add_le _ _

private theorem exists_norm_antipodal_pair_lt (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ∃ θ ∈ Icc 0 (2 * π),
      2 * ‖c‖ < ‖circleMap c r θ‖ + ‖circleMap c r (θ + π)‖ := by
  by_cases hc : c = 0
  · refine ⟨0, ⟨le_rfl, Real.two_pi_pos.le⟩, ?_⟩
    subst c
    simpa [circleMap, abs_of_pos hr] using!
      (mul_pos (show (0 : ℝ) < 2 by norm_num) hr)
  · let u : ℂ := (r / ‖c‖ : ℝ) * I * c
    have hu_norm : ‖u‖ = r := by
      simp [u, abs_of_pos hr, hc]
    have hu_mem : u ∈ sphere (0 : ℂ) |r| := by
      simp [hu_norm, abs_of_pos hr]
    rw [← image_circleMap_Ioc] at hu_mem
    obtain ⟨θ, hθ, hcircle⟩ := hu_mem
    refine ⟨θ, ⟨hθ.1.le, hθ.2⟩, ?_⟩
    let x := circleMap c r θ
    let y := circleMap c r (θ + π)
    have hx : x = c + u := by
      calc
        x = c + circleMap 0 r θ := by simp [x, circleMap]
        _ = c + u := by rw [hcircle]
    have hy : y = c - u := by
      have hantipode : circleMap 0 r (θ + π) = -circleMap 0 r θ := by
        simp [circleMap, add_mul, Complex.exp_add]
      calc
        y = c + circleMap 0 r (θ + π) := by simp [y, circleMap]
        _ = c - u := by rw [hantipode, hcircle]; ring
    let a : ℝ := r / ‖c‖
    have hx_factor : x = (1 + (a : ℂ) * I) * c := by
      rw [hx]
      simp only [u, a]
      push_cast
      ring
    have hy_factor : y = (1 - (a : ℂ) * I) * c := by
      rw [hy]
      simp only [u, a]
      push_cast
      ring
    have hfactor_norm : ‖(1 : ℂ) + (a : ℂ) * I‖ = ‖(1 : ℂ) - (a : ℂ) * I‖ := by
      rw [Complex.norm_def, Complex.norm_def]
      congr 1
      simp [Complex.normSq_apply]
    have hnorm : ‖x‖ = ‖y‖ := by
      rw [hx_factor, hy_factor, norm_mul, norm_mul, hfactor_norm]
    have hxy_ne : x ≠ y := by
      rw [hx, hy]
      intro h
      have : u = 0 := by linear_combination h / 2
      exact hr.ne' (hu_norm ▸ norm_eq_zero.mpr this)
    have hstrict : ‖x + y‖ < ‖x‖ + ‖y‖ := by
      apply lt_of_le_of_ne (norm_add_le x y)
      intro hEq
      exact hxy_ne (eq_of_norm_eq_of_norm_add_eq hnorm hEq)
    have hsum : x + y = 2 * c := by
      exact circleMap_add_antipode c r θ
    rw [hsum, norm_mul, Complex.norm_ofNat] at hstrict
    exact hstrict

/-- The circular average of the norm is strictly larger than the norm at the center when the
radius is positive. -/
theorem normCircleGap_pos (c : ℂ) {r : ℝ} (hr : 0 < r) : 0 < normCircleGap c r := by
  let f : ℝ → ℝ := fun θ ↦ ‖circleMap c r θ‖
  let g : ℝ → ℝ := fun θ ↦ f θ + f (θ + π)
  have hf_cont : Continuous f := continuous_norm_circleMap c r
  have hg_cont : Continuous g := hf_cont.add (hf_cont.comp (continuous_id.add continuous_const))
  have hconst_lt :
      (∫ _θ : ℝ in 0..2 * π, 2 * ‖c‖) < ∫ θ : ℝ in 0..2 * π, g θ := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      Real.two_pi_pos continuousOn_const hg_cont.continuousOn
    · intro θ _
      exact norm_antipodal_pair_le c r θ
    · simpa only [g, f] using! exists_norm_antipodal_pair_lt c r hr
  have hf_periodic : Periodic f (2 * π) := fun θ ↦ by
    simp only [f, periodic_circleMap c r θ]
  have hshift : (∫ θ : ℝ in 0..2 * π, f (θ + π)) = ∫ θ : ℝ in 0..2 * π, f θ := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa [add_assoc, add_comm, add_left_comm] using!
      hf_periodic.intervalIntegral_add_eq π 0
  have hf_int : IntervalIntegrable f volume 0 (2 * π) :=
    hf_cont.intervalIntegrable _ _
  have hshift_int : IntervalIntegrable (fun θ ↦ f (θ + π)) volume 0 (2 * π) :=
    (hf_cont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hg_integral :
      (∫ θ : ℝ in 0..2 * π, g θ) =
        (∫ θ : ℝ in 0..2 * π, f θ) + ∫ θ : ℝ in 0..2 * π, f (θ + π) := by
    dsimp only [g]
    exact intervalIntegral.integral_add hf_int hshift_int
  have hintegral_lt : (2 * π) * (2 * ‖c‖) < 2 * ∫ θ : ℝ in 0..2 * π, f θ := by
    calc
      (2 * π) * (2 * ‖c‖) = ∫ _θ : ℝ in 0..2 * π, 2 * ‖c‖ := by
        simp [smul_eq_mul]
        ring
      _ < ∫ θ : ℝ in 0..2 * π, g θ := hconst_lt
      _ = (∫ θ : ℝ in 0..2 * π, f θ) + ∫ θ : ℝ in 0..2 * π, f θ := by
        rw [hg_integral, hshift]
      _ = 2 * ∫ θ : ℝ in 0..2 * π, f θ := by ring
  have hbase_lt :
      (2 * π) * ‖c‖ < ∫ θ : ℝ in 0..2 * π, f θ := by
    nlinarith [hintegral_lt]
  rw [normCircleGap, circleAverage_def, smul_eq_mul, sub_pos]
  change ‖c‖ < (2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, f θ
  calc
    ‖c‖ = (2 * π)⁻¹ * ((2 * π) * ‖c‖) := by
      field_simp [ne_of_gt Real.two_pi_pos]
    _ < (2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, f θ :=
      mul_lt_mul_of_pos_left hbase_lt (inv_pos.mpr Real.two_pi_pos)

/-- A positive square-root factor preserves positivity of the norm circle gap. -/
theorem sqrt_mul_normCircleGap_pos (c : ℂ) {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    0 < √x * normCircleGap c r :=
  mul_pos (Real.sqrt_pos.2 hx) (normCircleGap_pos c hr)

/-- Natural-number specialization of `circleAverage_mul_norm_sub`. -/
theorem circleAverage_sqrt_nat_mul_norm_sub (n : ℕ) (c : ℂ) (r : ℝ) :
    circleAverage (fun z : ℂ ↦ √(n : ℝ) * ‖z‖) c r - √(n : ℝ) * ‖c‖ =
      √(n : ℝ) * normCircleGap c r :=
  circleAverage_mul_norm_sub _ c r

/-- Multiplication by `sqrt n` preserves strict positivity for nonzero natural `n`. -/
theorem sqrt_nat_mul_normCircleGap_pos {n : ℕ} (hn : n ≠ 0) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    0 < √(n : ℝ) * normCircleGap c r :=
  sqrt_mul_normCircleGap_pos c hr (by exact_mod_cast Nat.pos_of_ne_zero hn)

end CofiniteDerivatives
