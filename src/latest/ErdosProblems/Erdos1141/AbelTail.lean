import ErdosProblems.Erdos1141.SquareRootAbel

/-!
# Quantitative tails for the square-root Abel continuation
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace Erdos1141

noncomputable def abelPrefix (f : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, f n

noncomputable def abelKernel (f : ℕ → ℂ) (β : ℝ) (y : ℝ) : ℂ :=
  abelPrefix f y * (y : ℂ) ^ (-((β : ℂ) + 1))

lemma measurable_abelPrefix (f : ℕ → ℂ) : Measurable (abelPrefix f) :=
  (measurable_of_countable (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor

lemma measurable_abelKernel (f : ℕ → ℂ) (β : ℝ) : Measurable (abelKernel f β) := by
  unfold abelKernel
  exact (measurable_abelPrefix f).mul (by fun_prop)

lemma norm_abelPrefix_le_sqrt (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ))
    {y : ℝ} (hy : 0 ≤ y) : ‖abelPrefix f y‖ ≤ C * Real.sqrt y :=
  (hprefix ⌊y⌋₊).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (Nat.floor_le hy)) hC)

lemma norm_abelKernel_le (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ))
    (β : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖abelKernel f β y‖ ≤ C * y ^ (-β - 1 / 2) := by
  rw [abelKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  simp only [neg_re, add_re, ofReal_re, one_re]
  calc
    _ ≤ C * Real.sqrt y * y ^ (-(β + 1)) :=
      mul_le_mul_of_nonneg_right (norm_abelPrefix_le_sqrt f C hC hprefix hy.le)
        (Real.rpow_nonneg hy.le _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hy]
      congr 2
      ring

lemma integrableOn_abelKernel (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ))
    {β X : ℝ} (hβ : 1 / 2 < β) (hX : 0 < X) :
    IntegrableOn (abelKernel f β) (Ioi X) := by
  have hmajor : IntegrableOn (fun y : ℝ ↦ C * y ^ (-β - 1 / 2)) (Ioi X) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -β - 1 / 2 < -1) hX).const_mul C
  apply hmajor.mono' (measurable_abelKernel f β).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact norm_abelKernel_le f C hC hprefix β (hX.trans hy)

theorem norm_integral_abelKernel_tail_le (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ))
    {β X : ℝ} (hβ : 1 / 2 < β) (hX : 0 < X) :
    ‖∫ y in Ioi X, abelKernel f β y‖ ≤ C * X ^ (1 / 2 - β) / (β - 1 / 2) := by
  have hactual := integrableOn_abelKernel f C hC hprefix hβ hX
  have hmajor : IntegrableOn (fun y : ℝ ↦ C * y ^ (-β - 1 / 2)) (Ioi X) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -β - 1 / 2 < -1) hX).const_mul C
  calc
    _ ≤ ∫ y in Ioi X, ‖abelKernel f β y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi X, C * y ^ (-β - 1 / 2) := by
      apply setIntegral_mono_ae_restrict hactual.norm hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact norm_abelKernel_le f C hC hprefix β (hX.trans hy)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -β - 1 / 2 < -1) hX]
      rw [show -β - 1 / 2 + 1 = 1 / 2 - β by ring]
      have hneg : 1 / 2 - β = -(β - 1 / 2) := by ring
      rw [hneg, neg_div_neg_eq]
      ring

lemma sum_Icc_zero_eq_one_of_zero (f : ℕ → ℂ) (hf : f 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons, hf, zero_add]
  rw [← Finset.Icc_succ_left_eq_Ioc]
  norm_num

lemma deriv_abelWeight {β y : ℝ} (hβ : 0 < β) (hy : 0 < y) :
    deriv (fun t : ℝ ↦ (t : ℂ) ^ (-(β : ℂ))) y =
      -(β : ℂ) * (y : ℂ) ^ (-((β : ℂ) + 1)) := by
  rw [Complex.deriv_ofReal_cpow_const hy.ne' (neg_ne_zero.mpr (by exact_mod_cast hβ.ne'))]
  congr 2
  ring

lemma abel_prefix_identity (f : ℕ → ℂ) (hf0 : f 0 = 0)
    {β : ℝ} (hβ : 0 < β) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, f n * (n : ℂ) ^ (-(β : ℂ))) =
      (X : ℂ) ^ (-(β : ℂ)) * abelPrefix f X +
        (β : ℂ) * ∫ y in Ioc (1 : ℝ) X, abelKernel f β y := by
  let w : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(β : ℂ))
  have hwdiff : ∀ y ∈ Icc (1 : ℝ) X, DifferentiableAt ℝ w y := by
    intro y hy
    exact (hasDerivAt_ofReal_cpow_const (zero_lt_one.trans_le hy.1).ne'
      (neg_ne_zero.mpr (by exact_mod_cast hβ.ne'))).differentiableAt
  have hwcont : ContinuousOn (fun y : ℝ ↦ -(β : ℂ) * (y : ℂ) ^ (-((β : ℂ) + 1)))
      (Icc (1 : ℝ) X) := by
    apply continuousOn_const.mul
    intro y hy
    exact (Complex.continuousAt_ofReal_cpow_const y _
      (.inr (zero_lt_one.trans_le hy.1).ne')).continuousWithinAt
  have hwint : IntegrableOn (deriv w) (Icc (1 : ℝ) X) := by
    apply hwcont.integrableOn_Icc.congr_fun _ measurableSet_Icc
    intro y hy
    exact (deriv_abelWeight hβ (zero_lt_one.trans_le hy.1)).symm
  have habel := sum_mul_eq_sub_integral_mul₀' f hf0 X hwdiff hwint
  have hleft : (∑ n ∈ Finset.Icc 0 X, w n * f n) =
      ∑ n ∈ Finset.Icc 1 X, f n * (n : ℂ) ^ (-(β : ℂ)) := by
    rw [sum_Icc_zero_eq_one_of_zero (fun n ↦ w n * f n) (by rw [hf0, mul_zero])]
    apply Finset.sum_congr rfl
    intro n _
    exact mul_comm _ _
  have hcum : (∑ n ∈ Finset.Icc 0 X, f n) = abelPrefix f X := by
    rw [sum_Icc_zero_eq_one_of_zero f hf0]
    simp only [abelPrefix, Nat.floor_natCast]
  have hint : (∫ y in Ioc (1 : ℝ) X,
      deriv w y * ∑ n ∈ Finset.Icc 0 ⌊y⌋₊, f n) =
        -(β : ℂ) * ∫ y in Ioc (1 : ℝ) X, abelKernel f β y := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    change deriv w y * (∑ n ∈ Finset.Icc 0 ⌊y⌋₊, f n) = -(β : ℂ) * abelKernel f β y
    rw [sum_Icc_zero_eq_one_of_zero f hf0, deriv_abelWeight hβ (zero_lt_one.trans hy.1)]
    simp only [abelKernel, abelPrefix]
    ring
  rw [hleft, hcum, hint] at habel
  simpa only [w, neg_mul, sub_neg_eq_add, Complex.ofReal_natCast] using habel

/-- Truncating the Abel continuation costs a square-root tail. -/
theorem norm_abelValue_sub_prefix_le (f : ℕ → ℂ) (hf0 : f 0 = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C * Real.sqrt (n : ℝ))
    {β : ℝ} (hβ : 3 / 4 ≤ β) (X : ℕ) (hX : 0 < X) :
    ‖(β : ℂ) * (∫ y in Ioi (1 : ℝ), abelKernel f β y) -
      (∑ n ∈ Finset.Icc 1 X, f n * (n : ℂ) ^ (-(β : ℂ)))‖ ≤
      4 * C * (X : ℝ) ^ (1 / 2 - β) := by
  have hβpos : 0 < β := by linarith
  have hβhalf : 1 / 2 < β := by linarith
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hfull := integrableOn_abelKernel f C hC hprefix hβhalf zero_lt_one
  have htail := integrableOn_abelKernel f C hC hprefix hβhalf hXpos
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull htail
  rw [intervalIntegral.integral_of_le hXone] at hsplit
  have hfinite := abel_prefix_identity f hf0 hβpos X
  have hid : (β : ℂ) * (∫ y in Ioi (1 : ℝ), abelKernel f β y) -
      (∑ n ∈ Finset.Icc 1 X, f n * (n : ℂ) ^ (-(β : ℂ))) =
        (β : ℂ) * (∫ y in Ioi (X : ℝ), abelKernel f β y) -
          (X : ℂ) ^ (-(β : ℂ)) * abelPrefix f X := by
    rw [hfinite, ← hsplit]
    ring
  have hend : ‖(X : ℂ) ^ (-(β : ℂ)) * abelPrefix f X‖ ≤ C * (X : ℝ) ^ (1 / 2 - β) := by
    rw [norm_mul]
    have hnorm : ‖(X : ℂ) ^ (-(β : ℂ))‖ = (X : ℝ) ^ (-β) := by
      simpa only [Complex.ofReal_natCast, neg_re, ofReal_re] using
        (Complex.norm_cpow_eq_rpow_re_of_pos hXpos (y := -(β : ℂ)))
    rw [hnorm]
    calc
      _ ≤ (X : ℝ) ^ (-β) * (C * Real.sqrt (X : ℝ)) :=
        mul_le_mul_of_nonneg_left (norm_abelPrefix_le_sqrt f C hC hprefix hXpos.le)
          (by positivity)
      _ = _ := by
        rw [Real.sqrt_eq_rpow, mul_left_comm, ← Real.rpow_add hXpos]
        congr 2
        ring
  have hratio : β / (β - 1 / 2) ≤ 3 := by
    apply (div_le_iff₀ (by linarith : 0 < β - 1 / 2)).mpr
    linarith
  have htailBound : ‖(β : ℂ) * ∫ y in Ioi (X : ℝ), abelKernel f β y‖ ≤
      3 * C * (X : ℝ) ^ (1 / 2 - β) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβpos]
    calc
      _ ≤ β * (C * (X : ℝ) ^ (1 / 2 - β) / (β - 1 / 2)) :=
        mul_le_mul_of_nonneg_left (norm_integral_abelKernel_tail_le f C hC hprefix hβhalf hXpos)
          hβpos.le
      _ = (β / (β - 1 / 2)) * (C * (X : ℝ) ^ (1 / 2 - β)) := by ring
      _ ≤ 3 * (C * (X : ℝ) ^ (1 / 2 - β)) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := by ring
  rw [hid]
  have htri := norm_sub_le ((β : ℂ) * ∫ y in Ioi (X : ℝ), abelKernel f β y)
    ((X : ℂ) ^ (-(β : ℂ)) * abelPrefix f X)
  linarith

end Erdos1141
