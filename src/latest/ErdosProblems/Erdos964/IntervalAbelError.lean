import ErdosProblems.Erdos964.PowerAbelMain

/-!
# Abel error transfer on an interval with two moving endpoints
-/

namespace Erdos964

open BoundedGaps.Maynard MeasureTheory

noncomputable def intervalAbelMain (a b : ℝ) (B f : ℝ → ℝ) : ℝ :=
  f b * B b - f a * B a - ∫ t in Set.Ioc a b, deriv f t * B t

theorem abs_intervalWeightedSum_sub_intervalAbelMain_le (a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (c : ℕ → ℝ) (B f : ℝ → ℝ) (E V : ℝ) (hE : 0 ≤ E)
    (hfdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (hfint : IntegrableOn (deriv f) (Set.Icc a b))
    (hfnorm : IntegrableOn (fun t => |deriv f t|) (Set.Ioc a b))
    (hmainint : IntegrableOn (fun t => deriv f t * B t) (Set.Ioc a b))
    (happrox : ∀ t ∈ Set.Icc a b, |abelCumulative c t - B t| ≤ E)
    (hvariation : (∫ t in Set.Ioc a b, |deriv f t|) ≤ V) :
    |(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * c n) - intervalAbelMain a b B f| ≤
      E * (|f a| + |f b| + V) := by
  let A := abelCumulative c
  have hactualint : IntegrableOn (fun t => deriv f t * A t) (Set.Ioc a b) :=
    (integrableOn_mul_sum_Icc (m := 0) c ha hfint).mono_set Set.Ioc_subset_Icc_self
  have herrorint : IntegrableOn (fun t => deriv f t * (A t - B t)) (Set.Ioc a b) := by
    have h := hactualint.sub hmainint
    convert h using 1
    funext t
    simp only [Pi.sub_apply]
    ring
  have hintegral : |∫ t in Set.Ioc a b, deriv f t * (A t - B t)| ≤ E * V := by
    calc
      _ ≤ ∫ t in Set.Ioc a b, |deriv f t * (A t - B t)| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Set.Ioc a b, |deriv f t| * E := by
        apply integral_mono_ae herrorint.norm (hfnorm.mul_const E)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (happrox t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)
      _ = E * (∫ t in Set.Ioc a b, |deriv f t|) := by rw [integral_mul_const]; ring
      _ ≤ E * V := mul_le_mul_of_nonneg_left hvariation hE
  have hint : (∫ t in Set.Ioc a b, deriv f t * (A t - B t)) =
      (∫ t in Set.Ioc a b, deriv f t * A t) -
        ∫ t in Set.Ioc a b, deriv f t * B t := by
    calc
      _ = ∫ t in Set.Ioc a b, (deriv f t * A t - deriv f t * B t) := by
        apply integral_congr_ae
        filter_upwards [] with t
        ring
      _ = _ := integral_sub hactualint hmainint
  rw [sum_mul_eq_sub_sub_integral_mul c ha hab hfdiff hfint]
  change |(f b * A b - f a * A a - ∫ t in Set.Ioc a b, deriv f t * A t) -
    (f b * B b - f a * B a - ∫ t in Set.Ioc a b, deriv f t * B t)| ≤ _
  have hid : (f b * A b - f a * A a - ∫ t in Set.Ioc a b, deriv f t * A t) -
      (f b * B b - f a * B a - ∫ t in Set.Ioc a b, deriv f t * B t) =
      (f b * (A b - B b) - f a * (A a - B a)) -
        ∫ t in Set.Ioc a b, deriv f t * (A t - B t) := by rw [hint]; ring
  rw [hid]
  calc
    _ ≤ |f b * (A b - B b) - f a * (A a - B a)| +
        |∫ t in Set.Ioc a b, deriv f t * (A t - B t)| := abs_sub _ _
    _ ≤ (|f b * (A b - B b)| + |f a * (A a - B a)|) + E * V :=
      add_le_add (abs_sub _ _) hintegral
    _ ≤ (|f b| * E + |f a| * E) + E * V := by
      simp only [abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (happrox b ⟨hab, le_rfl⟩) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (happrox a ⟨le_rfl, hab⟩) (abs_nonneg _))) le_rfl
    _ = _ := by ring

theorem intervalAbelMain_eq_integral_deriv (a b : ℝ) (hab : a ≤ b) (B f : ℝ → ℝ)
    (hfderiv : ∀ t ∈ Set.Icc a b, HasDerivAt f (deriv f t) t)
    (hBderiv : ∀ t ∈ Set.Icc a b, HasDerivAt B (deriv B t) t)
    (hfint : IntervalIntegrable (deriv f) volume a b)
    (hBint : IntervalIntegrable (deriv B) volume a b) :
    intervalAbelMain a b B f = ∫ t in a..b, f t * deriv B t := by
  have hfU : ∀ t ∈ Set.uIcc a b, HasDerivAt f (deriv f t) t := by
    simpa only [Set.uIcc_of_le hab] using hfderiv
  have hBU : ∀ t ∈ Set.uIcc a b, HasDerivAt B (deriv B t) t := by
    simpa only [Set.uIcc_of_le hab] using hBderiv
  have hfcont : ContinuousOn f (Set.uIcc a b) :=
    fun t ht => (hfU t ht).continuousAt.continuousWithinAt
  have hBcont : ContinuousOn B (Set.uIcc a b) :=
    fun t ht => (hBU t ht).continuousAt.continuousWithinAt
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub hfU hBU hfint hBint
  rw [intervalIntegral.integral_add
    (hfint.mul_continuousOn hBcont) (hBint.continuousOn_mul hfcont)] at hparts
  unfold intervalAbelMain
  rw [← intervalIntegral.integral_of_le hab]
  linarith

end Erdos964
