import BoundedGaps.Maynard.WeightedSmoothAbel

/-!
# Abel error transfer with a general cumulative main term

This allows logarithmic powers of dimensions two and three in place of
the one-dimensional logarithmic cumulative main term.
-/

namespace Erdos964

open BoundedGaps.Maynard MeasureTheory

noncomputable def generalAbelMain (Q : ℕ) (B f : ℝ → ℝ) : ℝ :=
  f Q * B Q - ∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * B t

theorem abs_weightedSum_sub_generalAbelMain_le (Q : ℕ) (hQ : 1 ≤ Q)
    (c : ℕ → ℝ) (hc : c 0 = 0) (B f : ℝ → ℝ) (E V : ℝ) (hE : 0 ≤ E)
    (hfdiff : ∀ t ∈ Set.Icc (1 : ℝ) Q, DifferentiableAt ℝ f t)
    (hfint : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) Q))
    (hfnorm : IntegrableOn (fun t => |deriv f t|) (Set.Ioc (1 : ℝ) Q))
    (hmainint : IntegrableOn (fun t => deriv f t * B t) (Set.Ioc (1 : ℝ) Q))
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q, |abelCumulative c t - B t| ≤ E)
    (hvariation : (∫ t in Set.Ioc (1 : ℝ) Q, |deriv f t|) ≤ V) :
    |(∑ n ∈ Finset.Icc 0 Q, f n * c n) - generalAbelMain Q B f| ≤ E * (|f Q| + V) := by
  let A : ℝ → ℝ := abelCumulative c
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hactualint : IntegrableOn (fun t => deriv f t * A t) (Set.Ioc (1 : ℝ) Q) :=
    (integrableOn_mul_sum_Icc (m := 0) c zero_le_one hfint).mono_set Set.Ioc_subset_Icc_self
  have herrorint : IntegrableOn (fun t => deriv f t * (A t - B t)) (Set.Ioc (1 : ℝ) Q) := by
    have h := hactualint.sub hmainint
    convert h using 1
    funext t
    simp only [Pi.sub_apply]
    ring
  have hintegral : |∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * (A t - B t)| ≤ E * V := by
    calc
      _ ≤ ∫ t in Set.Ioc (1 : ℝ) Q, |deriv f t * (A t - B t)| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Set.Ioc (1 : ℝ) Q, |deriv f t| * E := by
        apply integral_mono_ae herrorint.norm (hfnorm.mul_const E)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (happrox t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)
      _ = E * (∫ t in Set.Ioc (1 : ℝ) Q, |deriv f t|) := by
        rw [integral_mul_const]
        ring
      _ ≤ E * V := mul_le_mul_of_nonneg_left hvariation hE
  have hendpoint := happrox (Q : ℝ) ⟨hQR, le_rfl⟩
  rw [sum_mul_eq_sub_integral_mul₀' c hc Q hfdiff hfint]
  unfold generalAbelMain
  have hsum : (∑ n ∈ Finset.Icc 0 Q, c n) = A Q := by
    simp only [A, abelCumulative, Nat.floor_natCast]
  rw [hsum]
  have hint : (∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * (A t - B t)) =
      (∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * A t) -
        ∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * B t := by
    calc
      _ = ∫ t in Set.Ioc (1 : ℝ) Q, (deriv f t * A t - deriv f t * B t) := by
        apply integral_congr_ae
        filter_upwards [] with t
        ring
      _ = _ := integral_sub hactualint hmainint
  have hid : (f Q * A Q - ∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * A t) -
      (f Q * B Q - ∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * B t) =
      f Q * (A Q - B Q) - ∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * (A t - B t) := by
    rw [hint]
    ring
  change |(f Q * A Q - ∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * A t) -
    (f Q * B Q - ∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * B t)| ≤ _
  rw [hid]
  calc
    _ ≤ |f Q * (A Q - B Q)| + |∫ t in Set.Ioc (1 : ℝ) Q, deriv f t * (A t - B t)| :=
      abs_sub _ _
    _ ≤ |f Q| * E + E * V := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hendpoint (abs_nonneg _)) hintegral
    _ = _ := by ring

end Erdos964
