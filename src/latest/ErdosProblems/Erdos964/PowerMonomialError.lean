import ErdosProblems.Erdos964.PowerMonomialMain
import ErdosProblems.Erdos964.LogMeanUniformError

/-!
# Uniform weighted monomial estimates for a logarithmic cumulative mean
-/

namespace Erdos964

open BoundedGaps.Maynard MeasureTheory Filter
open scoped Topology

theorem log_power_monomial_error (Q : ℕ) (hQ : 1 ≤ Q) (a : ℕ → ℝ) (ha : a 0 = 0)
    (S L E : ℝ) (hL : 0 < L) (hQL : Real.log Q ≤ L) (hE : 0 ≤ E)
    (κ j : ℕ) (hκ : 0 < κ)
    (happrox : ∀ t ∈ Set.Icc (1 : ℝ) Q,
      |abelCumulative a t - S * (Real.log t) ^ κ| ≤ E) :
    |(∑ n ∈ Finset.Icc 0 Q, normalizedLogMonomial L j n * a n) -
      S * κ / ((κ + j : ℕ) : ℝ) * (Real.log Q) ^ (κ + j) / L ^ j| ≤ 2 * E := by
  let f := normalizedLogMonomial L j
  let B : ℝ → ℝ := fun t => S * (Real.log t) ^ κ
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) Q) : HasDerivAt f (deriv f t) t :=
    (normalizedLogMonomial_hasDerivAt L j t (zero_lt_one.trans_le ht.1)).differentiableAt.hasDerivAt
  have hdcont := normalizedLogMonomial_deriv_continuousOn L j Q
  have hdint : IntervalIntegrable (deriv f) volume 1 Q := hdcont.intervalIntegrable_of_Icc hQR
  have hnormint : IntegrableOn (fun t => |deriv f t|) (Set.Ioc (1 : ℝ) Q) := by
    have h : IntegrableOn (fun t => ‖deriv f t‖) (Set.Ioc (1 : ℝ) Q) volume :=
      hdcont.norm.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    simpa only [Real.norm_eq_abs] using h
  have hmainint : IntegrableOn (fun t => deriv f t * B t) (Set.Ioc (1 : ℝ) Q) :=
    (hdcont.mul (continuousOn_const.mul ((continuousOn_id.log
      (fun _ ht => (zero_lt_one.trans_le ht.1).ne')).pow κ))).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hint : (∫ t in (1 : ℝ)..Q, deriv f t) = f Q - f 1 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht =>
      hderiv t (by simpa only [Set.uIcc_of_le hQR] using ht)) hdint
  have hvar : (∫ t in Set.Ioc (1 : ℝ) Q, |deriv f t|) ≤ f Q - f 1 := by
    apply le_of_eq
    calc
      _ = ∫ t in (1 : ℝ)..Q, deriv f t := by
        rw [intervalIntegral.integral_of_le hQR]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact abs_of_nonneg (normalizedLogMonomial_deriv_nonneg L hL.le j t ht.1.le)
      _ = _ := hint
  have h := abs_weightedSum_sub_generalAbelMain_le Q hQ a ha B f E (f Q - f 1) hE
    (fun t ht => (hderiv t ht).differentiableAt) hdcont.integrableOn_Icc hnormint hmainint
    happrox hvar
  rw [generalAbelMain_log_power_monomial Q hQ S L κ j hκ] at h
  have hend := normalizedLogMonomial_bounds L hL j Q hQR hQL
  have hstart := (normalizedLogMonomial_bounds L hL j 1 le_rfl
    (by simpa only [Real.log_one] using hL.le)).1
  calc
    _ ≤ E * (|f Q| + (f Q - f 1)) := h
    _ ≤ 2 * E := by
      rw [abs_of_nonneg hend.1]
      nlinarith [hend.2, hstart]

theorem exists_log_mean_uniform_monomial_error (a : ArithmeticFunction ℝ) (S : ℝ)
    (κ : ℕ) (hκ : 0 < κ)
    (hlimit : Tendsto (fun x : ℝ => abelCumulative a x / (Real.log x) ^ κ) atTop (𝓝 S))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R Q j : ℕ, 0 < Real.log R → 1 ≤ Q → Q ≤ R →
      |(∑ n ∈ Finset.Icc 0 Q, normalizedLogMonomial (Real.log R) j n * a n) -
        S * κ / ((κ + j : ℕ) : ℝ) * (Real.log Q) ^ (κ + j) / (Real.log R) ^ j| ≤
        2 * (ε * (Real.log R) ^ κ + C) := by
  obtain ⟨C, hC, herror⟩ := exists_log_mean_uniform_error a S κ hlimit ε hε
  refine ⟨C, hC, ?_⟩
  intro R Q j hR hQ hQR
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hQRreal : (Q : ℝ) ≤ R := by exact_mod_cast hQR
  apply log_power_monomial_error Q hQ a ArithmeticFunction.map_zero S (Real.log R)
    (ε * (Real.log R) ^ κ + C) hR (Real.log_le_log hQpos hQRreal) (by positivity) κ j hκ
  intro t ht
  refine (herror t ht.1).trans ?_
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg ht.1)
    (Real.log_le_log (zero_lt_one.trans_le ht.1) (ht.2.trans hQRreal)) κ) hε.le

end Erdos964
