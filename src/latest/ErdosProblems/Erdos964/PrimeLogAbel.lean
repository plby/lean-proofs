import ErdosProblems.Erdos964.IntervalAbelError
import ErdosProblems.Erdos964.PrimeMertensCumulative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A bounded-error Abel formula for weighted prime harmonic sums
-/

namespace Erdos964

open BoundedGaps.Maynard MeasureTheory

theorem intervalAbelMain_log (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (f : ℝ → ℝ)
    (hf : ∀ t ∈ Set.Icc x y, DifferentiableAt ℝ f t)
    (hf' : ContinuousOn (deriv f) (Set.Icc x y)) :
    intervalAbelMain x y Real.log f = ∫ t in x..y, f t / t := by
  have hlog' : ContinuousOn (deriv Real.log) (Set.Icc x y) := by
    rw [Real.deriv_log']
    exact continuousOn_id.inv₀ (fun t ht => (hx.trans_le ht.1).ne')
  have hlogderiv : ∀ t ∈ Set.Icc x y, HasDerivAt Real.log (deriv Real.log t) t := by
    intro t ht
    simpa only [Real.deriv_log] using Real.hasDerivAt_log (hx.trans_le ht.1).ne'
  have hmain := intervalAbelMain_eq_integral_deriv x y hxy Real.log f
    (fun t ht => (hf t ht).hasDerivAt)
    hlogderiv
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr hf'.integrableOn_Icc)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr hlog'.integrableOn_Icc)
  simpa only [Real.deriv_log, div_eq_mul_inv] using hmain

theorem primeLogWeightedSum_eq (x y : ℝ) (f : ℝ → ℝ) :
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊y⌋₊, f n * primeLogHarmonicWeight n) =
      ∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
        f p * (Real.log p / (p : ℝ)) := by
  classical
  simp only [primeLogHarmonicWeight, mul_ite, mul_zero, Finset.sum_filter]

theorem exists_prime_log_abel_error :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (x y : ℝ) (f : ℝ → ℝ), 1 ≤ x → x ≤ y →
      (∀ t ∈ Set.Icc x y, DifferentiableAt ℝ f t) →
      ContinuousOn (deriv f) (Set.Icc x y) →
      |(∑ p ∈ (Finset.Ioc ⌊x⌋₊ ⌊y⌋₊).filter Nat.Prime,
          f p * (Real.log p / (p : ℝ))) - (∫ t in x..y, f t / t)| ≤
        E * (|f x| + |f y| + ∫ t in x..y, |deriv f t|) := by
  obtain ⟨E, hE, herror⟩ := exists_primeLogHarmonicWeight_cumulative_error
  refine ⟨E, hE, ?_⟩
  intro x y f hx hxy hf hf'
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : ContinuousOn Real.log (Set.Icc x y) :=
    Real.continuousOn_log.mono (fun t ht => (hx0.trans_le ht.1).ne')
  have h := abs_intervalWeightedSum_sub_intervalAbelMain_le x y hx0.le hxy
    primeLogHarmonicWeight Real.log f E (∫ t in x..y, |deriv f t|) hE hf
    hf'.integrableOn_Icc (hf'.abs.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    ((hf'.mul hlog).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (fun t ht => herror t (hx.trans ht.1))
    (by rw [intervalIntegral.integral_of_le hxy])
  rw [primeLogWeightedSum_eq, intervalAbelMain_log x y hx0 hxy f hf hf'] at h
  exact h

end Erdos964
