/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Basic
import ErdosProblems.Erdos297.Statement

/-!
# Erdős Problem 297: exponential-moment upper bound

This file proves the finite product bound underlying the upper half of the
sharp asymptotic.  The count itself is defined using exact rational equality
in `ErdosProblems.Erdos297.Basic`; real numbers enter only after membership in
the exact representation family has been established.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos297

noncomputable section

attribute [local instance] Classical.propDecidable

/-- On the nonnegative half-line, the endpoint-extended free-energy kernel is
the logarithm of Mathlib's standard smooth `exp (-1/x)` gluing function. -/
lemma freeEnergyKernel_eq_log_expNegInvGlue_div
    {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) :
    freeEnergyKernel lam x =
      Real.log (1 + expNegInvGlue (x / lam)) := by
  by_cases hx0 : x = 0
  · subst x
    simp [freeEnergyKernel]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  simp [freeEnergyKernel, hx0, expNegInvGlue, not_le.mpr (div_pos hxpos hlam),
    inv_div]
  congr 3
  ring

/-- The free-energy kernel is monotone on the unit interval. -/
lemma monotoneOn_freeEnergyKernel {lam : ℝ} (hlam : 0 < lam) :
    MonotoneOn (freeEnergyKernel lam) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [freeEnergyKernel_eq_log_expNegInvGlue_div hlam hx.1,
    freeEnergyKernel_eq_log_expNegInvGlue_div hlam hy.1]
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right (expNegInvGlue.nonneg _)))
  gcongr
  exact expNegInvGlue.monotone (by
    exact (div_le_div_iff_of_pos_right hlam).2 hxy)

/-- The interval-integral and set-integral normalizations of the free-energy
kernel agree. -/
lemma intervalIntegral_freeEnergyKernel_eq_setIntegral (lam : ℝ) :
    (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) =
      ∫ x in Icc (0 : ℝ) 1, freeEnergyKernel lam x := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]

/-- The normalized right-endpoint Riemann sum used by the finite product. -/
def freeEnergyRiemannSum (lam : ℝ) (N : ℕ) : ℝ :=
  (∑ k ∈ range N,
    freeEnergyKernel lam (((k + 1 : ℕ) : ℝ) / (N : ℝ))) / (N : ℝ)

lemma monotoneOn_scaled_freeEnergyKernel
    {lam : ℝ} (hlam : 0 < lam) {N : ℕ} (hN : 0 < N) :
    MonotoneOn (fun x : ℝ ↦ freeEnergyKernel lam (x / (N : ℝ)))
      (Icc (0 : ℝ) (N : ℝ)) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  intro x hx y hy hxy
  apply monotoneOn_freeEnergyKernel hlam
  · exact ⟨div_nonneg hx.1 hNreal.le, (div_le_one hNreal).2 hx.2⟩
  · exact ⟨div_nonneg hy.1 hNreal.le, (div_le_one hNreal).2 hy.2⟩
  · exact (div_le_div_iff_of_pos_right hNreal).2 hxy

lemma scaled_freeEnergyKernel_integral
    (lam : ℝ) {N : ℕ} (hN : 0 < N) :
    (∫ x in (0 : ℝ)..(N : ℝ),
        freeEnergyKernel lam (x / (N : ℝ))) =
      (N : ℝ) * ∫ x in (0 : ℝ)..1, freeEnergyKernel lam x := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [intervalIntegral.integral_comp_div (freeEnergyKernel lam) hN0]
  simp [hN0]

lemma shifted_freeEnergy_sum_eq
    (lam : ℝ) {N : ℕ} (hN : 0 < N) :
    (∑ k ∈ range N,
        freeEnergyKernel lam (((k + 1 : ℕ) : ℝ) / (N : ℝ))) =
      (∑ k ∈ range N,
        freeEnergyKernel lam ((k : ℝ) / (N : ℝ))) +
        freeEnergyKernel lam 1 := by
  let f : ℕ → ℝ := fun k ↦ freeEnergyKernel lam ((k : ℝ) / (N : ℝ))
  calc
    (∑ k ∈ range N,
        freeEnergyKernel lam (((k + 1 : ℕ) : ℝ) / (N : ℝ))) =
        ∑ k ∈ range N, f (k + 1) := by rfl
    _ = ∑ k ∈ range (N + 1), f k := by
      rw [sum_range_succ']
      simp [f, freeEnergyKernel]
    _ = (∑ k ∈ range N, f k) + f N := by
      rw [sum_range_succ]
    _ = (∑ k ∈ range N,
        freeEnergyKernel lam ((k : ℝ) / (N : ℝ))) +
        freeEnergyKernel lam 1 := by
      simp [f, hN.ne']

lemma integral_le_freeEnergyRiemannSum
    {lam : ℝ} (hlam : 0 < lam) {N : ℕ} (hN : 0 < N) :
    (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) ≤
      freeEnergyRiemannSum lam N := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hscaled : MonotoneOn
      (fun x : ℝ ↦ freeEnergyKernel lam (x / (N : ℝ)))
      (Icc (0 : ℝ) ((0 : ℝ) + (N : ℝ))) := by
    simpa using monotoneOn_scaled_freeEnergyKernel hlam hN
  have hmono := hscaled.integral_le_sum
  simp only [zero_add] at hmono
  rw [scaled_freeEnergyKernel_integral lam hN] at hmono
  rw [freeEnergyRiemannSum]
  calc
    (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) =
        ((N : ℝ) * ∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) / (N : ℝ) := by
          field_simp
    _ ≤ (∑ k ∈ range N,
        freeEnergyKernel lam (((k + 1 : ℕ) : ℝ) / (N : ℝ))) / (N : ℝ) :=
      (div_le_div_iff_of_pos_right hNreal).2 hmono

lemma freeEnergyRiemannSum_le_integral_add
    {lam : ℝ} (hlam : 0 < lam) {N : ℕ} (hN : 0 < N) :
    freeEnergyRiemannSum lam N ≤
      (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) +
        freeEnergyKernel lam 1 / (N : ℝ) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hscaled : MonotoneOn
      (fun x : ℝ ↦ freeEnergyKernel lam (x / (N : ℝ)))
      (Icc (0 : ℝ) ((0 : ℝ) + (N : ℝ))) := by
    simpa using monotoneOn_scaled_freeEnergyKernel hlam hN
  have hmono := hscaled.sum_le_integral
  simp only [zero_add] at hmono
  rw [scaled_freeEnergyKernel_integral lam hN] at hmono
  rw [freeEnergyRiemannSum, shifted_freeEnergy_sum_eq lam hN]
  have hadd := add_le_add hmono (le_refl (freeEnergyKernel lam 1))
  calc
    ((∑ k ∈ range N,
        freeEnergyKernel lam ((k : ℝ) / (N : ℝ))) +
        freeEnergyKernel lam 1) / (N : ℝ) ≤
        ((N : ℝ) * (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) +
          freeEnergyKernel lam 1) / (N : ℝ) :=
      (div_le_div_iff_of_pos_right hNreal).2 hadd
    _ = (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) +
        freeEnergyKernel lam 1 / (N : ℝ) := by
      field_simp

/-- The discrete log-partition averages converge to the integral occurring in
`gamma`. -/
theorem tendsto_freeEnergyRiemannSum {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (freeEnergyRiemannSum lam) atTop
      (nhds (∫ x in Icc (0 : ℝ) 1, freeEnergyKernel lam x)) := by
  rw [← intervalIntegral_freeEnergyKernel_eq_setIntegral lam]
  have hlo : ∀ᶠ N : ℕ in atTop,
      (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) ≤
        freeEnergyRiemannSum lam N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact integral_le_freeEnergyRiemannSum hlam (by omega)
  have hhi : ∀ᶠ N : ℕ in atTop,
      freeEnergyRiemannSum lam N ≤
        (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) +
          freeEnergyKernel lam 1 / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact freeEnergyRiemannSum_le_integral_add hlam (by omega)
  have hupper : Tendsto
      (fun N : ℕ ↦
        (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x) +
          freeEnergyKernel lam 1 / (N : ℝ)) atTop
      (nhds (∫ x in (0 : ℝ)..1, freeEnergyKernel lam x)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_div_atTop_nhds_zero_nat (freeEnergyKernel lam 1))
  have ht := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper hlo hhi
  simpa using ht

/-- The finite product occurring in the exponential-moment upper bound. -/
def upperProduct (N : ℕ) (lam : ℝ) : ℝ :=
  ∏ n ∈ denominators N, (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ)))

/-- Exact rational reciprocal sum one implies the corresponding real sum is
one. -/
lemma real_reciprocal_sum_eq_one_of_mem_representations
    {N : ℕ} {A : Finset ℕ} (hA : A ∈ representations N) :
    (∑ n ∈ A, (n : ℝ)⁻¹) = 1 := by
  have hq : UnitFractions.rec_sum A = 1 := (mem_representations.mp hA).2
  have hr := congrArg (fun q : ℚ ↦ (q : ℝ)) hq
  simpa [UnitFractions.rec_sum, div_eq_mul_inv] using hr

/-- On an exact representation, the exponential weight is constant. -/
lemma prod_exp_reciprocal_eq
    {N : ℕ} {A : Finset ℕ} (hA : A ∈ representations N) (lam : ℝ) :
    (∏ n ∈ A, Real.exp (-lam * (N : ℝ) / (n : ℝ))) =
      Real.exp (-lam * (N : ℝ)) := by
  rw [← Real.exp_sum]
  congr 1
  calc
    (∑ n ∈ A, -lam * (N : ℝ) / (n : ℝ)) =
        (-lam * (N : ℝ)) * ∑ n ∈ A, (n : ℝ)⁻¹ := by
          simp only [div_eq_mul_inv, Finset.mul_sum]
    _ = -lam * (N : ℝ) := by
      rw [real_reciprocal_sum_eq_one_of_mem_representations hA, mul_one]

/-- Finite exponential-moment bound.  Positivity of `lam` is not needed for
this algebraic inequality; the sharp asymptotic later uses `0 < lam`. -/
theorem count_mul_exp_neg_le_upperProduct (N : ℕ) (lam : ℝ) :
    (count N : ℝ) * Real.exp (-lam * (N : ℝ)) ≤ upperProduct N lam := by
  calc
    (count N : ℝ) * Real.exp (-lam * (N : ℝ)) =
        ∑ A ∈ representations N, Real.exp (-lam * (N : ℝ)) := by
          simp [count]
    _ = ∑ A ∈ representations N,
          ∏ n ∈ A, Real.exp (-lam * (N : ℝ) / (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro A hA
          exact (prod_exp_reciprocal_eq hA lam).symm
    _ ≤ ∑ A ∈ (denominators N).powerset,
          ∏ n ∈ A, Real.exp (-lam * (N : ℝ) / (n : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro A _ _
          positivity
    _ = upperProduct N lam := by
          simpa [upperProduct] using
            (Finset.prod_one_add
              (denominators N)
              (f := fun n : ℕ ↦ Real.exp (-lam * (N : ℝ) / (n : ℝ)))).symm

/-- The product form usually quoted as the finite upper bound. -/
theorem count_le_exp_mul_upperProduct (N : ℕ) (lam : ℝ) :
    (count N : ℝ) ≤ Real.exp (lam * (N : ℝ)) * upperProduct N lam := by
  calc
    (count N : ℝ) = Real.exp (lam * (N : ℝ)) *
        ((count N : ℝ) * Real.exp (-lam * (N : ℝ))) := by
          calc
            (count N : ℝ) = (count N : ℝ) * 1 := by simp
            _ = (count N : ℝ) *
                (Real.exp (lam * (N : ℝ)) *
                  Real.exp (-lam * (N : ℝ))) := by
                    rw [← Real.exp_add]
                    ring_nf
                    simp
            _ = Real.exp (lam * (N : ℝ)) *
                ((count N : ℝ) * Real.exp (-lam * (N : ℝ))) := by ring
    _ ≤ Real.exp (lam * (N : ℝ)) * upperProduct N lam :=
      mul_le_mul_of_nonneg_left (count_mul_exp_neg_le_upperProduct N lam)
        (Real.exp_pos _).le

/-- Positive-parameter version of the finite upper bound. -/
theorem finite_exponential_moment_upper_bound
    (N : ℕ) (lam : ℝ) (_hlam : 0 < lam) :
    (count N : ℝ) ≤
      Real.exp (lam * (N : ℝ)) *
        ∏ n ∈ denominators N,
          (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ))) := by
  simpa [upperProduct] using count_le_exp_mul_upperProduct N lam

lemma upperProduct_pos (N : ℕ) (lam : ℝ) : 0 < upperProduct N lam := by
  rw [upperProduct]
  positivity

/-- Taking logarithms in the finite product estimate converts the product to
the sum that is subsequently treated as a Riemann sum. -/
theorem log_count_le_lam_mul_add_sum
    {N : ℕ} (hN : 1 ≤ N) (lam : ℝ) :
    Real.log (count N : ℝ) ≤ lam * (N : ℝ) +
      ∑ n ∈ denominators N,
        Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ))) := by
  have hcount : 0 < (count N : ℝ) := by
    exact_mod_cast count_pos hN
  calc
    Real.log (count N : ℝ) ≤
        Real.log (Real.exp (lam * (N : ℝ)) * upperProduct N lam) :=
      Real.log_le_log hcount (count_le_exp_mul_upperProduct N lam)
    _ = Real.log (Real.exp (lam * (N : ℝ))) +
        Real.log (upperProduct N lam) := by
      rw [Real.log_mul (Real.exp_ne_zero _) (upperProduct_pos N lam).ne']
    _ = lam * (N : ℝ) +
        ∑ n ∈ denominators N,
          Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ))) := by
      rw [Real.log_exp, upperProduct,
        Real.log_prod (fun n _hn ↦ by positivity)]

lemma sum_denominators_eq_sum_range_succ
    (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ denominators N, f n) =
      ∑ k ∈ range N, f (k + 1) := by
  induction N with
  | zero => simp [denominators]
  | succ N ih =>
      rw [denominators, sum_Icc_succ_top (by omega), sum_range_succ]
      simpa [denominators, ih]

lemma freeEnergyKernel_nat_ratio
    (lam : ℝ) {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    freeEnergyKernel lam ((n : ℝ) / (N : ℝ)) =
      Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ))) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [freeEnergyKernel, if_neg (div_ne_zero hn0 hN0)]
  congr 3
  field_simp

lemma discreteLogAverage_eq_freeEnergyRiemannSum
    (lam : ℝ) {N : ℕ} (hN : 0 < N) :
    (∑ n ∈ denominators N,
      Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ)))) / (N : ℝ) =
      freeEnergyRiemannSum lam N := by
  rw [freeEnergyRiemannSum, sum_denominators_eq_sum_range_succ]
  congr 1
  apply sum_congr rfl
  intro k hk
  exact (freeEnergyKernel_nat_ratio lam hN (Nat.succ_pos k)).symm

/-- Exact normalized logarithmic upper bound before passing to the limit. -/
theorem logGrowth_le_lam_add_freeEnergyRiemannSum
    {N : ℕ} (hN : 1 ≤ N) {lam : ℝ} :
    logGrowth N ≤ lam + freeEnergyRiemannSum lam N := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  rw [logGrowth]
  calc
    Real.log (count N : ℝ) / (N : ℝ) ≤
        (lam * (N : ℝ) +
          ∑ n ∈ denominators N,
            Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ)))) / (N : ℝ) :=
      (div_le_div_iff_of_pos_right hNreal).2
        (log_count_le_lam_mul_add_sum hN lam)
    _ = lam +
        (∑ n ∈ denominators N,
          Real.log (1 + Real.exp (-lam * (N : ℝ) / (n : ℝ)))) / (N : ℝ) := by
      field_simp
    _ = lam + freeEnergyRiemannSum lam N := by
      rw [discreteLogAverage_eq_freeEnergyRiemannSum lam
        (lt_of_lt_of_le Nat.zero_lt_one hN)]

/-- The finite exponential-moment inequality and the Riemann-sum limit give
the normalized asymptotic upper bound at every positive parameter. -/
theorem eventually_logGrowth_le_gamma_add
    {lam : ℝ} (hlam : 0 < lam) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, logGrowth N ≤ gamma lam + ε := by
  have hconv := tendsto_freeEnergyRiemannSum hlam
  have hbelow : ∀ᶠ N : ℕ in atTop,
      freeEnergyRiemannSum lam N <
        (∫ x in Icc (0 : ℝ) 1, freeEnergyKernel lam x) + ε :=
    (tendsto_order.1 hconv).2 _
      (lt_add_of_pos_right _ hε)
  filter_upwards [hbelow, eventually_ge_atTop 1] with N hsum hN
  calc
    logGrowth N ≤ lam + freeEnergyRiemannSum lam N :=
      logGrowth_le_lam_add_freeEnergyRiemannSum hN
    _ ≤ lam + ((∫ x in Icc (0 : ℝ) 1, freeEnergyKernel lam x) + ε) := by
      exact add_le_add (le_refl lam) hsum.le
    _ = gamma lam + ε := by
      rw [gamma]
      ring

end

end Erdos297

#print axioms Erdos297.finite_exponential_moment_upper_bound
#print axioms Erdos297.eventually_logGrowth_le_gamma_add
