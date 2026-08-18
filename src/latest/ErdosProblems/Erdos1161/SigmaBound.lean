import ErdosProblems.Erdos1161.DivisorBounds

/-!
# A divisor-sum bound uniform on a logarithmic-power box

`DivisorBounds` proves the Euler-product estimate
`sigma₁(m) / m ≪ log log m`. Here we put it into the uniform form needed
for the large-order range in Erdős Problem 1161: the argument `m` may vary up
to `n ^ (C * log₂ n)`, where `C` is fixed.
-/

namespace Erdos1161

open Filter Real
open scoped Topology

noncomputable section

private lemma natLog_two_mul_log_two_le_log (n : ℕ) (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := by
  have hpow := Nat.pow_log_le_self 2 hn
  have hcast : (((2 ^ Nat.log 2 n : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log
    (show (0 : ℝ) < ((2 ^ Nat.log 2 n : ℕ) : ℕ) by positivity) hcast
  simpa [Nat.cast_pow, Real.log_pow] using hlog

private lemma natLog_two_cast_le_two_mul_log (n : ℕ) (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  have h := natLog_two_mul_log_two_le_log n hn
  have hnonneg : (0 : ℝ) ≤ Nat.log 2 n := by positivity
  nlinarith [Real.log_two_gt_d9]

private theorem eventually_loglog_le_three_loglog_of_le_pow_log (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m →
      m ≤ n ^ (C * Nat.log 2 n) →
      Real.log (Real.log m) ≤ 3 * Real.log (Real.log n) := by
  have hll : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  by_cases hC : C = 0
  · subst C
    filter_upwards
      [hll.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    intro m hm hmle
    have hm1 : m = 1 := by
      simp only [Nat.zero_mul, pow_zero] at hmle
      omega
    subst m
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hn
  · have hCpos : 0 < C := Nat.pos_of_ne_zero hC
    filter_upwards
      [eventually_ge_atTop (2 : ℕ),
        hll.eventually (eventually_ge_atTop (0 : ℝ)),
        hll.eventually
          (eventually_ge_atTop (Real.log (2 * (C : ℝ))))] with n hn2 hll0 hconst
    intro m hm hmle
    have hn0 : n ≠ 0 := by omega
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn2
    have hlogn : 0 < Real.log n := Real.log_pos hnR
    have hlogn0 : 0 ≤ Real.log n := hlogn.le
    by_cases hm1 : m = 1
    · subst m
      simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hll0
    · have hmR : (1 : ℝ) < m := by
        have : 1 < m := by omega
        exact_mod_cast this
      have hlogm : 0 < Real.log m := Real.log_pos hmR
      have hcastle : (m : ℝ) ≤ ((n ^ (C * Nat.log 2 n) : ℕ) : ℝ) := by
        exact_mod_cast hmle
      have hlogpow := Real.log_le_log (by positivity : (0 : ℝ) < (m : ℝ)) hcastle
      have hNatLog := natLog_two_cast_le_two_mul_log n hn0
      have hCcast : (0 : ℝ) ≤ C := by positivity
      have hexponent : ((C * Nat.log 2 n : ℕ) : ℝ) ≤
          2 * (C : ℝ) * Real.log n := by
        push_cast
        nlinarith
      have hlogm_upper : Real.log m ≤
          (2 * (C : ℝ)) * (Real.log n) ^ 2 := by
        rw [Nat.cast_pow, Real.log_pow] at hlogpow
        calc
          Real.log m ≤ ((C * Nat.log 2 n : ℕ) : ℝ) * Real.log n := hlogpow
          _ ≤ (2 * (C : ℝ) * Real.log n) * Real.log n := by
            exact mul_le_mul_of_nonneg_right hexponent hlogn0
          _ = (2 * (C : ℝ)) * (Real.log n) ^ 2 := by ring
      have hloglog := Real.log_le_log hlogm hlogm_upper
      have hrewrite :
          Real.log ((2 * (C : ℝ)) * (Real.log n) ^ 2) =
            Real.log (2 * (C : ℝ)) + 2 * Real.log (Real.log n) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        norm_num
      rw [hrewrite] at hloglog
      linarith

/-- Uniform `sigma₁(m) / m ≪ log log n` for
`m ≤ n ^ (C * log₂ n)`, with a constant depending only on `C`. -/
theorem eventually_divisorSum_ratio_le_const_mul_loglog_uniform_pow_log (C : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m →
      m ≤ n ^ (C * Nat.log 2 n) →
      (divisorSum m : ℝ) / (m : ℝ) ≤
        K * Real.log (Real.log n) := by
  obtain ⟨A, hA, hpoint⟩ :=
    eventually_divisorSum_ratio_le_const_mul_loglog
  rw [eventually_atTop] at hpoint
  obtain ⟨M, hM⟩ := hpoint
  have hll : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨3 * A + 1, by positivity, ?_⟩
  filter_upwards
    [eventually_loglog_le_three_loglog_of_le_pow_log C,
      hll.eventually (eventually_ge_atTop (M : ℝ)),
      hll.eventually (eventually_ge_atTop (0 : ℝ))] with n hbox hlarge hnonneg
  intro m hm hmle
  by_cases hMm : M ≤ m
  · have hratio := hM m hMm
    have hcompare := hbox m hm hmle
    calc
      (divisorSum m : ℝ) / (m : ℝ) ≤
          A * Real.log (Real.log m) := hratio
      _ ≤ A * (3 * Real.log (Real.log n)) :=
        mul_le_mul_of_nonneg_left hcompare hA.le
      _ ≤ (3 * A + 1) * Real.log (Real.log n) := by
        nlinarith
  · have hmM : m < M := Nat.lt_of_not_ge hMm
    have hsigma : divisorSum m ≤ m ^ 2 := by
      simpa [divisorSum] using ArithmeticFunction.sigma_le_pow_succ 1 m
    have hratio_m : (divisorSum m : ℝ) / (m : ℝ) ≤ (m : ℝ) := by
      rw [div_le_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)]
      exact_mod_cast (show divisorSum m ≤ m * m by simpa [pow_two] using hsigma)
    have hmll : (m : ℝ) ≤ Real.log (Real.log n) := by
      exact (by exact_mod_cast hmM.le : (m : ℝ) ≤ M).trans hlarge
    calc
      (divisorSum m : ℝ) / (m : ℝ) ≤ (m : ℝ) := hratio_m
      _ ≤ Real.log (Real.log n) := hmll
      _ ≤ (3 * A + 1) * Real.log (Real.log n) := by
        exact le_mul_of_one_le_left hnonneg (by nlinarith [hA])

end

end Erdos1161
