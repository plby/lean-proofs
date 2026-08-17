/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.FactorialEgyptian
import ErdosProblems.Erdos285.Proposition7Mass
import UnitFractions.AuxiliaryLemmas

/-!
# A sublinear factorial cutoff

We use `ceil (n / sqrt (log n))`.  Its ratio to `n` tends to zero, whereas
its factorial eventually dominates `exp (2n)`, and hence `lcm(1,...,n)`.
-/

open Filter
open scoped Topology Real

namespace Erdos284

noncomputable section

/-- The number of mixed-radix digits used for the correction fraction. -/
def factorialCutoff (n : ℕ) : ℕ :=
  ⌈(n : ℝ) / Real.sqrt (Real.log (n : ℝ))⌉₊

private lemma factorialScale_tendsto_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / Real.sqrt (Real.log (n : ℝ)))
      atTop atTop := by
  apply tendsto_atTop.2
  intro B
  have hsqrtTop : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hsqrtTop.eventually (eventually_ge_atTop B),
    eventually_ge_atTop 3] with n hBn hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlogle : Real.log (n : ℝ) ≤ (n : ℝ) :=
    (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
  have hsqrtle : Real.sqrt (Real.log (n : ℝ)) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt hlogle
  rw [le_div_iff₀ (Real.sqrt_pos.2 hlogpos)]
  calc
    B * Real.sqrt (Real.log (n : ℝ)) ≤
        Real.sqrt (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hBn (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrtle (Real.sqrt_nonneg _)
    _ = (n : ℝ) := Real.mul_self_sqrt hnpos.le

theorem factorialCutoff_ratio_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (factorialCutoff n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  let s : ℕ → ℝ := fun n ↦ (n : ℝ) / Real.sqrt (Real.log (n : ℝ))
  have hsTop : Tendsto s atTop atTop := factorialScale_tendsto_atTop
  have hround : Tendsto (fun n : ℕ ↦ (⌈s n⌉₊ : ℝ) / s n)
      atTop (nhds 1) := tendsto_nat_ceil_div_atTop.comp hsTop
  have hsqrtTop : Tendsto (fun n : ℕ ↦ Real.sqrt (Real.log (n : ℝ)))
      atTop atTop := Real.tendsto_sqrt_atTop.comp tendsto_log_coe_at_top
  have hinv : Tendsto
      (fun n : ℕ ↦ (Real.sqrt (Real.log (n : ℝ)))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsqrtTop
  have hprod := hround.mul hinv
  convert hprod using 1
  · funext n
    by_cases hn : n = 0
    · simp [factorialCutoff, s, hn]
    by_cases hlog : Real.sqrt (Real.log (n : ℝ)) = 0
    · simp [factorialCutoff, s, hlog]
    simp only [factorialCutoff, s]
    field_simp
  · norm_num

private lemma eventually_sqrt_le_factorialBase :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (n : ℝ) ≤
        (factorialCutoff n : ℝ) * Real.exp (-1) := by
  have hlogdiv : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  have hsqrtzero : Tendsto
      (fun n : ℕ ↦ Real.sqrt (Real.log (n : ℝ) / (n : ℝ)))
      atTop (nhds 0) := by simpa using hlogdiv.sqrt
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.exp 1 * Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) ≤ 1 :=
    (hsqrtzero.const_mul (Real.exp 1)).eventually
      (eventually_le_nhds (by norm_num : Real.exp 1 * (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop 3] with n hsmalln hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hsqrtnpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsqrtlogpos : 0 < Real.sqrt (Real.log (n : ℝ)) :=
    Real.sqrt_pos.2 hlogpos
  have hsqrtdiv :
      Real.sqrt (Real.log (n : ℝ) / (n : ℝ)) =
        Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_div hlogpos.le]
  rw [hsqrtdiv] at hsmalln
  have hbase : Real.exp 1 * Real.sqrt (Real.log (n : ℝ)) ≤
      Real.sqrt (n : ℝ) := by
    have := mul_le_mul_of_nonneg_right hsmalln hsqrtnpos.le
    field_simp at this
    simpa [mul_assoc] using this
  have hlogroot : Real.sqrt (Real.log (n : ℝ)) ≤
      Real.sqrt (n : ℝ) * Real.exp (-1) := by
    calc
      Real.sqrt (Real.log (n : ℝ)) =
          (Real.exp 1 * Real.sqrt (Real.log (n : ℝ))) * Real.exp (-1) := by
        rw [mul_assoc, mul_comm (Real.sqrt _) (Real.exp (-1)),
          ← mul_assoc, ← Real.exp_add]
        norm_num
      _ ≤ Real.sqrt (n : ℝ) * Real.exp (-1) :=
        mul_le_mul_of_nonneg_right hbase (Real.exp_pos (-1)).le
  have hsle : (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) ≤
      (factorialCutoff n : ℝ) := by
    exact Nat.le_ceil _
  calc
    Real.sqrt (n : ℝ) =
        (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) *
          (Real.sqrt (Real.log (n : ℝ)) / Real.sqrt (n : ℝ)) := by
      field_simp
      nlinarith [Real.sq_sqrt hnpos.le]
    _ ≤ (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) * Real.exp (-1) :=
      mul_le_mul_of_nonneg_left
        ((div_le_iff₀ hsqrtnpos).2 (by simpa [mul_comm] using hlogroot))
        (div_nonneg hnpos.le hsqrtlogpos.le)
    _ ≤ (factorialCutoff n : ℝ) * Real.exp (-1) :=
      mul_le_mul_of_nonneg_right hsle (Real.exp_pos (-1)).le

/-- The factorial cutoff eventually exceeds the exponential LCM majorant. -/
theorem eventually_exp_two_mul_le_factorialCutoff_factorial :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (2 * n) ≤ (factorialCutoff n).factorial := by
  have hsqrtlogTop : Tendsto
      (fun n : ℕ ↦ Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_log_coe_at_top
  filter_upwards [eventually_sqrt_le_factorialBase,
    hsqrtlogTop.eventually (eventually_ge_atTop 4),
    eventually_ge_atTop 3] with n hbase hroot hn
  let t := factorialCutoff n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hrootpos : 0 < Real.sqrt (Real.log (n : ℝ)) :=
    Real.sqrt_pos.2 hlogpos
  have htle : (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) ≤ (t : ℝ) :=
    Nat.le_ceil _
  have hnle : (n : ℝ) ≤ (t : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by
    rw [div_le_iff₀ hrootpos] at htle
    simpa [mul_comm] using htle
  have hrootSq : (Real.sqrt (Real.log (n : ℝ))) ^ 2 =
      Real.log (n : ℝ) := Real.sq_sqrt hlogpos.le
  have hexponent : 2 * (n : ℝ) ≤
      Real.log (Real.sqrt (n : ℝ)) * (t : ℝ) := by
    rw [Real.log_sqrt hnpos.le]
    nlinarith
  have hsqrtpow : Real.exp (2 * (n : ℝ)) ≤
      (Real.sqrt (n : ℝ)) ^ t := by
    calc
      Real.exp (2 * (n : ℝ)) ≤
          Real.exp (Real.log (Real.sqrt (n : ℝ)) * (t : ℝ)) :=
        Real.exp_monotone hexponent
      _ = (Real.sqrt (n : ℝ)) ^ t := by
        rw [mul_comm, Real.exp_nat_mul, Real.exp_log (Real.sqrt_pos.2 hnpos)]
  have hpowbase : (Real.sqrt (n : ℝ)) ^ t ≤
      ((t : ℝ) * Real.exp (-1)) ^ t := by
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hbase t
  exact (hsqrtpow.trans hpowbase).trans
    (UnitFractions.factorial_bound t)

/-- The denominator-control statement used by the correction construction. -/
theorem eventually_initialLcm_le_factorialCutoff_factorial :
    ∀ᶠ n : ℕ in atTop,
      Erdos285.PrimePowers.initialLcm n ≤ (factorialCutoff n).factorial := by
  filter_upwards
    [Erdos285.Proposition7Mass.eventually_initialLcm_le_exp_two_mul,
      eventually_exp_two_mul_le_factorialCutoff_factorial]
      with n hlcm hfac
  exact_mod_cast hlcm.trans hfac

end

end Erdos284

#print axioms Erdos284.factorialCutoff_ratio_tendsto_zero
#print axioms Erdos284.eventually_initialLcm_le_factorialCutoff_factorial
