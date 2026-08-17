import ErdosProblems.Erdos121.MarginalLarge

/-! # Elementary comparison of the total and marginal masses -/

open Filter
open scoped BigOperators Topology

namespace Erdos121

set_option autoImplicit false

noncomputable section

def k5PrimeConstant : ℝ :=
  Classical.choose Erdos888.exists_forall_dyadicPrimeCount_le_scale

def k5EulerRatioConstant : ℝ :=
  Real.exp (5 * Erdos469.naturalSquareSeries) *
    Erdos469.naturalLinearMertensUpper

def k5MarginalConstant : ℝ :=
  4 * k5EulerRatioConstant * (800 * k5PrimeConstant) ^ 6 *
    200 ^ 10 * 4000000 * 100000000 ^ 3

lemma k5PrimeConstant_pos : 0 < k5PrimeConstant :=
  (Classical.choose_spec
    Erdos888.exists_forall_dyadicPrimeCount_le_scale).1

lemma k5EulerRatioConstant_pos : 0 < k5EulerRatioConstant := by
  apply mul_pos (Real.exp_pos _)
  exact Erdos469.naturalLinearMertensUpper_pos

lemma k5MarginalConstant_pos : 0 < k5MarginalConstant := by
  dsimp [k5MarginalConstant]
  have hE := k5EulerRatioConstant_pos
  have hA := k5PrimeConstant_pos
  positivity

lemma log_smallCutoff (U : ℕ) :
    Real.log (smallCutoff U : ℝ) =
      ((U / 1000000 : ℕ) : ℝ) * Real.log 2 := by
  rw [smallCutoff]
  convert Real.log_pow (2 : ℝ) (U / 1000000) using 1 <;> norm_num

lemma log_smallCutoff_lower {U : ℕ} (hU : 4000000 ≤ U) :
    (U : ℝ) ≤ 4000000 * Real.log (smallCutoff U : ℝ) := by
  have hq : 2 ≤ U / 1000000 := by omega
  have hUq : U ≤ 2000000 * (U / 1000000) := by omega
  have hUqR : (U : ℝ) ≤
      2000000 * ((U / 1000000 : ℕ) : ℝ) := by
    exact_mod_cast hUq
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  rw [log_smallCutoff]
  have hqR : (0 : ℝ) ≤ (U / 1000000 : ℕ) := by positivity
  nlinarith

lemma scale_le_parameter (U : ℕ) :
    U ≤ 100000000 * (U / 100000000 + 1) := by omega

private lemma real_coefficient_comparison
    {u r L n E A : ℝ}
    (hu : 0 < u) (hr : 0 < r) (hL : 0 < L) (hn : 0 < n)
    (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hur : u ≤ 100000000 * r) (huL : u ≤ 4000000 * L) :
    2 * r ^ 2 * (800 * A / u) ^ 6 / n * (E / L) ≤
      (4 * E * (800 * A) ^ 6 * 200 ^ 10 * 4000000 *
          100000000 ^ 3) / n *
        ((1 / 2 : ℝ) * r ^ 5 * (1 / (200 * u)) ^ 10) := by
  have hu3 : u ^ 3 ≤ (100000000 * r) ^ 3 := by
    gcongr
  have hu4 : u ^ 4 ≤
      (4000000 * 100000000 ^ 3) * (L * r ^ 3) := by
    calc
      u ^ 4 = u * u ^ 3 := by ring
      _ ≤ (4000000 * L) * (100000000 * r) ^ 3 := by
        exact mul_le_mul huL hu3 (by positivity) (by positivity)
      _ = (4000000 * 100000000 ^ 3) * (L * r ^ 3) := by ring
  have hratio : u ^ 4 / (L * r ^ 3) ≤
      4000000 * 100000000 ^ 3 := by
    apply (div_le_iff₀ (mul_pos hL (pow_pos hr 3))).2
    nlinarith
  have hid :
      2 * r ^ 2 * (800 * A / u) ^ 6 / n * (E / L) =
        (4 * E * (800 * A) ^ 6 * 200 ^ 10 / n) *
          (u ^ 4 / (L * r ^ 3)) *
          ((1 / 2 : ℝ) * r ^ 5 * (1 / (200 * u)) ^ 10) := by
    field_simp
    ring
  rw [hid]
  have hfac : 0 ≤ 4 * E * (800 * A) ^ 6 * 200 ^ 10 / n := by
    positivity
  have hbase : 0 ≤ (1 / 2 : ℝ) * r ^ 5 * (1 / (200 * u)) ^ 10 := by
    positivity
  calc
    (4 * E * (800 * A) ^ 6 * 200 ^ 10 / n) *
          (u ^ 4 / (L * r ^ 3)) *
          ((1 / 2 : ℝ) * r ^ 5 * (1 / (200 * u)) ^ 10) ≤
        (4 * E * (800 * A) ^ 6 * 200 ^ 10 / n) *
          (4000000 * 100000000 ^ 3) *
          ((1 / 2 : ℝ) * r ^ 5 * (1 / (200 * u)) ^ 10) := by
      gcongr
    _ = _ := by ring

/-- Each point mass is bounded by a fixed multiple of `1/n` times the total
mass.  This is the quantitative form used by the union bound. -/
theorem eventually_k5Marginal_le_total :
    ∀ᶠ U : ℕ in atTop, ∀ n : ℕ, 0 < n → ∀ v : Fin 5,
      (k5Weight U).mass (fun ω => k5OutcomeTuple ω v = n) ≤
        k5MarginalConstant / n * (k5Weight U).mass (fun _ => True) := by
  filter_upwards [eventually_dyadicPrimeMass_bounds_on_scale,
    eventually_k5TotalMass_lower, eventually_ge_atTop 1000000000]
      with U hprime htotal hU
  intro n hn v
  have hU4 : 4000000 ≤ U := by omega
  have hY : 2 ≤ smallCutoff U := by
    rw [smallCutoff]
    exact Nat.one_lt_two_pow (by omega)
  have hlogPos : 0 < Real.log (smallCutoff U : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < smallCutoff U by omega)
  have hmarg := k5Marginal_le hn hU (fun b hb hbU => (hprime b hb hbU).2) v
  have heuler := smallEuler_six_le_ten_div_log hY
  have hpre :
      (k5Weight U).mass (fun ω => k5OutcomeTuple ω v = n) ≤
        ((2 * (U / 100000000 + 1) ^ 2 : ℕ) : ℝ) *
          ((800 * k5PrimeConstant) / U) ^ 6 / n *
          ((k5EulerRatioConstant / Real.log (smallCutoff U : ℝ)) *
            smallEuler 10 (smallCutoff U)) := by
    apply hmarg.trans
    apply mul_le_mul_of_nonneg_left heuler
    positivity
  have hcoeff := real_coefficient_comparison
    (u := (U : ℝ))
    (r := ((U / 100000000 + 1 : ℕ) : ℝ))
    (L := Real.log (smallCutoff U : ℝ)) (n := (n : ℝ))
    (E := k5EulerRatioConstant) (A := k5PrimeConstant)
    (by positivity) (by positivity) hlogPos (by positivity)
    k5EulerRatioConstant_pos.le k5PrimeConstant_pos.le
    (by exact_mod_cast scale_le_parameter U)
    (log_smallCutoff_lower hU4)
  have hcoeff' :
      ((2 * (U / 100000000 + 1) ^ 2 : ℕ) : ℝ) *
          ((800 * k5PrimeConstant) / U) ^ 6 / n *
          (k5EulerRatioConstant / Real.log (smallCutoff U : ℝ)) ≤
        k5MarginalConstant / n *
          ((1 / 2 : ℝ) *
            ((U / 100000000 + 1 : ℕ) : ℝ) ^ 5 *
            ((1 : ℝ) / (200 * U)) ^ 10) := by
    simpa [k5MarginalConstant, mul_assoc] using hcoeff
  calc
    (k5Weight U).mass (fun ω => k5OutcomeTuple ω v = n) ≤
        (((2 * (U / 100000000 + 1) ^ 2 : ℕ) : ℝ) *
          ((800 * k5PrimeConstant) / U) ^ 6 / n *
          (k5EulerRatioConstant / Real.log (smallCutoff U : ℝ))) *
            smallEuler 10 (smallCutoff U) := by
      simpa [mul_assoc] using hpre
    _ ≤ (k5MarginalConstant / n *
          ((1 / 2 : ℝ) *
            ((U / 100000000 + 1 : ℕ) : ℝ) ^ 5 *
            ((1 : ℝ) / (200 * U)) ^ 10)) *
          smallEuler 10 (smallCutoff U) := by
      exact mul_le_mul_of_nonneg_right hcoeff'
        (smallEuler_pos 10 (smallCutoff U)).le
    _ = k5MarginalConstant / n *
          ((smallEuler 10 (smallCutoff U) / 2) *
            ((U / 100000000 + 1 : ℕ) : ℝ) ^ 5 *
            ((1 : ℝ) / (200 * U)) ^ 10) := by ring
    _ ≤ k5MarginalConstant / n *
        (k5Weight U).mass (fun _ => True) := by
      exact mul_le_mul_of_nonneg_left htotal
        (div_nonneg k5MarginalConstant_pos.le (by positivity))

end

end Erdos121
