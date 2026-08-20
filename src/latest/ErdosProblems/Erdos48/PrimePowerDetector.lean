/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherCutoffMean

/-!
# Prime-power removal for Gallagher's cutoff detector

The unweighted von Mangoldt coefficient is split into its prime part and
the contribution of higher prime powers.  Chebyshev's explicit bound for
`psi - theta` gives a sharp square-energy estimate for the latter on each
dyadic detector shell.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open Complex

/-- The prime part of the unweighted Gallagher coefficient. -/
noncomputable def primeCutoffCoefficient (n : ℕ) : ℂ :=
  if n.Prime then cutoffVonMangoldtCoefficient n else 0

/-- The part of the unweighted Gallagher coefficient supported on prime
powers of exponent at least two. -/
noncomputable def higherPrimePowerCutoffCoefficient (n : ℕ) : ℂ :=
  if n.Prime then 0 else cutoffVonMangoldtCoefficient n

theorem cutoffVonMangoldtCoefficient_eq_prime_add_higher (n : ℕ) :
    cutoffVonMangoldtCoefficient n =
      primeCutoffCoefficient n + higherPrimePowerCutoffCoefficient n := by
  by_cases hn : n.Prime <;>
    simp [primeCutoffCoefficient, higherPrimePowerCutoffCoefficient, hn]

theorem cutoffPolynomial_eq_prime_add_higher
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : Finset ℕ) (t : ℝ) :
    (∑ n ∈ s, cutoffVonMangoldtCoefficient n * chi n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) =
      (∑ n ∈ s, primeCutoffCoefficient n * chi n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ))) +
      ∑ n ∈ s, higherPrimePowerCutoffCoefficient n * chi n *
        Complex.exp (I * (((-t * Real.log n) : ℝ) : ℂ)) := by
  simp_rw [cutoffVonMangoldtCoefficient_eq_prime_add_higher]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem norm_higherPrimePowerCutoffCoefficient_sq (n : ℕ) :
    ‖higherPrimePowerCutoffCoefficient n‖ ^ 2 =
      if n.Prime then 0 else
        ArithmeticFunction.vonMangoldt n ^ 2 * ((n : ℝ)⁻¹) ^ 2 := by
  by_cases hn : n.Prime
  · simp [higherPrimePowerCutoffCoefficient, hn]
  · rw [higherPrimePowerCutoffCoefficient, if_neg hn,
      cutoffVonMangoldtCoefficient]
    rw [Complex.norm_real, Real.norm_of_nonneg (by
      exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))]
    simp only [hn, if_false]
    ring

/-- Sharp square energy of the higher-prime-power coefficient on one
dyadic shell. -/
theorem sum_detectorDyadicShell_higherPrimePower_energy_le
    (Y N a : ℕ) (hY : 1 ≤ Y) :
    (∑ n ∈ detectorDyadicShell Y N a,
        ‖higherPrimePowerCutoffCoefficient n‖ ^ 2) ≤
      2 * ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ 2) *
        Real.sqrt (2 * (2 ^ a : ℕ)) * (((2 ^ a : ℕ) : ℝ)⁻¹) ^ 2 := by
  let A : ℕ := 2 ^ a
  let P : ℝ := ((a + 1 : ℕ) : ℝ) * Real.log 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpoint (n : ℕ) (hn : n ∈ detectorDyadicShell Y N a) :
      ‖higherPrimePowerCutoffCoefficient n‖ ^ 2 ≤
        P * (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) *
          ((A : ℝ)⁻¹) ^ 2 := by
    have hnBounds := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N a hY hn)
    have hnPos : (0 : ℝ) < n := by exact_mod_cast (hA.trans hnBounds.1)
    have hnUpper : (n : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hnBounds.2
    have hlog : ArithmeticFunction.vonMangoldt n ≤ P := by
      calc
        ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
          ArithmeticFunction.vonMangoldt_le_log
        _ ≤ Real.log (2 * (A : ℝ)) := Real.log_le_log hnPos hnUpper
        _ = P := by
          dsimp [A, P]
          rw [show (2 : ℝ) * (2 ^ a : ℕ) = (2 : ℝ) ^ (a + 1) by
            push_cast
            rw [pow_succ]
            ring]
          rw [Real.log_pow]
    have hinv : ((n : ℝ)⁻¹) ^ 2 ≤ ((A : ℝ)⁻¹) ^ 2 := by
      gcongr
      exact_mod_cast hnBounds.1.le
    rw [norm_higherPrimePowerCutoffCoefficient_sq]
    split_ifs with hnPrime
    · positivity
    · have hsquare : ArithmeticFunction.vonMangoldt n ^ 2 ≤
          P * ArithmeticFunction.vonMangoldt n := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right hlog
          ArithmeticFunction.vonMangoldt_nonneg
      exact mul_le_mul hsquare hinv (by positivity) (by positivity)
  have hsupport :
      (∑ n ∈ detectorDyadicShell Y N a,
          if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) ≤
        Chebyshev.psi ((2 * A : ℕ) : ℝ) -
          Chebyshev.theta ((2 * A : ℕ) : ℝ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
    rw [show (∑ n ∈ detectorDyadicShell Y N a,
        if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) =
        ∑ n ∈ (detectorDyadicShell Y N a).filter (fun n ↦ ¬n.Prime),
          ArithmeticFunction.vonMangoldt n by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnPrime : n.Prime <;> simp [hnPrime]]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnShell := Finset.mem_Ioc.mp
        (detectorDyadicShell_subset Y N a hY hnData.1)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨by omega, hnShell.2⟩, hnData.2⟩
    · intro n hn hnot
      exact ArithmeticFunction.vonMangoldt_nonneg
  have htwoA : (1 : ℝ) ≤ ((2 * A : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * A by omega)
  have hgap := Chebyshev.psi_sub_theta_le
    (x := ((2 * A : ℕ) : ℝ)) htwoA
  have hlogEq : Real.log (((2 * A : ℕ) : ℝ)) = P := by
    dsimp [A, P]
    rw [show (((2 * 2 ^ a : ℕ) : ℝ)) = (2 : ℝ) ^ (a + 1) by
      push_cast
      rw [pow_succ]
      ring]
    rw [Real.log_pow]
  calc
    (∑ n ∈ detectorDyadicShell Y N a,
        ‖higherPrimePowerCutoffCoefficient n‖ ^ 2) ≤
      ∑ n ∈ detectorDyadicShell Y N a,
        P * (if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) *
          ((A : ℝ)⁻¹) ^ 2 := Finset.sum_le_sum hpoint
    _ = P * (∑ n ∈ detectorDyadicShell Y N a,
          if n.Prime then 0 else ArithmeticFunction.vonMangoldt n) *
            ((A : ℝ)⁻¹) ^ 2 := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ P * (Chebyshev.psi ((2 * A : ℕ) : ℝ) -
          Chebyshev.theta ((2 * A : ℕ) : ℝ)) * ((A : ℝ)⁻¹) ^ 2 := by
      gcongr
    _ ≤ P * (2 * Real.sqrt ((2 * A : ℕ) : ℝ) *
          Real.log ((2 * A : ℕ) : ℝ)) * ((A : ℝ)⁻¹) ^ 2 := by
      gcongr
    _ = 2 * P ^ 2 * Real.sqrt (2 * (A : ℝ)) * ((A : ℝ)⁻¹) ^ 2 := by
      rw [hlogEq]
      push_cast
      ring
    _ = _ := by rfl

end Erdos48
