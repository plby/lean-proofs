/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CentralChebyshevApplication
import ErdosProblems.Erdos378.ReciprocalPrimeSelection

/-!
# Removing prime powers from weighted Chebyshev intervals
-/

open Filter
open Asymptotics
open scoped Topology BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace PrimeWeightedInterval

open PrimeReciprocal
open CentralChebyshev
open CentralChebyshevApplication
open ReciprocalChebyshevAsymptotic
open InverseSquareChebyshev
open InverseSquareCorrelation
open InverseSquareChebyshevAsymptotic
open InverseSquareChebyshevApplication
open InverseSquareChebyshevLimit
open ReciprocalPrimeSelection

noncomputable section

def primeWeightedInterval (w : ℕ → ℂ) (a b : ℕ) : ℂ :=
  ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * w p

private lemma weightedChebyshevInterval_eq_prime_add_nonprime
    (w : ℕ → ℂ) (a b : ℕ) :
    weightedChebyshevInterval w a b =
      primeWeightedInterval w a b +
        ∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ ↦ ¬n.Prime),
          (ArithmeticFunction.vonMangoldt n : ℂ) * w n := by
  unfold weightedChebyshevInterval primeWeightedInterval
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.Ioc a b) (fun n : ℕ ↦ n.Prime)]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  exact congrArg (fun z : ℝ ↦ (z : ℂ) * w p)
    (ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2)

lemma norm_primeWeightedInterval_sub_weighted_le
    (w : ℕ → ℂ) (hw : ∀ n, ‖w n‖ ≤ 1) (a b : ℕ) :
    ‖primeWeightedInterval w a b - weightedChebyshevInterval w a b‖ ≤
      Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ) := by
  rw [weightedChebyshevInterval_eq_prime_add_nonprime]
  simp only [sub_add_cancel_left, norm_neg]
  calc
    ‖∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ ↦ ¬n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℂ) * w n‖ ≤
      ∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ ↦ ¬n.Prime),
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * w n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Ioc a b).filter (fun n : ℕ ↦ ¬n.Prime),
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      simpa using mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
        (hw n)
    _ ≤ ∑ n ∈ (Finset.Ioc 0 b).filter (fun n : ℕ ↦ ¬n.Prime),
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rcases Finset.mem_filter.mp hn with ⟨hnab, hnprime⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
          ⟨Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hnab).1,
            (Finset.mem_Ioc.mp hnab).2⟩, hnprime⟩
      · intro n hn hnnot
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ = Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ) := by
      rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
      simp

lemma norm_primeWeightedInterval_le
    {w : ℕ → ℂ} (hw : ∀ n, ‖w n‖ ≤ 1) {a b : ℕ} {R : ℝ}
    (hcheb : ‖weightedChebyshevInterval w a b‖ ≤ R) :
    ‖primeWeightedInterval w a b‖ ≤
      R + (Chebyshev.psi (b : ℝ) - Chebyshev.theta (b : ℝ)) := by
  have hdiff := norm_primeWeightedInterval_sub_weighted_le w hw a b
  have hdecomp : primeWeightedInterval w a b =
      (primeWeightedInterval w a b - weightedChebyshevInterval w a b) +
        weightedChebyshevInterval w a b := by ring
  rw [hdecomp]
  exact (norm_add_le _ _).trans (add_le_add hdiff hcheb) |>.trans (by linarith)

def centralPrimeMajorant (y : ℕ) : ℝ :=
  centralChebyshevMajorant y (reciprocalVaughanCutoff y)
    (centralTypeBound y) (centralUniformDelta y) +
      (Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ))

private theorem tendsto_chebyshevPsi_nat_ratio :
    Tendsto (fun n : ℕ ↦ Chebyshev.psi (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp
    BoundedGaps.PrimeNumberTheorem.chebyshevPsi_natCast_isEquivalent
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact_mod_cast (show n ≠ 0 by omega)

private theorem tendsto_chebyshevTheta_nat_ratio :
    Tendsto (fun n : ℕ ↦ Chebyshev.theta (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  apply (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp
    BoundedGaps.PrimeNumberTheorem.chebyshevTheta_natCast_isEquivalent
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact_mod_cast (show n ≠ 0 by omega)

theorem tendsto_centralPrimeMajorant_div_zero :
    Tendsto (fun y : ℕ ↦ centralPrimeMajorant y / (y : ℝ))
      atTop (nhds 0) := by
  have hprime : Tendsto (fun y : ℕ ↦
      (Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ)) / (y : ℝ))
      atTop (nhds 0) := by
    have hpsi := tendsto_chebyshevPsi_nat_ratio
    have htheta := tendsto_chebyshevTheta_nat_ratio
    convert hpsi.sub htheta using 1
    · funext y
      by_cases hy : y = 0
      · simp [hy]
      field_simp
    · norm_num
  unfold centralPrimeMajorant
  convert tendsto_centralChebyshevMajorant_div_zero.add hprime using 1
  · funext y
    rw [add_div]
  · norm_num

def inverseSquarePrimeMajorant (y : ℕ) : ℝ :=
  inverseSquareChebyshevMajorant y (reciprocalVaughanCutoff y)
    (inverseSquareCorrelationCap y) (inverseSquareTypeBound y)
    (inverseSquareAsymptoticDelta y) +
      (Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ))

theorem tendsto_inverseSquarePrimeMajorant_div_zero :
    Tendsto (fun y : ℕ ↦ inverseSquarePrimeMajorant y / (y : ℝ))
      atTop (nhds 0) := by
  have hprime : Tendsto (fun y : ℕ ↦
      (Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ)) / (y : ℝ))
      atTop (nhds 0) := by
    have hpsi := tendsto_chebyshevPsi_nat_ratio
    have htheta := tendsto_chebyshevTheta_nat_ratio
    convert hpsi.sub htheta using 1
    · funext y
      by_cases hy : y = 0
      · simp [hy]
      field_simp
    · norm_num
  unfold inverseSquarePrimeMajorant
  convert tendsto_uniform_inverseSquareChebyshev_bound_div_zero.add hprime using 1
  · funext y
    rw [add_div]
  · norm_num

theorem eventually_centralPrime_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * X → X ≤ (y : ℝ) ^ 16 →
      ‖primeWeightedInterval (reciprocalWeight X) x y‖ ≤
        centralPrimeMajorant y := by
  filter_upwards [eventually_centralChebyshev_bound] with y hy
  intro x X hxy hyx hX hXlo hXhi
  apply norm_primeWeightedInterval_le
  · intro n
    simp
  · exact hy hxy hyx hX hXlo hXhi

theorem eventually_inverseSquarePrime_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * X → X ≤ (y : ℝ) ^ 16 →
      (inverseSquareCorrelationCap y : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X →
      ‖primeWeightedInterval (inverseSquareWeight X) x y‖ ≤
        inverseSquarePrimeMajorant y := by
  filter_upwards [eventually_inverseSquareChebyshev_bound] with y hy
  intro x X hxy hyx hX hXlo hXhi hXratio
  apply norm_primeWeightedInterval_le
  · intro n
    simp
  · exact hy hxy hyx hX hXlo hXhi hXratio

end

end PrimeWeightedInterval
end Erdos378
