import ErdosProblems.Erdos67.StationaryWiener
import ErdosProblems.Erdos67.MRTFourPrimeBound

/-!
# Finite energy of correlation sums over primes

The first moment is bounded by the coordinate second moment. Ordered pairs
are then grouped by their nonnegative differences, ready for the proved
prime-pair square-sum sieve bound.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

theorem square_integral_le_integral_square (Q : ProbabilityMeasure Configuration)
    (F : Configuration → ℝ) (hF : Continuous F) :
    (∫ ω, F ω ∂(Q : Measure Configuration)) ^ 2 ≤
      ∫ ω, F ω ^ 2 ∂(Q : Measure Configuration) := by
  let a := ∫ ω, F ω ∂(Q : Measure Configuration)
  have hn : 0 ≤ ∫ ω, (F ω - a) ^ 2 ∂(Q : Measure Configuration) :=
    integral_nonneg fun ω ↦ sq_nonneg _
  have he (ω : Configuration) : (F ω - a) ^ 2 = F ω ^ 2 - (2 * a) * F ω + a ^ 2 := by ring
  simp_rw [he] at hn
  rw [integral_add, integral_sub, integral_const_mul, integral_const] at hn
  · simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hn
    dsimp [a] at hn
    nlinarith
  · exact integrable_configuration_continuous Q _ (hF.pow 2)
  · exact (integrable_configuration_continuous Q F hF).const_mul _
  · exact (integrable_configuration_continuous Q _ (hF.pow 2)).sub
      ((integrable_configuration_continuous Q F hF).const_mul _)
  · exact integrable_const _

theorem finite_correlation_sum_square_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (A : Finset ℕ) (d : ℕ) :
    (∑ p ∈ A, correlation Q ((d * p : ℕ) : ℤ)) ^ 2 ≤
      ∑ p ∈ A, ∑ q ∈ A, correlation Q (((d * p : ℕ) : ℤ) - ((d * q : ℕ) : ℤ)) := by
  let F : Configuration → ℝ := fun ω ↦ coordinate 0 ω * ∑ p ∈ A, coordinate (d * p : ℕ) ω
  have hF : Continuous F := (continuous_coordinate 0).mul
    (continuous_finsetSum _ fun p _ ↦ continuous_coordinate _)
  have hfirst : (∫ ω, F ω ∂(Q : Measure Configuration)) =
      ∑ p ∈ A, correlation Q ((d * p : ℕ) : ℤ) := by
    simp only [F, mul_sum]
    rw [integral_finsetSum]
    · rfl
    · intro p _
      exact integrable_configuration_continuous Q _
        ((continuous_coordinate 0).mul (continuous_coordinate _))
  have hsecond : (∫ ω, F ω ^ 2 ∂(Q : Measure Configuration)) =
      ∑ p ∈ A, ∑ q ∈ A, correlation Q (((d * p : ℕ) : ℤ) - ((d * q : ℕ) : ℤ)) := by
    simp only [F, mul_pow, sq_coordinate, one_mul]
    simp only [pow_two, sum_mul, mul_sum]
    rw [integral_finsetSum]
    · apply sum_congr rfl
      intro p _
      rw [integral_finsetSum]
      · apply sum_congr rfl
        intro q _
        calc
          _ = ∫ ω, coordinate (d * p : ℕ) ω * coordinate (d * q : ℕ) ω
              ∂(Q : Measure Configuration) := integral_congr_ae
            (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)
          _ = _ := integral_coordinate_pair_nat Q hQ _ _
      · intro q _
        exact integrable_configuration_continuous Q _
          ((continuous_coordinate _).mul (continuous_coordinate _))
    · intro p _
      exact integrable_configuration_continuous Q _ (continuous_finsetSum _ fun q _ ↦
        (continuous_coordinate _).mul (continuous_coordinate _))
  rw [← hfirst, ← hsecond]
  exact square_integral_le_integral_square Q F hF

end Erdos67.StationaryModel
