import ErdosProblems.Erdos157.PolynomialInverseRoots
import ErdosProblems.Erdos157.EulerPositivity

/-! The inverse-root power sums as coefficients of the logarithmic derivative. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial ElementaryCharacterBound
open scoped BigOperators

noncomputable def rootPowerCoefficient {m : ℕ} (α : Fin m → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else -(∑ i, α i ^ n)

theorem hasSum_rootPowerCoefficient {m : ℕ} (α : Fin m → ℂ) (z : ℂ)
    (hα : ∀ i, ‖α i * z‖ < 1) :
    HasSum (fun n => rootPowerCoefficient α n * z ^ n)
      (∑ i, contribution (α i * z)) := by
  have hi : ∀ i : Fin m, HasSum (fun n : ℕ => -((α i * z) ^ (n + 1)))
      (contribution (α i * z)) := by
    intro i
    simpa only [contribution, neg_div] using (hasSum_geometric_succ (hα i)).neg
  have hs : HasSum (fun n : ℕ => ∑ i, -((α i * z) ^ (n + 1)))
      (∑ i, contribution (α i * z)) := hasSum_sum (fun i _ => hi i)
  have hshift : HasSum (fun n : ℕ => rootPowerCoefficient α (n + 1) * z ^ (n + 1))
      (∑ i, contribution (α i * z)) := by
    apply hs.congr_fun
    intro n
    simp [rootPowerCoefficient, mul_pow, Finset.sum_mul, Finset.sum_neg_distrib, neg_mul]
  apply (hasSum_nat_add_iff' 1).mp
  simpa [rootPowerCoefficient] using hshift

theorem summable_norm_rootPowerCoefficient {m : ℕ} (α : Fin m → ℂ)
    (r : ℝ) (hr : 0 ≤ r) (hα : ∀ i, ‖α i‖ * r < 1) :
    Summable (fun n => ‖rootPowerCoefficient α n‖ * r ^ n) := by
  have hs : Summable (fun n : ℕ => ∑ i, (‖α i‖ * r) ^ n) :=
    summable_sum (fun i _ => summable_geometric_of_lt_one (by positivity) (hα i))
  apply Summable.of_nonneg_of_le (fun n => by positivity) (g := fun n => ‖rootPowerCoefficient α n‖ * r ^ n)
    (f := fun n : ℕ => ∑ i, (‖α i‖ * r) ^ n)
  · intro n
    by_cases hn : n = 0
    · simp [rootPowerCoefficient, hn]
    · rw [rootPowerCoefficient, if_neg hn, norm_neg]
      calc
        _ ≤ (∑ i, ‖α i ^ n‖) * r ^ n :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
        _ = _ := by simp [Finset.sum_mul, norm_pow, mul_pow]
  · exact hs

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

theorem hasSum_lPolynomial_rootPowerCoefficient (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    HasSum (fun n => rootPowerCoefficient (inverseRootAt (lPolynomial g χ)) n * z ^ n)
      (z * ((lPolynomial g χ).derivative.eval z / (lPolynomial g χ).eval z)) := by
  rw [inverseRoots_logDerivative (lPolynomial g χ) (lPolynomial_constantCoeff g hg χ hχ) z
    (lPolynomial_eval_ne_zero g hg χ hχ z hz)]
  apply hasSum_rootPowerCoefficient
  intro i
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (lPolynomial_inverseRoot_norm_le g hg χ hχ i)
    (norm_nonneg z)).trans_lt hz

end Erdos157.Elementary.PolynomialCharacters
