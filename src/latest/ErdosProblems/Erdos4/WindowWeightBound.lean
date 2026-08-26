import ErdosProblems.Erdos4.DivisibilityExpansion
import ErdosProblems.Erdos4.ReciprocalTail

/-!
# Uniform coefficient and weight bounds after a fixed prime cutoff

The convergent reciprocal-square tail supplies the cutoff independently
of every outer radius and every source or center. The cutoff may be
enlarged afterward, so these bounds can be combined with the principal
gain and nonprincipal Fourier requirements.
-/

open scoped BigOperators

namespace Erdos4.WindowWeightBound

open ArithmeticFibers LocalIndicatorExpansion DivisibilityExpansion

instance primeWindow_factPrime (K R : ℕ) (p : primeWindow K R) : Fact (p : ℕ).Prime :=
  ⟨(mem_primeWindow.mp p.property).1⟩

theorem exists_tail_cutoff (k : ℕ) :
    ∃ K₀ : ℕ, k + 2 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ R : ℕ,
      (k : ℝ) * rowCost k * (∑ p : primeWindow K R, 1 / (p : ℝ) ^ 2) ≤ 1 := by
  let c : ℝ := (k : ℝ) * rowCost k
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg k) (rowCost_nonneg k)
  have hε : 0 < 1 / (c + 1) := by positivity
  obtain ⟨K₁, _hK₁, htail⟩ := ReciprocalTail.exists_reciprocal_square_cutoff hε
  refine ⟨max K₁ (k + 2), le_max_right _ _, ?_⟩
  intro K hK R
  have hK₁ : K₁ ≤ K := (le_max_left K₁ (k + 2)).trans hK
  have hh := (htail (primeWindow K R) (fun p hp =>
    lt_of_le_of_lt hK₁ (mem_primeWindow.mp hp).2.1)).2.le
  have hprod := (le_div_iff₀ (by positivity : 0 < c + 1)).mp hh
  have hsum : 0 ≤ ∑ p ∈ primeWindow K R, 1 / (p : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun p _hp => div_nonneg zero_le_one (sq_nonneg _))
  rw [Finset.sum_coe_sort (primeWindow K R) (fun p : ℕ => 1 / (p : ℝ) ^ 2)]
  change c * _ ≤ 1
  nlinarith

/-- The total absolute divisor coefficient mass is at most `exp(1) R²`,
and each actual affine weight is at most `exp(1)² R⁴`. No further
condition on a reciprocal tail is left in the conclusion. -/
theorem exists_uniform_bounds {m : ℝ} (hm : 1 ≤ m) (k : ℕ) :
    ∃ K₀ : ℕ, k + 2 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → ∀ R : ℕ, 2 ≤ R →
      (∑ b : primeWindow K R → Option (Fin k),
        |divisorCoefficient m R (fun p : primeWindow K R => (p : ℕ)) b|) ≤
          Real.exp 1 * (R : ℝ) ^ 2 ∧
      ∀ (Y W : ℕ) (h : Fin k → ℕ) (p n : ℕ),
        AffineWeights.weight (fun l : primeWindow K R => (l : ℕ)) m R Y W h p n ≤
          Real.exp 1 ^ 2 * (R : ℝ) ^ 4 := by
  obtain ⟨K₀, hK₀, htail⟩ := exists_tail_cutoff k
  refine ⟨K₀, hK₀, ?_⟩
  intro K hK R hR
  let ell : primeWindow K R → ℕ := fun p => p
  have hell : ∀ p, k + 2 ≤ ell p := fun p =>
    (hK₀.trans hK).trans (mem_primeWindow.mp p.property).2.1.le
  have ht : (k : ℝ) * rowCost k * ∑ p, 1 / (ell p : ℝ) ^ 2 ≤ 1 := htail K hK R
  constructor
  · exact (sum_abs_coefficient_le_mass hm hR ell hell).trans
      (CutoffMass.mass_le_of_small_tail R ell (fun p => by have := hell p; omega)
        (rowCost_nonneg k) ht)
  · intro Y W h p n
    exact weight_le_of_small_tail hm hR ell hell ht Y W h p n

end Erdos4.WindowWeightBound
