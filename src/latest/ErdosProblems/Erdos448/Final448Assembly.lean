import ErdosProblems.Erdos448.Prop3Assembly448
import ErdosProblems.Erdos448.Prop4Summation448

open Filter Finset
open scoped BigOperators Topology

namespace Erdos448FinalAssembly

open Erdos448Prop3Assembly

lemma naturalGridSelectedPairTerm_nonneg (K n : ℕ) :
    0 ≤ naturalGridSelectedPairTerm K n := by
  unfold naturalGridSelectedPairTerm
  positivity

/-- The final density conclusion, isolated from the last analytic first-moment
estimate.  The latter will be supplied uniformly for the selector parameter. -/
theorem erdos_448_of_naturalGrid_linear_moment
    (hlinear : ∀ K : ℕ, 0 < K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ x : ℕ in atTop,
        (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤ C * x) :
    ¬ ∀ ε : ℝ, 0 < ε →
        {n : ℕ | (Erdos448.tauPlus n : ℝ) <
          ε * (n.divisors.card : ℝ)}.HasDensity 1 := by
  rcases NaturalGridConcentration448.exists_naturalGrid_goodSet with
    ⟨K, hK, hG⟩
  rcases hlinear K hK with ⟨C, hC, hsum⟩
  apply Erdos448.erdos_448_of_exists_strict_upperDensity
  apply Erdos448.exists_strict_upperDensity_of_fixed_moment_package
    (NaturalGridConcentration448.naturalGridFourFifthsSet K)
    (naturalGridSelectedPairTerm K) C hC hG
  · intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [naturalGridSelectedPairTerm, Erdos448.tauPlus]
    · simpa [naturalGridSelectedPairTerm] using
        (Erdos448.four_fifths_tau_div_tauPlus_le_normalized_closePairs
          hn0
          (NaturalGridConcentration448.naturalGridSelectedDivisors_subset K n)
          hn)
  · exact naturalGridSelectedPairTerm_nonneg K
  · exact hsum

end Erdos448FinalAssembly
