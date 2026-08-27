/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourcePrimeSieve
import ErdosProblems.Erdos4b.FGKMTInitialSurvivorDecomposition
import ErdosProblems.Erdos4b.FGKMTInitialSourceRanges

/-! # An actual interval residue sieve, with only the smooth exception left to bound -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def sourceIntegerSurvivors (a c : ℝ) (x : ℕ)
    (b : ResidueAssignment (sourceSmallPrimes a x))
    (r : ResidueAssignment (commonPinnedPrimeSet (x / 2) x)) : Finset ℕ :=
  initialResidueSurvivors x ⌊sourceIntervalLength c x⌋₊
    (zeroExtendedResidue (sourceSmallPrimes a x) (commonPinnedPrimeSet (x / 2) x) b r)

theorem eventually_source_integer_survivors_decomposition {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ (b : ResidueAssignment (sourceSmallPrimes a x))
      (r : ResidueAssignment (commonPinnedPrimeSet (x / 2) x)),
      sourceIntegerSurvivors a c x b r ⊆
        Nat.smoothNumbersUpTo ⌊sourceIntervalLength c x⌋₊ (⌊sourceSmallPrimeUpper a x⌋₊ + 1) ∪
          naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x)
            (sourceSurvivorVertices a c x b) r := by
  filter_upwards [eventually_source_rounded_initial_ranges ha hc] with x hx b r
  exact initialResidueSurvivors_subset_smooth_union_prime hx.1 hx.2.1 hx.2.2 b r

theorem exists_source_initial_sieve {a : ℝ} (ha : 0 < a) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ᶠ x : ℕ in atTop,
      ∃ r : ℕ → ℕ,
        ((initialResidueSurvivors x ⌊sourceIntervalLength c x⌋₊ r).card : ℝ) ≤
          (Nat.smoothNumbersUpTo ⌊sourceIntervalLength c x⌋₊
            (⌊sourceSmallPrimeUpper a x⌋₊ + 1)).card + K * x / Real.log (x : ℝ) := by
  obtain ⟨c, K, hc, hK, hprime⟩ := exists_source_prime_sieve ha
  refine ⟨c, K, hc, hK, ?_⟩
  filter_upwards [hprime, eventually_source_integer_survivors_decomposition ha hc] with x hx hdecomp
  obtain ⟨b, r, hcount⟩ := hx
  have hcard := (Finset.card_le_card (hdecomp b r)).trans (Finset.card_union_le _ _)
  have hcardR : ((sourceIntegerSurvivors a c x b r).card : ℝ) ≤
      (Nat.smoothNumbersUpTo ⌊sourceIntervalLength c x⌋₊ (⌊sourceSmallPrimeUpper a x⌋₊ + 1)).card +
        (naturalResidueSurvivors (commonPinnedPrimeSet (x / 2) x)
          (sourceSurvivorVertices a c x b) r).card := by exact_mod_cast hcard
  refine ⟨zeroExtendedResidue (sourceSmallPrimes a x) (commonPinnedPrimeSet (x / 2) x) b r, ?_⟩
  exact hcardR.trans (add_le_add le_rfl hcount)

end

end Erdos4b.FGKMT
