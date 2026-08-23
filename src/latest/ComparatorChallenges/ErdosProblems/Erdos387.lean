import ErdosProblems.Erdos387.AlmostPrimeExhaustion
import ErdosProblems.Erdos387.Endpoint
import ErdosProblems.Erdos387.QualitativeRoughCounting

open scoped BigOperators

namespace Erdos387

def UniversalNearDivisor (c : ℝ) : Prop :=
  0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
    ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k

def IsCounterexample (c : ℝ) (n k : ℕ) : Prop :=
  1 ≤ k ∧ k < n ∧
    ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n → ¬d ∣ n.choose k

def IsFixedBCounterexample (B n k : ℕ) : Prop :=
  1 ≤ k ∧ k < n ∧
    ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n → ¬d ∣ n.choose k

theorem erdos_387_of_counterexamples
    (h : ∀ c : ℝ, 0 < c → ∃ n k : ℕ, IsCounterexample c n k) :
    ¬ ∃ c : ℝ, UniversalNearDivisor c := by
  sorry

theorem erdos_387_of_fixedB
    (h : ∀ B : ℕ, 2 ≤ B → ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_eventually_fixedB
    (h : ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ n k : ℕ, IsFixedBCounterexample B n k) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_eventually_BNPZ
    (h : ∀ᶠ k : ℕ in Filter.atTop,
      ∃ n : ℕ, 1 ≤ k ∧ k < n ∧
        ∀ d : ℕ,
          (d : ℝ) ∈ Set.Ioc (BNPZEndpoint k * n) n → ¬d ∣ n.choose k) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_cover_certificates
    (h : ∀ B : ℕ, 2 ≤ B →
      ∃ n k : ℕ, ∃ D : CoverFactorization n k,
        1 ≤ k ∧ k < n ∧
        ∀ e : ℕ → ℕ,
          (∀ i < k, e i ∣ (n - i) / D.g i) →
          ¬((∏ i ∈ Finset.range k, e i : ℕ) : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_absorber_error_bounds
    (h : ∀ m : ℕ, 3 ≤ m →
      ∃ k : ℕ, ∃ C : CoverBPZ.AbsorberCoverValid m k,
        ∃ T z y medium large : ℕ,
          3 ≤ k ∧ 2 ≤ y ∧
          (AbsorberLargeErrors C T z large).card +
              (AbsorberMediumErrors C T z medium large).card +
              (AbsorberConvenientErrors C T z y medium).card +
              (AbsorberAlmostPrimeErrors C T z y medium).card <
            (SiftedAbsorberParameterCandidates C T z).card) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_frozen_roughProduct_bounds
    (h : ∀ m : ℕ, 3 ≤ m →
      ∃ k : ℕ, ∃ C : CoverBPZ.AbsorberCoverValid m k,
        ∃ t₀ T z : ℕ,
          3 ≤ k ∧
          (FrozenRoughProductErrors C t₀ T z).card <
            (SiftedAbsorberParameterCandidates (C.frozen t₀) T z).card) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_refined_error_bounds
    (h : ∀ B K : ℕ, 3 ≤ B →
      ∀ S : CoverBPZ.BPZSection6Input B K,
        ∃ X z y medium large : ℕ,
          2 ≤ y ∧
          (CoverBPZ.RefinedLargeErrors S X z large).card +
              (CoverBPZ.RefinedMediumErrors S X z medium large).card +
              (CoverBPZ.RefinedConvenientErrors S X z y medium).card +
              (CoverBPZ.RefinedAlmostPrimeErrors S X z y medium).card <
            (RefinedSiftedCandidates S X z).card) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

theorem erdos_387_of_refined_five_error_bounds
    (h : ∀ B K : ℕ, 3 ≤ B →
      ∀ S : CoverBPZ.BPZSection6Input B K,
        ∃ X z y medium large secondMin gap : ℕ,
          2 ≤ y ∧ 1 ≤ secondMin ∧
          B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2 ∧
          B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2 ∧
          (CoverBPZ.RefinedLargeErrors S X z large).card +
              (CoverBPZ.RefinedMediumErrors S X z medium large).card +
              (CoverBPZ.RefinedConvenientErrors S X z y medium).card +
              (CoverBPZ.RefinedComparablePrimeErrors S X z secondMin gap
                medium).card +
              (CoverBPZ.RefinedSeparatedAlmostPrimeErrors S X z y medium
                secondMin gap).card <
            (RefinedSiftedCandidates S X z).card) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n k : ℕ, 1 ≤ k → k < n →
      ∃ d : ℕ, (d : ℝ) ∈ Set.Ioc (c * n) n ∧ d ∣ n.choose k := by
  sorry

end Erdos387
