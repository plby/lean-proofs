import ErdosProblems.Erdos248.BadMassAssembly
import ErdosProblems.Erdos248.MediumTail
import ErdosProblems.Erdos248.LargeTail

/-!
# Erdős Problem 248: final tail assembly

This file contains the parameter-free logical assembly of the two analytic
tail estimates.  The analytic moment arguments are deliberately kept behind
the exact interfaces `HasUniformMediumPrimeTail` and
`HasUniformLargePrimeTail`: each predicate asserts that one fixed natural
threshold works for every Wirsing constant, every corresponding regular
sieve dimension, and every shift in the required range.

Once the two estimates have a common threshold, the deterministic prime-range
decomposition in `BadMassAssembly.lean` gives the summable weighted bad-mass
bound.  `FinalReduction.lean` then extracts arbitrarily large simultaneous
witnesses and hence the exact infinite-set statement of Problem 248.
-/

noncomputable section

open scoped ArithmeticFunction.omega BigOperators

namespace Erdos248

local instance tailAssemblyDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Increasing the exceptional-event threshold can only decrease the
medium-prime bad mass. -/
theorem mediumPrimeBadMass_anti_threshold
    {K T U k : ℕ} (hTU : T ≤ U) :
    mediumPrimeBadMass K U k ≤ mediumPrimeBadMass K T k := by
  unfold mediumPrimeBadMass
  apply Finset.sum_le_sum
  intro n hn
  by_cases hU : U * k < mediumPrimeCount K k n
  · have hT : T * k < mediumPrimeCount K k n :=
      (Nat.mul_le_mul_right k hTU).trans_lt hU
    simp only [if_pos hU, if_pos hT]
    exact le_rfl
  · simp only [if_neg hU]
    split_ifs
    · exact sieveWeight_nonneg K n
    · exact le_rfl

/-- Increasing the exceptional-event threshold can only decrease the
large-prime bad mass. -/
theorem largePrimeBadMass_anti_threshold
    {K T U k : ℕ} (hTU : T ≤ U) :
    largePrimeBadMass K U k ≤ largePrimeBadMass K T k := by
  unfold largePrimeBadMass
  apply Finset.sum_le_sum
  intro n hn
  by_cases hU : U * k < largePrimeCount K k n
  · have hT : T * k < largePrimeCount K k n :=
      (Nat.mul_le_mul_right k hTU).trans_lt hU
    simp only [if_pos hU, if_pos hT]
    exact le_rfl
  · simp only [if_neg hU]
    split_ifs
    · exact sieveWeight_nonneg K n
    · exact le_rfl

/-- A fixed threshold controls every near-shift medium-prime exceptional
event, uniformly in the analytic normalization constant and sieve
dimension. -/
def HasUniformMediumPrimeTail (T : ℕ) : Prop :=
  ∀ {A : ℝ} {K : ℕ}, HasUniformWirsingBound A →
    NormalizationRegular A K →
    ∀ k, 1 ≤ k → k ≤ K →
      mediumPrimeBadMass K T k ≤
        sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))

/-- A fixed threshold controls every large-prime exceptional event, uniformly
in the analytic normalization constant, sieve dimension, and all relevant
shifts. -/
def HasUniformLargePrimeTail (T : ℕ) : Prop :=
  ∀ {A : ℝ} {K : ℕ}, HasUniformWirsingBound A →
    NormalizationRegular A K →
    ∀ k, 1 ≤ k → k ≤ intervalExponent K →
      largePrimeBadMass K T k ≤
        sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))

/-- The uniform medium-prime tail property is preserved when the threshold is
increased. -/
theorem HasUniformMediumPrimeTail.mono {T U : ℕ}
    (hTU : T ≤ U) (hT : HasUniformMediumPrimeTail T) :
    HasUniformMediumPrimeTail U := by
  intro A K hA hreg k hk1 hkK
  exact (mediumPrimeBadMass_anti_threshold hTU).trans
    (hT hA hreg k hk1 hkK)

/-- The uniform large-prime tail property is preserved when the threshold is
increased. -/
theorem HasUniformLargePrimeTail.mono {T U : ℕ}
    (hTU : T ≤ U) (hT : HasUniformLargePrimeTail T) :
    HasUniformLargePrimeTail U := by
  intro A K hA hreg k hk1 hkM
  exact (largePrimeBadMass_anti_threshold hTU).trans
    (hT hA hreg k hk1 hkM)

/-- Exact final assembly for a common fixed threshold.  There are no hidden
parameter assumptions: `T` is independent of `A`, `K`, and `k`, and the
constant in the conclusion is the explicit natural number `2 * T + 102`
viewed in `ℝ`. -/
theorem erdos248_of_uniform_primeRange_tails
    (T : ℕ) (hmedium : HasUniformMediumPrimeTail T)
    (hlarge : HasUniformLargePrimeTail T) :
    ∃ C > (0 : ℝ),
      {n : ℕ | ∀ k ≥ 1, ω (n + k) ≤ C * k}.Infinite := by
  apply erdos248_of_uniform_weightedBadMass (2 * T + 102) (by omega)
  intro A K hA hreg
  exact uniform_weightedBadMass_of_primeRange_tails hA hreg le_rfl
    (hmedium hA hreg) (hlarge hA hreg)

/-- Existential packaging of the final assembly, convenient when the medium
and large moment arguments first produce separate fixed thresholds. -/
theorem erdos248_of_exists_uniform_primeRange_tails
    (h : ∃ T : ℕ,
      HasUniformMediumPrimeTail T ∧ HasUniformLargePrimeTail T) :
    ∃ C > (0 : ℝ),
      {n : ℕ | ∀ k ≥ 1, ω (n + k) ≤ C * k}.Infinite := by
  obtain ⟨T, hmedium, hlarge⟩ := h
  exact erdos248_of_uniform_primeRange_tails T hmedium hlarge

/-- Final assembly when the two analytic moment arguments supply unrelated
fixed thresholds.  Their maximum is still an absolute threshold and controls
both tails by monotonicity. -/
theorem erdos248_of_separate_uniform_primeRange_tails
    (hmedium : ∃ T : ℕ, HasUniformMediumPrimeTail T)
    (hlarge : ∃ T : ℕ, HasUniformLargePrimeTail T) :
    ∃ C > (0 : ℝ),
      {n : ℕ | ∀ k ≥ 1, ω (n + k) ≤ C * k}.Infinite := by
  obtain ⟨Tm, hm⟩ := hmedium
  obtain ⟨Tl, hl⟩ := hlarge
  apply erdos248_of_uniform_primeRange_tails (max Tm Tl)
  · exact hm.mono (Nat.le_max_left Tm Tl)
  · exact hl.mono (Nat.le_max_right Tm Tl)

/-- Erdős Problem 248, assembled from the concrete uniform medium- and
large-prime tail estimates. -/
theorem erdos248_resolved :
    ∃ C > (0 : ℝ),
      {n : ℕ | ∀ k ≥ 1, ω (n + k) ≤ C * k}.Infinite := by
  apply erdos248_of_separate_uniform_primeRange_tails
  · obtain ⟨T, hT⟩ := exists_uniform_mediumPrimeBadMass_tail
    refine ⟨T, ?_⟩
    intro A K hA hreg k hk1 hkK
    exact hT hA hreg k hk1 hkK
  · obtain ⟨T, hT⟩ := exists_uniform_largePrimeBadMass_tail
    refine ⟨T, ?_⟩
    intro A K hA hreg k hk1 hkmax
    exact hT hA hreg k hk1 hkmax

end Erdos248
