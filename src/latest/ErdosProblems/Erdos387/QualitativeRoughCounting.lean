/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.QualitativeDivisorStructure

/-!
# A single rough-product error set

After freezing the small-prime valuations, the four BNPZ divisor-error
classes may be viewed as an analytic partition of one simpler set: parameters
for which divisors of the varying rough residual parts have a product large
enough to create a near-top divisor.  This file defines that set and proves
the exact finite cardinality handoff.
-/

namespace Erdos387

open scoped BigOperators

/-- A frozen parameter admits fixed-part choices and rough-part choices whose
products satisfy the necessary inequalities for a near-top divisor. -/
def IsFrozenRoughProductError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ t z : ℕ) : Prop :=
  ∃ a b : Fin k → ℕ,
    a ∈ frozenFixedPartChoices C t₀ ∧
    (∀ i : Fin k,
      b i ∣ CoverBPZ.AbsorberCoverValid.largePrimePart k
        ((C.frozen t₀).residual t (Fin.rev i))) ∧
    (∀ i : Fin k, IsZRough z (b i)) ∧
    (C.frozen t₀).nNat t <
      m * ((∏ i, a i) * ∏ i, b i) ∧
    (∏ i, a i) * ∏ i, b i ≤ (C.frozen t₀).nNat t

/-- The literal subset of sifted parameters carrying a rough-product error. -/
noncomputable def FrozenRoughProductErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t₀ T z : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates (C.frozen t₀) T z).filter fun t =>
    IsFrozenRoughProductError C t₀ t z

/-- Every bad near-divisor parameter is a rough-product error after the
small-prime valuations have been frozen. -/
theorem badSiftedFrozen_subset_roughProductErrors
    {m k t₀ T z : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hm : 0 < m) (hk : 0 < k) :
    BadSiftedAbsorberParameterCandidates (C.frozen t₀) T z ⊆
      FrozenRoughProductErrors C t₀ T z := by
  classical
  intro t htBad
  rw [BadSiftedAbsorberParameterCandidates, Finset.mem_filter] at htBad
  obtain ⟨htS, hnear⟩ := htBad
  obtain ⟨d, E, hnd, hdn, hvalue, _hcomponents,
      _hpairwise, _htwo⟩ :=
    absorberNearDivisor_has_residualTuple (C.frozen t₀) hm hk hnear
  have hlower : (C.frozen t₀).nNat t < m * E.value := by
    simpa [hvalue] using hnd
  have hupper : E.value ≤ (C.frozen t₀).nNat t := by
    simpa [hvalue] using hdn
  obtain ⟨a, b, ha, hb, hrough, hvalueSplit, _hAdvd,
      _hroughLower, hroughUpper⟩ :=
    exists_roughProduct_of_near_frozen_residualDivisor
      C htS E hlower hupper
  have hexactLower :
      (C.frozen t₀).nNat t < m * ((∏ i, a i) * ∏ i, b i) := by
    simpa [← hvalueSplit] using hlower
  rw [FrozenRoughProductErrors, Finset.mem_filter]
  refine ⟨htS, a, b, ?_, hb, hrough, hexactLower, hroughUpper⟩
  exact (mem_frozenFixedPartChoices_iff C t₀ a).2 ha

theorem badSiftedFrozen_card_le_roughProductErrors
    {m k t₀ T z : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hm : 0 < m) (hk : 0 < k) :
    (BadSiftedAbsorberParameterCandidates (C.frozen t₀) T z).card ≤
      (FrozenRoughProductErrors C t₀ T z).card :=
  Finset.card_le_card (badSiftedFrozen_subset_roughProductErrors C hm hk)

/-- The sole remaining analytic comparison in the frozen formulation. -/
theorem exists_frozenAbsorberCounterexample_of_roughProduct_card_lt
    {m k t₀ T z : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hm : 0 < m) (hk : 0 < k)
    (hcard : (FrozenRoughProductErrors C t₀ T z).card <
      (SiftedAbsorberParameterCandidates (C.frozen t₀) T z).card) :
    ∃ t : ℕ,
      t ∈ Finset.Ioc (T / 2) T ∧
      Nat.Coprime (sievePrimeProduct k z)
        (((C.frozen t₀).nNat t).choose k) ∧
      ∀ d : ℕ,
        (d : ℝ) ∈ Set.Ioc (((C.frozen t₀).nNat t : ℝ) / m)
          ((C.frozen t₀).nNat t) →
        ¬d ∣ ((C.frozen t₀).nNat t).choose k := by
  apply exists_absorberCounterexample_of_bad_card_lt (C.frozen t₀) hm
  exact lt_of_le_of_lt
    (badSiftedFrozen_card_le_roughProductErrors C hm hk) hcard

end Erdos387
