/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ErrorClasses
import ErdosProblems.Erdos387.Section6Counting

/-!
# Finite error sets for the BNPZ divisor argument

This module turns the component-level exhaustion into a literal cover of the
bad finite set and proves the resulting cardinality inequality.  The later
analytic modules therefore only need to bound the four named finite sets.
-/

namespace Erdos387

namespace CoverBPZ

/-- A bad tuple with a component above `large`. -/
def IsLargeError {B K : ℕ} (S : BPZSection6Input B K)
    (n large : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        n < B * d ∧ d ≤ n ∧ E.value = d ∧ E.HasLargeComponent large

/-- A bad tuple with a component in `(medium, large]`. -/
def IsMediumError {B K : ℕ} (S : BPZSection6Input B K)
    (n medium large : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        n < B * d ∧ d ≤ n ∧ E.value = d ∧
          E.HasMediumComponent medium large

/-- A bad tuple having a convenient component factorization above `y`. -/
def IsConvenientError {B K : ℕ} (S : BPZSection6Input B K)
    (n y medium : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        n < B * d ∧ d ≤ n ∧ E.value = d ∧ E.HasConvenientComponent y
          ∧ ∀ i : Fin S.k, E.factor i ≤ medium

/-- The remaining error class: all components are at most `medium`, and
each is a `y³`-small factor times at most one large prime. -/
def IsAlmostPrimeError {B K : ℕ} (S : BPZSection6Input B K)
    (n y medium : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        n < B * d ∧ d ≤ n ∧ E.value = d ∧
          (∀ i : Fin S.k, E.factor i ≤ medium) ∧ E.IsAlmostPrimeTuple y

noncomputable def LargeErrors {B K : ℕ} (S : BPZSection6Input B K)
    (X z large : ℕ) : Finset ℕ := by
  classical
  exact (SiftedCandidates S X z).filter fun n => IsLargeError S n large

noncomputable def MediumErrors {B K : ℕ} (S : BPZSection6Input B K)
    (X z medium large : ℕ) : Finset ℕ := by
  classical
  exact (SiftedCandidates S X z).filter fun n => IsMediumError S n medium large

noncomputable def ConvenientErrors {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium : ℕ) : Finset ℕ := by
  classical
  exact (SiftedCandidates S X z).filter fun n =>
    IsConvenientError S n y medium

noncomputable def AlmostPrimeErrors {B K : ℕ} (S : BPZSection6Input B K)
    (X z y medium : ℕ) : Finset ℕ := by
  classical
  exact (SiftedCandidates S X z).filter fun n => IsAlmostPrimeError S n y medium

/-- The bad set is covered by the four successive component classes. -/
theorem badCandidates_subset_errorClasses
    {B K X z y medium large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hy : 2 ≤ y) :
    BadCandidates S X z ⊆
      (((LargeErrors S X z large ∪ MediumErrors S X z medium large) ∪
        ConvenientErrors S X z y medium) ∪
          AlmostPrimeErrors S X z y medium) := by
  classical
  intro n hnBad
  rw [BadCandidates, Finset.mem_filter] at hnBad
  obtain ⟨hnS, hnear⟩ := hnBad
  have hnData := hnS
  rw [SiftedCandidates, Finset.mem_filter] at hnData
  obtain ⟨hnWindow, hn, hprog, hrough⟩ := hnData
  obtain ⟨d, E, hnd, hdn, hvalue, _hcomponentDvd,
      _hcomponentPairwise, _htwo⟩ :=
    nearDivisor_has_residualTuple S hB hn hprog hnear
  have hpos : ∀ i : Fin S.k, 0 < E.factor i := by
    intro i
    have hfactorDvd : E.factor i ∣ n.choose S.k :=
      (E.divides i).trans
        (coverQuotient_dvd_choose (S.toCoverFactorization hn hprog) i.isLt)
    exact Nat.pos_of_dvd_of_pos hfactorDvd (Nat.choose_pos hn.le)
  rcases E.errorClass_exhaustion (y := y) (medium := medium) (large := large)
      hy hpos with hlarge | hmedium | hconv | halmost
  · apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    left
    rw [LargeErrors, Finset.mem_filter]
    exact ⟨hnS, hn, hprog, d, E, hnd, hdn, hvalue, hlarge⟩
  · apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    right
    rw [MediumErrors, Finset.mem_filter]
    exact ⟨hnS, hn, hprog, d, E, hnd, hdn, hvalue, hmedium⟩
  · apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    right
    rw [ConvenientErrors, Finset.mem_filter]
    exact ⟨hnS, hn, hprog, d, E, hnd, hdn, hvalue, hconv.2,
      hconv.1⟩
  · apply Finset.mem_union.mpr
    right
    rw [AlmostPrimeErrors, Finset.mem_filter]
    exact ⟨hnS, hn, hprog, d, E, hnd, hdn, hvalue, halmost.1, halmost.2⟩

/-- Cardinality form of the error-class cover. -/
theorem badCandidates_card_le_error_sum
    {B K X z y medium large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hy : 2 ≤ y) :
    (BadCandidates S X z).card ≤
      (LargeErrors S X z large).card +
      (MediumErrors S X z medium large).card +
      (ConvenientErrors S X z y medium).card +
      (AlmostPrimeErrors S X z y medium).card := by
  let EL := LargeErrors S X z large
  let EM := MediumErrors S X z medium large
  let EC := ConvenientErrors S X z y medium
  let EA := AlmostPrimeErrors S X z y medium
  calc
    (BadCandidates S X z).card ≤ (EL ∪ EM ∪ EC ∪ EA).card :=
      Finset.card_le_card (badCandidates_subset_errorClasses S hB hy)
    _ ≤ (EL ∪ EM ∪ EC).card + EA.card := Finset.card_union_le _ _
    _ ≤ ((EL ∪ EM).card + EC.card) + EA.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ ((EL.card + EM.card) + EC.card) + EA.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ = EL.card + EM.card + EC.card + EA.card := by omega

/-- The exact analytic handoff: any four error bounds whose sum is smaller
than the sifted set produce the required fixed-`B` counterexample. -/
theorem exists_counterexample_of_error_sum_lt
    {B K X z y medium large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hy : 2 ≤ y)
    (herrors :
        (LargeErrors S X z large).card +
        (MediumErrors S X z medium large).card +
        (ConvenientErrors S X z y medium).card +
        (AlmostPrimeErrors S X z y medium).card <
          (SiftedCandidates S X z).card) :
    ∃ n : ℕ,
      n ∈ Finset.Ioc (X / 2) X ∧ S.k < n ∧
      (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α ∧
      IsZRough z (n.choose S.k) ∧
      ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n →
        ¬d ∣ n.choose S.k := by
  apply exists_counterexample_of_bad_card_lt S hB
  exact lt_of_le_of_lt (badCandidates_card_le_error_sum S hB hy) herrors

end CoverBPZ

end Erdos387
