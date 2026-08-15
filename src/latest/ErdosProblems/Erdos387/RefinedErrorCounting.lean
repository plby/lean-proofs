/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ErrorCounting
import ErdosProblems.Erdos387.RefinedSieve

/-!
# Error-class counting on the refined BNPZ progression

This is the exact finite `S - E` interface used after imposing
`n ≡ k (mod p)` for every prime `k < p < 2k`.
-/

namespace Erdos387

/-- Divisibility by the canonical refined modulus implies membership in the
original public cover progression. -/
theorem refinement_progression_implies_public
    {B K n : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hprog : (CoverBPZ.refinementModulus S : ℤ) ∣
      (n : ℤ) - CoverBPZ.refinementResidue S) :
    (CoverBPZ.Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α := by
  apply (progression_dvd_iff_modEq S).mpr
  have hmod :=
    (CoverBPZ.refinement_progression_dvd_iff_modEq S).mp hprog
  exact (hmod.of_mul_right (CoverBPZ.refinementPrimeProduct S.k)).trans
    (CoverBPZ.refinementResidue_mod_Nk S)

/-- The bad subset of the refined sifted progression. -/
noncomputable def RefinedBadCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X z : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    HasFixedBNearDivisor B n S.k

theorem exists_counterexample_of_refined_bad_card_lt
    {B K X z : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hB : 0 < B)
    (hcard : (RefinedBadCandidates S X z).card <
      (RefinedSiftedCandidates S X z).card) :
    ∃ n : ℕ,
      n ∈ Finset.Ioc (X / 2) X ∧ S.k < n ∧
      (CoverBPZ.refinementModulus S : ℤ) ∣
        (n : ℤ) - CoverBPZ.refinementResidue S ∧
      IsZRough z (n.choose S.k) ∧
      ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n →
        ¬d ∣ n.choose S.k := by
  classical
  have hnsubset : ¬RefinedSiftedCandidates S X z ⊆
      RefinedBadCandidates S X z := by
    intro hsub
    exact (Nat.not_lt_of_ge (Finset.card_le_card hsub)) hcard
  obtain ⟨n, hnS, hnBad⟩ := Finset.not_subset.mp hnsubset
  have hnData := hnS
  rw [RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  refine ⟨n, hnData.1.1, hnData.1.2.1, hnData.1.2.2,
    hnData.2, ?_⟩
  intro d hdI hdvd
  apply hnBad
  rw [RefinedBadCandidates, Finset.mem_filter]
  refine ⟨hnS, d, ?_, ?_, hdvd⟩
  · exact (mem_Ioc_natCast_div_iff hB).mp hdI |>.1
  · exact (mem_Ioc_natCast_div_iff hB).mp hdI |>.2

namespace CoverBPZ

noncomputable def RefinedLargeErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z large : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    IsLargeError S n large

noncomputable def RefinedMediumErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z medium large : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    IsMediumError S n medium large

noncomputable def RefinedConvenientErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    IsConvenientError S n y medium

noncomputable def RefinedAlmostPrimeErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    IsAlmostPrimeError S n y medium

/-- The same tuple-level exhaustion, now restricted to the exact refined
candidate set. -/
theorem refinedBadCandidates_subset_errorClasses
    {B K X z y medium large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hy : 2 ≤ y) :
    RefinedBadCandidates S X z ⊆
      (((RefinedLargeErrors S X z large ∪
        RefinedMediumErrors S X z medium large) ∪
        RefinedConvenientErrors S X z y medium) ∪
          RefinedAlmostPrimeErrors S X z y medium) := by
  classical
  intro n hnBad
  rw [RefinedBadCandidates, Finset.mem_filter] at hnBad
  obtain ⟨hnS, hnear⟩ := hnBad
  have hnData := hnS
  rw [RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  obtain ⟨⟨hnWindow, hn, hnRefined⟩, hrough⟩ := hnData
  have hprog := refinement_progression_implies_public S hnRefined
  obtain ⟨d, E, hnd, hdn, hvalue, _hcomponentDvd,
      _hcomponentPairwise, _htwo⟩ :=
    nearDivisor_has_residualTuple S hB hn hprog hnear
  have hpos : ∀ i : Fin S.k, 0 < E.factor i := by
    intro i
    have hfactorDvd : E.factor i ∣ n.choose S.k :=
      (E.divides i).trans
        (coverQuotient_dvd_choose (S.toCoverFactorization hn hprog) i.isLt)
    exact Nat.pos_of_dvd_of_pos hfactorDvd (Nat.choose_pos hn.le)
  rcases E.errorClass_exhaustion (y := y) (medium := medium)
      (large := large) hy hpos with hlarge | hmedium | hconv | halmost
  · apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    left
    rw [RefinedLargeErrors, Finset.mem_filter]
    exact ⟨hnS, hn, hprog, d, E, hnd, hdn, hvalue, hlarge⟩
  · apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    right
    rw [RefinedMediumErrors, Finset.mem_filter]
    exact ⟨hnS, hn, hprog, d, E, hnd, hdn, hvalue, hmedium⟩
  · apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    right
    rw [RefinedConvenientErrors, Finset.mem_filter]
    exact ⟨hnS, hn, hprog, d, E, hnd, hdn, hvalue, hconv.2,
      hconv.1⟩
  · apply Finset.mem_union.mpr
    right
    rw [RefinedAlmostPrimeErrors, Finset.mem_filter]
    exact ⟨hnS, hn, hprog, d, E, hnd, hdn, hvalue,
      halmost.1, halmost.2⟩

theorem refinedBadCandidates_card_le_error_sum
    {B K X z y medium large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hy : 2 ≤ y) :
    (RefinedBadCandidates S X z).card ≤
      (RefinedLargeErrors S X z large).card +
      (RefinedMediumErrors S X z medium large).card +
      (RefinedConvenientErrors S X z y medium).card +
      (RefinedAlmostPrimeErrors S X z y medium).card := by
  let EL := RefinedLargeErrors S X z large
  let EM := RefinedMediumErrors S X z medium large
  let EC := RefinedConvenientErrors S X z y medium
  let EA := RefinedAlmostPrimeErrors S X z y medium
  calc
    (RefinedBadCandidates S X z).card ≤ (EL ∪ EM ∪ EC ∪ EA).card :=
      Finset.card_le_card (refinedBadCandidates_subset_errorClasses S hB hy)
    _ ≤ (EL ∪ EM ∪ EC).card + EA.card := Finset.card_union_le _ _
    _ ≤ ((EL ∪ EM).card + EC.card) + EA.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ ((EL.card + EM.card) + EC.card) + EA.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ = EL.card + EM.card + EC.card + EA.card := by omega

/-- Exact final Section 6 handoff on the correct refined progression. -/
theorem exists_refined_counterexample_of_error_sum_lt
    {B K X z y medium large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hy : 2 ≤ y)
    (herrors :
        (RefinedLargeErrors S X z large).card +
        (RefinedMediumErrors S X z medium large).card +
        (RefinedConvenientErrors S X z y medium).card +
        (RefinedAlmostPrimeErrors S X z y medium).card <
          (RefinedSiftedCandidates S X z).card) :
    ∃ n : ℕ,
      n ∈ Finset.Ioc (X / 2) X ∧ S.k < n ∧
      (refinementModulus S : ℤ) ∣ (n : ℤ) - refinementResidue S ∧
      IsZRough z (n.choose S.k) ∧
      ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n →
        ¬d ∣ n.choose S.k := by
  apply exists_counterexample_of_refined_bad_card_lt S hB
  exact lt_of_le_of_lt
    (refinedBadCandidates_card_le_error_sum S hB hy) herrors

end CoverBPZ

end Erdos387
