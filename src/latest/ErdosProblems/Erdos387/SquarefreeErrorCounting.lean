/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AlmostPrimeExhaustion
import ErdosProblems.Erdos387.SquarefreeCandidates

/-!
# The five-error handoff inside the squarefree residual candidates

The analytic estimates may discard the negligible candidates having a
nonsquarefree residual quotient.  This file repeats the final finite
pigeonhole argument inside the surviving squarefree set, so subsequent
estimates never need prime-power Kloosterman bounds for their varying
moduli.
-/

namespace Erdos387

namespace CoverBPZ

noncomputable def RefinedSquarefreeBadCandidates {B K : ℕ}
    (S : BPZSection6Input B K) (X z : ℕ) : Finset ℕ :=
  RefinedBadCandidates S X z ∩ RefinedSquarefreeCandidates S X z

noncomputable def RefinedSquarefreeLargeErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z large : ℕ) : Finset ℕ :=
  RefinedLargeErrors S X z large ∩ RefinedSquarefreeCandidates S X z

noncomputable def RefinedSquarefreeMediumErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z medium large : ℕ) : Finset ℕ :=
  RefinedMediumErrors S X z medium large ∩
    RefinedSquarefreeCandidates S X z

noncomputable def RefinedSquarefreeConvenientErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z y medium : ℕ) : Finset ℕ :=
  RefinedConvenientErrors S X z y medium ∩
    RefinedSquarefreeCandidates S X z

noncomputable def RefinedSquarefreeComparablePrimeErrors {B K : ℕ}
    (S : BPZSection6Input B K)
    (X z secondMin gap medium : ℕ) : Finset ℕ :=
  RefinedComparablePrimeErrors S X z secondMin gap medium ∩
    RefinedSquarefreeCandidates S X z

noncomputable def RefinedSquarefreeSeparatedAlmostPrimeErrors {B K : ℕ}
    (S : BPZSection6Input B K)
    (X z y medium secondMin gap : ℕ) : Finset ℕ :=
  RefinedSeparatedAlmostPrimeErrors S X z y medium secondMin gap ∩
    RefinedSquarefreeCandidates S X z

theorem refinedSquarefreeBadCandidates_subset_five_errorClasses
    {B K X z y medium large secondMin gap : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) (hy : 2 ≤ y)
    (hsecond : 1 ≤ secondMin)
    (hscaleSecond :
      B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2)
    (hscaleGap :
      B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2) :
    RefinedSquarefreeBadCandidates S X z ⊆
      (((RefinedSquarefreeLargeErrors S X z large ∪
          RefinedSquarefreeMediumErrors S X z medium large) ∪
        RefinedSquarefreeConvenientErrors S X z y medium) ∪
        RefinedSquarefreeComparablePrimeErrors S X z secondMin gap medium) ∪
        RefinedSquarefreeSeparatedAlmostPrimeErrors S X z y medium
          secondMin gap := by
  classical
  intro n hn
  rw [RefinedSquarefreeBadCandidates, Finset.mem_inter] at hn
  obtain ⟨hnBad, hnSq⟩ := hn
  have hfour := refinedBadCandidates_subset_errorClasses
    (medium := medium) (large := large) S hB hy hnBad
  simp only [RefinedSquarefreeLargeErrors,
    RefinedSquarefreeMediumErrors, RefinedSquarefreeConvenientErrors,
    RefinedSquarefreeComparablePrimeErrors,
    RefinedSquarefreeSeparatedAlmostPrimeErrors, Finset.mem_inter,
    Finset.mem_union]
  rcases Finset.mem_union.mp hfour with hfirst | halmost
  · rcases Finset.mem_union.mp hfirst with hpair | hconv
    · rcases Finset.mem_union.mp hpair with hlarge | hmedium
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hlarge, hnSq⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hmedium, hnSq⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨hconv, hnSq⟩))
  · have hsplit :=
      refinedAlmostPrimeErrors_subset_comparable_union_separated S hsecond
        hscaleSecond hscaleGap halmost
    rcases Finset.mem_union.mp hsplit with hcomp | hsep
    · exact Or.inl (Or.inr ⟨hcomp, hnSq⟩)
    · exact Or.inr ⟨hsep, hnSq⟩

theorem refinedSquarefreeBadCandidates_card_le_five_error_sum
    {B K X z y medium large secondMin gap : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) (hy : 2 ≤ y)
    (hsecond : 1 ≤ secondMin)
    (hscaleSecond :
      B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2)
    (hscaleGap :
      B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2) :
    (RefinedSquarefreeBadCandidates S X z).card ≤
      (RefinedSquarefreeLargeErrors S X z large).card +
        (RefinedSquarefreeMediumErrors S X z medium large).card +
        (RefinedSquarefreeConvenientErrors S X z y medium).card +
        (RefinedSquarefreeComparablePrimeErrors S X z secondMin gap
          medium).card +
        (RefinedSquarefreeSeparatedAlmostPrimeErrors S X z y medium
          secondMin gap).card := by
  let E₁ := RefinedSquarefreeLargeErrors S X z large
  let E₂ := RefinedSquarefreeMediumErrors S X z medium large
  let E₃ := RefinedSquarefreeConvenientErrors S X z y medium
  let E₄ := RefinedSquarefreeComparablePrimeErrors S X z secondMin gap medium
  let E₅ := RefinedSquarefreeSeparatedAlmostPrimeErrors S X z y medium
    secondMin gap
  calc
    (RefinedSquarefreeBadCandidates S X z).card ≤
        ((((E₁ ∪ E₂) ∪ E₃) ∪ E₄) ∪ E₅).card :=
      Finset.card_le_card
        (refinedSquarefreeBadCandidates_subset_five_errorClasses S hB hy
          hsecond hscaleSecond hscaleGap)
    _ ≤ (((E₁ ∪ E₂) ∪ E₃) ∪ E₄).card + E₅.card :=
      Finset.card_union_le _ _
    _ ≤ ((E₁ ∪ E₂) ∪ E₃).card + E₄.card + E₅.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ (E₁ ∪ E₂).card + E₃.card + E₄.card + E₅.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ E₁.card + E₂.card + E₃.card + E₄.card + E₅.card := by
      gcongr
      exact Finset.card_union_le _ _

/-- Exact final Section 6 handoff after deleting nonsquarefree residual
candidates. -/
theorem exists_refined_counterexample_of_squarefree_five_error_sum_lt
    {B K X z y medium large secondMin gap : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) (hy : 2 ≤ y)
    (hsecond : 1 ≤ secondMin)
    (hscaleSecond :
      B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2)
    (hscaleGap :
      B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2)
    (herrors :
      (RefinedSquarefreeLargeErrors S X z large).card +
          (RefinedSquarefreeMediumErrors S X z medium large).card +
          (RefinedSquarefreeConvenientErrors S X z y medium).card +
          (RefinedSquarefreeComparablePrimeErrors S X z secondMin gap
            medium).card +
          (RefinedSquarefreeSeparatedAlmostPrimeErrors S X z y medium
            secondMin gap).card <
        (RefinedSquarefreeCandidates S X z).card) :
    ∃ n : ℕ,
      n ∈ Finset.Ioc (X / 2) X ∧ S.k < n ∧
      (refinementModulus S : ℤ) ∣ (n : ℤ) - refinementResidue S ∧
      IsZRough z (n.choose S.k) ∧
      ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n →
        ¬d ∣ n.choose S.k := by
  classical
  have hbadCard : (RefinedSquarefreeBadCandidates S X z).card <
      (RefinedSquarefreeCandidates S X z).card :=
    lt_of_le_of_lt
      (refinedSquarefreeBadCandidates_card_le_five_error_sum S hB hy
        hsecond hscaleSecond hscaleGap) herrors
  have hnsubset : ¬RefinedSquarefreeCandidates S X z ⊆
      RefinedSquarefreeBadCandidates S X z := by
    intro hsub
    exact (Nat.not_lt_of_ge (Finset.card_le_card hsub)) hbadCard
  obtain ⟨n, hnSq, hnBad⟩ := Finset.not_subset.mp hnsubset
  have hnS := hnSq
  rw [RefinedSquarefreeCandidates, Finset.mem_filter] at hnS
  have hnData := hnS.1
  rw [RefinedSiftedCandidates, Finset.mem_filter,
    mem_RefinedBaseCandidates] at hnData
  refine ⟨n, hnData.1.1, hnData.1.2.1, hnData.1.2.2, hnData.2, ?_⟩
  intro d hdI hdvd
  apply hnBad
  rw [RefinedSquarefreeBadCandidates, Finset.mem_inter,
    RefinedBadCandidates, Finset.mem_filter]
  refine ⟨⟨hnS.1, d, ?_, ?_, hdvd⟩, hnSq⟩
  · exact (mem_Ioc_natCast_div_iff hB).mp hdI |>.1
  · exact (mem_Ioc_natCast_div_iff hB).mp hdI |>.2

end CoverBPZ

end Erdos387
