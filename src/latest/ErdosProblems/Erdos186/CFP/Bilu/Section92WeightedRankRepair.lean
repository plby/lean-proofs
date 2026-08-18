/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section92PresentationQuotientAssembly

/-!
# Rank-weighted termination of the primitive quotient repair

Orthogonal quotienting can increase ordinary body volume by a fixed
dimension-dependent factor.  The source's minimal-rank argument absorbs
this by weighting a rank-`r` body by `repairFactor ^ r`.  A quotient drops
the rank by one, so any one-step volume cost bounded by `repairFactor`
makes the weighted volume nonincreasing.

This file formalizes that bookkeeping independently of the analytic
estimate which supplies the factor.
-/

namespace Erdos186.CFP.Bilu.Section92WeightedRankRepair

open Section92PresentationDescent
open Section92PresentationQuotientAssembly
open Section92BodyPresentationQuotient
open Section92OuterInjectivityBridge
open Section92ShortKernel
open Section94RankThresholdBoundary
open Section94SortedContainerAssembly

noncomputable section

set_option autoImplicit false

variable {A : Finset ℤ}

/-- A finite rank-uniform repair factor.  The summand at rank `n` is the
coarse one-step factor furnished by the projected-volume theorem. -/
def canonicalRankRepairFactor (s rankBound : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (rankBound + 1),
    (n : ℝ) * (2 * outerDilationBound n (2 * s))

theorem one_le_canonicalRankRepairFactor (s rankBound : ℕ) :
    1 ≤ canonicalRankRepairFactor s rankBound := by
  unfold canonicalRankRepairFactor
  have hsum : 0 ≤ ∑ n ∈ Finset.range (rankBound + 1),
      (n : ℝ) * (2 * outerDilationBound n (2 * s)) := by
    apply Finset.sum_nonneg
    intro n _hn
    exact mul_nonneg (Nat.cast_nonneg n)
      (mul_nonneg (by norm_num) (outerDilationBound_nonneg n (2 * s)))
  linarith

/-- Every rank below the ceiling has its local quotient cost bounded by
the single canonical repair factor. -/
theorem localQuotientFactor_le_canonicalRankRepairFactor
    {n s rankBound : ℕ} (hn : n ≤ rankBound) :
    (n : ℝ) * (2 * outerDilationBound n (2 * s)) ≤
      canonicalRankRepairFactor s rankBound := by
  have hterm : (n : ℝ) * (2 * outerDilationBound n (2 * s)) ≤
      ∑ i ∈ Finset.range (rankBound + 1),
        (i : ℝ) * (2 * outerDilationBound i (2 * s)) := by
    exact Finset.single_le_sum
      (s := Finset.range (rankBound + 1))
      (f := fun i : ℕ ↦
        (i : ℝ) * (2 * outerDilationBound i (2 * s)))
      (fun i _hi ↦ mul_nonneg (Nat.cast_nonneg i)
        (mul_nonneg (by norm_num)
          (outerDilationBound_nonneg i (2 * s))))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  unfold canonicalRankRepairFactor
  linarith

/-- The rank-weighted volume used to make quotient repair monotone. -/
def rankWeightedBodyVolume (repairFactor : ℝ)
    (X : RankedBodyPresentation A) : ℝ :=
  repairFactor ^ X.1 * bodyVolume X

theorem rankWeightedBodyVolume_pos
    {repairFactor : ℝ} (hrepair : 0 < repairFactor)
    (X : RankedBodyPresentation A) :
    0 < rankWeightedBodyVolume repairFactor X :=
  mul_pos (pow_pos hrepair _) (bodyVolume_pos X)

/-- Minimal-rank termination while retaining an arbitrary nonincreasing
rank-weighted volume bound. -/
theorem exists_enlargedInjective_with_rankWeightedVolume_le
    (s rankBound : ℕ) (repairFactor : ℝ)
    (initial : RankedBodyPresentation A)
    (hinitialRank : initial.1 ≤ rankBound)
    (reduce : ∀ X : RankedBodyPresentation A,
      ¬ EnlargedInjective s X →
        ∃ Y : RankedBodyPresentation A,
          Y.1 < X.1 ∧
          rankWeightedBodyVolume repairFactor Y ≤
            rankWeightedBodyVolume repairFactor X) :
    ∃ X : RankedBodyPresentation A,
      EnlargedInjective s X ∧ X.1 ≤ rankBound ∧
        rankWeightedBodyVolume repairFactor X ≤
          rankWeightedBodyVolume repairFactor initial := by
  obtain ⟨X, hweighted, hgood, hrank⟩ :=
    exists_good_of_rank_reduction_with_rank_bound
      (fun X : RankedBodyPresentation A ↦
        rankWeightedBodyVolume repairFactor X ≤
          rankWeightedBodyVolume repairFactor initial)
      (EnlargedInjective s) initial le_rfl rankBound hinitialRank
      (by
        intro X hX hbad
        obtain ⟨Y, hYX, hweight⟩ := reduce X hbad
        exact ⟨Y, hweight.trans hX, hYX⟩)
  exact ⟨X, hgood, hrank, hweighted⟩

/-- A one-step ordinary volume cost bounded by `repairFactor` is exactly
absorbed by the one-rank drop in the weighted volume. -/
theorem rankWeightedBodyVolume_quotient_le
    {n : ℕ} {T repairFactor : ℝ}
    (hrepair : 1 ≤ repairFactor)
    (X : BodyPresentation A n)
    (S : PrimitiveKernelStep X.seminorm X.map T)
    (hcard : 1 < A.card)
    (hvolume : bodyVolume (quotientRankedBodyPresentation X S hcard) ≤
      repairFactor * bodyVolume ⟨n, X⟩) :
    rankWeightedBodyVolume repairFactor
        (quotientRankedBodyPresentation X S hcard) ≤
      rankWeightedBodyVolume repairFactor ⟨n, X⟩ := by
  let k := S.quotient.complementRank
  have hnonneg : 0 ≤ repairFactor ^ k :=
    pow_nonneg (zero_le_one.trans hrepair) _
  calc
    rankWeightedBodyVolume repairFactor
        (quotientRankedBodyPresentation X S hcard) =
        repairFactor ^ k *
          bodyVolume (quotientRankedBodyPresentation X S hcard) := rfl
    _ ≤ repairFactor ^ k *
          (repairFactor * bodyVolume ⟨n, X⟩) :=
      mul_le_mul_of_nonneg_left hvolume hnonneg
    _ = repairFactor ^ (k + 1) * bodyVolume ⟨n, X⟩ := by
      rw [pow_succ]
      ring
    _ = repairFactor ^ n * bodyVolume ⟨n, X⟩ := by
      rw [S.quotient.rank_eq]
    _ = rankWeightedBodyVolume repairFactor ⟨n, X⟩ := rfl

/-- The fully canonical weighted rank repair, assuming only the uniform
ordinary-volume factor furnished by the projected-volume estimate. -/
theorem exists_enlargedInjective_of_canonicalWeightedQuotient
    (s rankBound : ℕ) {repairFactor : ℝ}
    (hrepair : 1 ≤ repairFactor)
    (hcard : 1 < A.card)
    (initial : RankedBodyPresentation A)
    (hinitialRank : initial.1 ≤ rankBound)
    (hquotientVolume : ∀ (X : RankedBodyPresentation A)
      (S : PrimitiveKernelStep X.2.seminorm X.2.map
        (outerDilationBound X.1 (2 * s))),
      bodyVolume
          (quotientRankedBodyPresentation X.2 S hcard) ≤
        repairFactor * bodyVolume X) :
    ∃ X : RankedBodyPresentation A,
      EnlargedInjective s X ∧ X.1 ≤ rankBound ∧
        rankWeightedBodyVolume repairFactor X ≤
          rankWeightedBodyVolume repairFactor initial := by
  apply exists_enlargedInjective_with_rankWeightedVolume_le
    s rankBound repairFactor initial hinitialRank
  intro X hbad
  obtain ⟨S⟩ :=
    exists_primitiveKernelStep_of_not_enlargedInjective X.2 hbad
  refine ⟨quotientRankedBodyPresentation X.2 S hcard,
    quotientBodyPresentation_rank_lt X.2 S, ?_⟩
  exact rankWeightedBodyVolume_quotient_le hrepair X.2 S hcard
    (hquotientVolume X S)

/-- Rank-uniform form: it suffices to establish the natural local factor
`n * (2 * outerDilationBound n (2*s))` at each quotient step. -/
theorem exists_enlargedInjective_of_localQuotientVolumeBound
    (s rankBound : ℕ) (hcard : 1 < A.card)
    (initial : RankedBodyPresentation A)
    (hinitialRank : initial.1 ≤ rankBound)
    (hlocalVolume : ∀ (X : RankedBodyPresentation A),
      X.1 ≤ rankBound →
      ∀ S : PrimitiveKernelStep X.2.seminorm X.2.map
        (outerDilationBound X.1 (2 * s)),
      bodyVolume
          (quotientRankedBodyPresentation X.2 S hcard) ≤
        ((X.1 : ℝ) *
          (2 * outerDilationBound X.1 (2 * s))) * bodyVolume X) :
    ∃ X : RankedBodyPresentation A,
      EnlargedInjective s X ∧ X.1 ≤ rankBound ∧
        rankWeightedBodyVolume
            (canonicalRankRepairFactor s rankBound) X ≤
          rankWeightedBodyVolume
            (canonicalRankRepairFactor s rankBound) initial := by
  let q := canonicalRankRepairFactor s rankBound
  obtain ⟨X, hX, hgood, _hrank⟩ :=
    exists_good_of_rank_reduction_with_rank_bound
      (fun X : RankedBodyPresentation A ↦
        X.1 ≤ rankBound ∧
          rankWeightedBodyVolume q X ≤
            rankWeightedBodyVolume q initial)
      (EnlargedInjective s) initial ⟨hinitialRank, le_rfl⟩
      rankBound hinitialRank
      (by
        intro X hX hbad
        obtain ⟨S⟩ :=
          exists_primitiveKernelStep_of_not_enlargedInjective X.2 hbad
        let Y := quotientRankedBodyPresentation X.2 S hcard
        have hYX : Y.1 < X.1 :=
          quotientBodyPresentation_rank_lt X.2 S
        have hlocal := hlocalVolume X hX.1 S
        have hfactor :
            ((X.1 : ℝ) *
                (2 * outerDilationBound X.1 (2 * s))) * bodyVolume X ≤
              q * bodyVolume X :=
          mul_le_mul_of_nonneg_right
            (localQuotientFactor_le_canonicalRankRepairFactor
              (s := s) (rankBound := rankBound) hX.1)
            (bodyVolume_pos X).le
        have hweighted : rankWeightedBodyVolume q Y ≤
            rankWeightedBodyVolume q X :=
          rankWeightedBodyVolume_quotient_le
            (one_le_canonicalRankRepairFactor s rankBound)
            X.2 S hcard (hlocal.trans hfactor)
        exact ⟨Y,
          ⟨(Nat.le_of_lt hYX).trans hX.1, hweighted.trans hX.2⟩,
          hYX⟩)
  exact ⟨X, hgood, hX.1, hX.2⟩

/-- Ordinary body volume is bounded by the rank-weighted volume whenever
the repair factor is at least one. -/
theorem bodyVolume_le_rankWeightedBodyVolume
    {repairFactor : ℝ} (hrepair : 1 ≤ repairFactor)
    (X : RankedBodyPresentation A) :
    bodyVolume X ≤ rankWeightedBodyVolume repairFactor X := by
  change bodyVolume X ≤ repairFactor ^ X.1 * bodyVolume X
  have hpow : 1 ≤ repairFactor ^ X.1 := one_le_pow₀ hrepair
  nlinarith [hpow, (bodyVolume_pos X).le]

end

end Erdos186.CFP.Bilu.Section92WeightedRankRepair

#print axioms
  Erdos186.CFP.Bilu.Section92WeightedRankRepair.exists_enlargedInjective_of_canonicalWeightedQuotient
