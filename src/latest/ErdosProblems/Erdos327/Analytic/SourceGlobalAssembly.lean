import ErdosProblems.Erdos327.Analytic.DyadicCover
import ErdosProblems.Erdos327.Analytic.SourceBoxAllCutoffs
import ErdosProblems.Erdos327.Analytic.SieveSchedule

/-!
# Global finite assembly of the source-coordinate estimate

This file inserts the exact sieve schedule into every dyadic source block.
The main theorem is a completely finite sum.  Blocks on which all analytic
hypotheses hold use the scheduled cutoff and the explicit residual
envelope.  All other blocks remain rigorously bounded by the same finite
sieve with the cutoff clamped at two and the exact residual moment.
-/

namespace Erdos327.Analytic

open Finset

noncomputable section

/-- The cutoff schedule clamped at two.  This only changes the initial
indices for which `sieveCutoff j = 1`. -/
def sourceClampedSieveCutoff (j : ℕ) : ℕ :=
  max 2 (sieveCutoff j)

theorem two_le_sourceClampedSieveCutoff (j : ℕ) :
    2 ≤ sourceClampedSieveCutoff j := by
  simp [sourceClampedSieveCutoff]

/-- Once the scheduled cutoff is admissible, clamping does nothing. -/
theorem sourceClampedSieveCutoff_eq
    {j : ℕ} (hj : 2 ≤ sieveCutoff j) :
    sourceClampedSieveCutoff j = sieveCutoff j := by
  exact max_eq_right hj

/-- Indices on which the scheduled cutoff and the explicit residual
mean-value theorem are simultaneously available. -/
def sourceScheduledGoodIndex (L N j : ℕ) : Prop :=
  2 ≤ sieveCutoff j ∧
    L ≤ dyadicScale j ∧
    2 ≤ 2 * N / dyadicScale j ^ 2

instance sourceScheduledGoodIndexDecidable (L N j : ℕ) :
    Decidable (sourceScheduledGoodIndex L N j) :=
  Classical.propDecidable _

/-- The fully explicit scheduled block bound. -/
def sourceScheduledExplicitBlockBound
    (L N : ℕ) (A K : ℝ) (j : ℕ) : ℝ :=
  sourceDyadicBudget L (dyadicScale j) A K *
    sourceAllCutoffSharpSieveBound
      L (sieveCutoff j) (dyadicScale j) (sieveRadius j) *
    sourceDyadicResidualEnvelope
      L (dyadicScale j) (2 * N / dyadicScale j ^ 2)

/-- A fallback valid at every index.  It keeps the exact residual moment
and merely clamps the prime cutoff at two. -/
def sourceScheduledFallbackBlockBound
    (L N : ℕ) (A K : ℝ) (j : ℕ) : ℝ :=
  sourceDyadicBudget L (dyadicScale j) A K *
    sourceAllCutoffSharpSieveBound
      L (sourceClampedSieveCutoff j)
        (dyadicScale j) (sieveRadius j) *
    sourceDyadicResidualMoment
      L (dyadicScale j) (2 * N / dyadicScale j ^ 2)

/-- The global summand visibly separates fully explicit analytic blocks
from the finite exceptional blocks. -/
def sourceScheduledBlockBound
    (L N : ℕ) (A K : ℝ) (j : ℕ) : ℝ :=
  if sourceScheduledGoodIndex L N j then
    sourceScheduledExplicitBlockBound L N A K j
  else
    sourceScheduledFallbackBlockBound L N A K j

theorem dyadicScale_pos (j : ℕ) :
    0 < dyadicScale j := by
  unfold dyadicScale
  positivity

/-- The schedule-dominance hypothesis guarantees that the scheduled
prime cutoff is already admissible. -/
theorem two_le_sieveCutoff_of_dominance
    {j : ℕ} (hdom : 32 * sieveRadius j ≤ j) :
    2 ≤ sieveCutoff j := by
  have hk : 2 ≤ sieveCutoffExponent j :=
    two_le_sieveCutoffExponent hdom
  unfold sieveCutoff
  calc
    2 ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ sieveCutoffExponent j :=
      Nat.pow_le_pow_right (by norm_num) hk

/-- A dyadic scale below `sqrt N` has residual cutoff at least two. -/
theorem two_le_sourceResidualCutoff_of_sq_le
    {N X : ℕ} (hX : 0 < X) (hXN : X ^ 2 ≤ N) :
    2 ≤ 2 * N / X ^ 2 := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < X ^ 2)).2
  nlinarith

/-- Concrete sufficient conditions for a dyadic index to lie in the good
analytic part of the scheduled sum. -/
theorem sourceScheduledGoodIndex_of_bounds
    {L N j : ℕ}
    (hdom : 32 * sieveRadius j ≤ j)
    (hLX : L ≤ dyadicScale j)
    (hXN : dyadicScale j ^ 2 ≤ N) :
    sourceScheduledGoodIndex L N j := by
  exact ⟨two_le_sieveCutoff_of_dominance hdom, hLX,
    two_le_sourceResidualCutoff_of_sq_le (dyadicScale_pos j) hXN⟩

/-- Every good dyadic slice is bounded by the fully explicit scheduled
main term, factorial tail, polynomial boundary, and residual envelope. -/
theorem card_sourceDyadic_le_scheduledExplicit
    {L N j : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A)
    (hj : sourceScheduledGoodIndex L N j) :
    ((sourceDyadicCoordinateSet L N A K (dyadicScale j)).card : ℝ) ≤
      sourceScheduledExplicitBlockBound L N A K j := by
  rcases hj with ⟨hz, hLX, hY⟩
  exact card_sourceDyadicCoordinateSet_le_allCutoffs_explicit
    (L := L) (N := N) (z := sieveCutoff j)
    (X := dyadicScale j) (R := sieveRadius j)
    (A := A) (K := K) hL hLX hz hY hA

/-- Every dyadic slice, including the initial and terminal exceptional
ones, is bounded by the clamped-cutoff fallback. -/
theorem card_sourceDyadic_le_scheduledFallback
    {L N j : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A) :
    ((sourceDyadicCoordinateSet L N A K (dyadicScale j)).card : ℝ) ≤
      sourceScheduledFallbackBlockBound L N A K j := by
  exact card_sourceDyadicCoordinateSet_le_allCutoffs_mul_residual
    (L := L) (N := N) (z := sourceClampedSieveCutoff j)
    (X := dyadicScale j) (R := sieveRadius j)
    (A := A) (K := K)
    hL (dyadicScale_pos j)
    (two_le_sourceClampedSieveCutoff j) hA

/-- Uniform pointwise scheduled bound for every dyadic slice. -/
theorem card_sourceDyadic_le_scheduledBlock
    {L N j : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A) :
    ((sourceDyadicCoordinateSet L N A K (dyadicScale j)).card : ℝ) ≤
      sourceScheduledBlockBound L N A K j := by
  by_cases hj : sourceScheduledGoodIndex L N j
  · rw [sourceScheduledBlockBound, if_pos hj]
    exact card_sourceDyadic_le_scheduledExplicit hL hA hj
  · rw [sourceScheduledBlockBound, if_neg hj]
    exact card_sourceDyadic_le_scheduledFallback hL hA

/-- Exact finite global source-coordinate estimate with the natural-power
sieve schedule inserted at every dyadic scale. -/
theorem card_sourceCoordinateSet_le_scheduled_sum
    {L N : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A) :
    ((sourceCoordinateSet L N A K).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        sourceScheduledBlockBound L N A K j := by
  refine (card_sourceCoordinateSet_le_sum_dyadic L N A K).trans ?_
  apply sum_le_sum
  intro j hj
  simpa [dyadicScale] using
    (card_sourceDyadic_le_scheduledBlock
      (L := L) (N := N) (j := j) (A := A) (K := K) hL hA)

/-- The scheduled sum can be displayed as two disjoint finite sums:
good analytic indices and their finite complement. -/
theorem scheduled_sum_eq_good_add_exceptional
    (L N : ℕ) (A K : ℝ) :
    (∑ j ∈ range (Nat.log 2 N + 1),
        sourceScheduledBlockBound L N A K j) =
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (sourceScheduledGoodIndex L N),
        sourceScheduledExplicitBlockBound L N A K j) +
      ∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦ ¬sourceScheduledGoodIndex L N j),
        sourceScheduledFallbackBlockBound L N A K j := by
  rw [← sum_filter_add_sum_filter_not
    (range (Nat.log 2 N + 1))
    (sourceScheduledGoodIndex L N)]
  apply congrArg₂ (· + ·)
  · apply sum_congr rfl
    intro j hj
    have hgood :=
      (mem_filter.mp hj).2
    simp [sourceScheduledBlockBound, hgood]
  · apply sum_congr rfl
    intro j hj
    have hbad :=
      (mem_filter.mp hj).2
    simp [sourceScheduledBlockBound, hbad]

/-- Split form of the global finite estimate, making the precise remaining
exceptional range part of the theorem statement. -/
theorem card_sourceCoordinateSet_le_good_add_exceptional
    {L N : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A) :
    ((sourceCoordinateSet L N A K).card : ℝ) ≤
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (sourceScheduledGoodIndex L N),
        sourceScheduledExplicitBlockBound L N A K j) +
      ∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦ ¬sourceScheduledGoodIndex L N j),
        sourceScheduledFallbackBlockBound L N A K j := by
  rw [← scheduled_sum_eq_good_add_exceptional L N A K]
  exact card_sourceCoordinateSet_le_scheduled_sum hL hA

/-- The same scheduled sum directly bounds the score-oriented bad source
vertices appearing in the canonical reduction. -/
theorem card_rankBad_le_scheduled_sum
    {L N : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N) (hA : 0 ≤ A) :
    ((Erdos327.rankBad (Erdos327.upto N)
      (regularSource L A K N)
      ArithmeticFunction.cardFactors).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        sourceScheduledBlockBound L N A K j := by
  have hcoordinate :
      ((Erdos327.rankBad (Erdos327.upto N)
        (regularSource L A K N)
        ArithmeticFunction.cardFactors).card : ℝ) ≤
        ((sourceCoordinateSet L N A K).card : ℝ) := by
    exact_mod_cast card_rankBad_le_sourceCoordinateSet hL hN
  exact hcoordinate.trans
    (card_sourceCoordinateSet_le_scheduled_sum hL hA)

/-- Split scheduled bound for the canonical bad-source count.  Thus the
remaining analytic task is exactly to bound this displayed finite sum by
the desired density budget. -/
theorem card_rankBad_le_good_add_exceptional
    {L N : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N) (hA : 0 ≤ A) :
    ((Erdos327.rankBad (Erdos327.upto N)
      (regularSource L A K N)
      ArithmeticFunction.cardFactors).card : ℝ) ≤
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (sourceScheduledGoodIndex L N),
        sourceScheduledExplicitBlockBound L N A K j) +
      ∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦ ¬sourceScheduledGoodIndex L N j),
        sourceScheduledFallbackBlockBound L N A K j := by
  rw [← scheduled_sum_eq_good_add_exceptional L N A K]
  exact card_rankBad_le_scheduled_sum hL hN hA

end

end Erdos327.Analytic
