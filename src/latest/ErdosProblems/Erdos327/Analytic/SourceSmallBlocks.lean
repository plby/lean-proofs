import ErdosProblems.Erdos327.Analytic.SourceGlobalAssembly

/-!
# Initial source blocks

The source coordinate set retains both `v ≤ 3u` and `L ≤ u+v`.
Consequently the dyadic block `X ≤ u < 2X` is empty when `8X < L`.
The finitely many remaining blocks with `X < L ≤ 8X` are covered by
the all-cutoff sieve and exact residual moment without requiring
`L ≤ X`.
-/

namespace Erdos327.Analytic

open Finset

noncomputable section

/-- A source block too far below the roughness cutoff is empty. -/
theorem sourceDyadicCoordinateSet_eq_empty_of_eight_mul_lt
    {L N X : ℕ} {A K : ℝ} (hXL : 8 * X < L) :
    sourceDyadicCoordinateSet L N A K X = ∅ := by
  ext q
  constructor
  · intro hq
    rw [sourceDyadicCoordinateSet, mem_filter] at hq
    rcases hq with ⟨hqSource, _hXu, hu2X⟩
    rw [sourceCoordinateSet, mem_filter] at hqSource
    rcases hqSource.2 with
      ⟨_hcop, hv3u, _hscore, _hpair, _hexact, hLsum,
        _hbLower, _hbUpper, _hoddU, _hoddSum, _hoddD,
        _hrough, _hregular⟩
    omega
  · simp

/-- A nonempty dyadic source block must meet the roughness cutoff after
enlarging its scale by the exact factor eight. -/
theorem cutoff_le_eight_mul_of_sourceDyadic_nonempty
    {L N X : ℕ} {A K : ℝ}
    (hne : (sourceDyadicCoordinateSet L N A K X).Nonempty) :
    L ≤ 8 * X := by
  by_contra hnot
  have hXL : 8 * X < L := Nat.lt_of_not_ge hnot
  rw [sourceDyadicCoordinateSet_eq_empty_of_eight_mul_lt hXL] at hne
  exact not_nonempty_empty hne

/-- Every initial scheduled block is either identically empty or belongs
to the short transition range `X < L ≤ 8X` and has the analytic
all-cutoff/exact-residual bound. -/
theorem source_initialBlock_empty_or_analytic
    {L N j : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A)
    (_hXL : dyadicScale j < L) :
    sourceDyadicCoordinateSet L N A K (dyadicScale j) = ∅ ∨
      (L ≤ 8 * dyadicScale j ∧
        ((sourceDyadicCoordinateSet
          L N A K (dyadicScale j)).card : ℝ) ≤
          sourceScheduledFallbackBlockBound L N A K j) := by
  by_cases hfar : 8 * dyadicScale j < L
  · exact Or.inl
      (sourceDyadicCoordinateSet_eq_empty_of_eight_mul_lt hfar)
  · exact Or.inr
      ⟨Nat.le_of_not_gt hfar,
        card_sourceDyadic_le_scheduledFallback hL hA⟩

/-- An initial index cannot enter the fully explicit branch, whose
residual envelope requires `L ≤ X`. -/
theorem not_sourceScheduledGoodIndex_of_scale_lt
    {L N j : ℕ} (hXL : dyadicScale j < L) :
    ¬sourceScheduledGoodIndex L N j := by
  intro hj
  exact (Nat.not_le_of_gt hXL) hj.2.1

/-- Hence every nonempty initial block uses the analytic fallback with
the actual scheduled cutoff whenever it is at least two, and otherwise
with the harmless cutoff clamped at two. -/
theorem sourceScheduledBlockBound_eq_fallback_of_scale_lt
    {L N j : ℕ} {A K : ℝ}
    (hXL : dyadicScale j < L) :
    sourceScheduledBlockBound L N A K j =
      sourceScheduledFallbackBlockBound L N A K j := by
  rw [sourceScheduledBlockBound,
    if_neg (not_sourceScheduledGoodIndex_of_scale_lt hXL)]

/-- Refined scheduled summand: the provably empty far-initial blocks
contribute zero, while every other block keeps its established analytic
bound. -/
def sourceRefinedScheduledBlockBound
    (L N : ℕ) (A K : ℝ) (j : ℕ) : ℝ :=
  if 8 * dyadicScale j < L then 0
  else sourceScheduledBlockBound L N A K j

/-- Pointwise refined scheduled estimate. -/
theorem card_sourceDyadic_le_refinedScheduledBlock
    {L N j : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A) :
    ((sourceDyadicCoordinateSet
      L N A K (dyadicScale j)).card : ℝ) ≤
      sourceRefinedScheduledBlockBound L N A K j := by
  by_cases hfar : 8 * dyadicScale j < L
  · rw [sourceRefinedScheduledBlockBound, if_pos hfar,
      sourceDyadicCoordinateSet_eq_empty_of_eight_mul_lt hfar]
    simp
  · rw [sourceRefinedScheduledBlockBound, if_neg hfar]
    exact card_sourceDyadic_le_scheduledBlock hL hA

/-- Global source-coordinate estimate with all far-initial blocks removed
exactly and all nonempty initial blocks still analytically bounded. -/
theorem card_sourceCoordinateSet_le_refinedScheduled_sum
    {L N : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hA : 0 ≤ A) :
    ((sourceCoordinateSet L N A K).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        sourceRefinedScheduledBlockBound L N A K j := by
  refine (card_sourceCoordinateSet_le_sum_dyadic L N A K).trans ?_
  apply sum_le_sum
  intro j hj
  simpa [dyadicScale] using
    (card_sourceDyadic_le_refinedScheduledBlock
      (L := L) (N := N) (j := j) (A := A) (K := K) hL hA)

/-- Refined global bound for the canonical bad-source count. -/
theorem card_rankBad_le_refinedScheduled_sum
    {L N : ℕ} {A K : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N) (hA : 0 ≤ A) :
    ((Erdos327.rankBad (Erdos327.upto N)
      (regularSource L A K N)
      ArithmeticFunction.cardFactors).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        sourceRefinedScheduledBlockBound L N A K j := by
  have hcoordinate :
      ((Erdos327.rankBad (Erdos327.upto N)
        (regularSource L A K N)
        ArithmeticFunction.cardFactors).card : ℝ) ≤
        ((sourceCoordinateSet L N A K).card : ℝ) := by
    exact_mod_cast card_rankBad_le_sourceCoordinateSet hL hN
  exact hcoordinate.trans
    (card_sourceCoordinateSet_le_refinedScheduled_sum hL hA)

end

end Erdos327.Analytic
