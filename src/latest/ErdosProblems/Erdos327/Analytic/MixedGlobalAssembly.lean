import ErdosProblems.Erdos327.Analytic.DyadicCover
import ErdosProblems.Erdos327.Analytic.MixedMainReduction
import ErdosProblems.Erdos327.Analytic.MixedBoxAllCutoffs
import ErdosProblems.Erdos327.Analytic.SieveSchedule

/-!
# Global finite assembly of the mixed-edge estimate

This file inserts the exact sieve schedule into every dyadic mixed-coordinate
block.  There are three regimes.

* Good blocks use the scheduled cutoff, the explicit all-cutoff three-form
  estimate, and the explicit residual Mertens bound.
* Intermediate blocks retain the all-cutoff three-form estimate but keep the
  residual moment as an exact finite sum.
* Initial blocks on which `L ≤ X` or `z ≤ X` is unavailable are retained as
  literal finite block cardinalities.

The final theorem bounds the canonical mixed-edge count by this completely
finite scheduled sum, plus the one possible exceptional endpoint edge from
`MixedMainReduction`.
-/

namespace Erdos327.Analytic

open Finset Real

noncomputable section

/-- The scheduled mixed cutoff clamped at two. -/
def mixedClampedSieveCutoff (j : ℕ) : ℕ :=
  max 2 (sieveCutoff j)

theorem two_le_mixedClampedSieveCutoff (j : ℕ) :
    2 ≤ mixedClampedSieveCutoff j := by
  simp [mixedClampedSieveCutoff]

/-- Once the scheduled cutoff is at least two, clamping does nothing. -/
theorem mixedClampedSieveCutoff_eq
    {j : ℕ} (hj : 2 ≤ sieveCutoff j) :
    mixedClampedSieveCutoff j = sieveCutoff j := by
  exact max_eq_right hj

/-- The scheduled cutoff never exceeds its dyadic outer scale. -/
theorem sieveCutoff_le_dyadicScale (j : ℕ) :
    sieveCutoff j ≤ dyadicScale j := by
  have hden : 0 < 16 * sieveRadius j :=
    Nat.mul_pos (by norm_num) (sieveRadius_pos j)
  have hexponent :
      sieveCutoffExponent j ≤ j := by
    unfold sieveCutoffExponent
    exact Nat.div_le_self j _
  unfold sieveCutoff dyadicScale
  exact Nat.pow_le_pow_right (by norm_num) hexponent

/-- On a block lying beyond the roughness cutoff, the clamped sieve cutoff
also lies below the dyadic scale. -/
theorem mixedClampedSieveCutoff_le_dyadicScale
    {L j : ℕ} (hL : 3 ≤ L) (hLX : L ≤ dyadicScale j) :
    mixedClampedSieveCutoff j ≤ dyadicScale j := by
  unfold mixedClampedSieveCutoff
  apply max_le
  · omega
  · exact sieveCutoff_le_dyadicScale j

/-- The exact residual moment retained on intermediate mixed blocks. -/
def mixedExactResidualMoment
    (L N X : ℕ) (qb qo : ℝ) : ℝ :=
  ∑ t ∈ Icc 1 (N / (X * X)),
    if Rough L t then
      (1 / (qb * qo)) ^ primeFactorCountBetween L X t
    else 0

theorem mixedExactResidualMoment_nonneg
    (L N X : ℕ) {qb qo : ℝ}
    (hqb : 0 ≤ qb) (hqo : 0 ≤ qo) :
    0 ≤ mixedExactResidualMoment L N X qb qo := by
  unfold mixedExactResidualMoment
  apply sum_nonneg
  intro t ht
  split_ifs <;> positivity

/-- All-cutoff three-form control with the residual moment left exact.
Unlike the fully explicit theorem, this requires no lower bound on
`N / X²`. -/
theorem card_mixedCoordinateBoxBlock_le_allCutoffs_mul_exactResidual
    {L N z X R : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hX : 1 ≤ X)
    (hz : 2 ≤ z) (hzX : z ≤ X)
    (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo) :
    ((mixedCoordinateBoxBlock
        L N Ab Kb Ao Ko X).card : ℝ) ≤
      mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
        mixedAllCutoffSharpBoxBound L z X R qb qo *
        mixedExactResidualMoment L N X qb qo := by
  let alpha : ℝ := 1 / qb
  let beta : ℝ := 1 / qo
  let s : ℝ := 1 / (qb * qo)
  have hqb0 : 0 < qb := zero_lt_one.trans hqb
  have hqo0 : 0 < qo := zero_lt_one.trans hqo
  have hprod0 : 0 < qb * qo := mul_pos hqb0 hqo0
  have hprodOne : 1 ≤ qb * qo := by
    nlinarith [mul_pos (sub_pos.mpr hqb) (sub_pos.mpr hqo)]
  have ha0 : 0 ≤ alpha := by
    dsimp [alpha]
    positivity
  have ha1 : alpha ≤ 1 := by
    dsimp [alpha]
    exact (div_le_one₀ hqb0).mpr hqb.le
  have hb0 : 0 ≤ beta := by
    dsimp [beta]
    positivity
  have hb1 : beta ≤ 1 := by
    dsimp [beta]
    exact (div_le_one₀ hqo0).mpr hqo.le
  have hs0 : 0 ≤ s := by
    dsimp [s]
    positivity
  have hs1 : s ≤ 1 := by
    dsimp [s]
    exact (div_le_one₀ hprod0).mpr hprodOne
  have hbase :=
    card_mixedCoordinateBoxBlock_le_box_mul_residual
      (N := N) (z := z) (X := X)
      (Ab := Ab) (Kb := Kb) (Ao := Ao) (Ko := Ko)
      hL hX hzX hqb hqo hM
  have hbox :
      finiteWeightBoxSum
          (crossRetainedFamily (P := oddPrimesUpTo z)
            (mixedQU L alpha) (mixedQW L beta)
            (mixedQLinear L s)) X ≤
        mixedAllCutoffSharpBoxBound L z X R qb qo := by
    dsimp [mixedAllCutoffSharpBoxBound, alpha, beta, s]
    exact mixed_threeFormBoxSum_le_allCutoffs
      ha0 ha1 hb0 hb1 hs0 hs1 (by omega) hz
  have hprefactor0 :=
    mixedBlockPrefactor_nonneg
      (Ab := Ab) (Kb := Kb) (Ao := Ao) (Ko := Ko)
      hL hX hqb hqo
  have hresidual0 :
      0 ≤ ∑ t ∈ Icc 1 (N / (X * X)),
        if Rough L t then
          (1 / (qb * qo)) ^ primeFactorCountBetween L X t
        else 0 := by
    apply sum_nonneg
    intro t ht
    split_ifs <;> positivity
  have hscaledBox :
      mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
          finiteWeightBoxSum
            (crossRetainedFamily (P := oddPrimesUpTo z)
              (mixedQU L alpha) (mixedQW L beta)
              (mixedQLinear L s)) X ≤
        mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
          mixedAllCutoffSharpBoxBound L z X R qb qo :=
    mul_le_mul_of_nonneg_left hbox hprefactor0
  dsimp [alpha, beta, s] at hbase hscaledBox
  exact hbase.trans <|
    mul_le_mul_of_nonneg_right hscaledBox hresidual0

/-- Indices on which the scheduled cutoff and the explicit residual theorem
are simultaneously available. -/
def mixedScheduledGoodIndex (L N j : ℕ) : Prop :=
  2 ≤ sieveCutoff j ∧
    L ≤ dyadicScale j ∧
    sieveCutoff j ≤ dyadicScale j ∧
    L ≤ N / (dyadicScale j * dyadicScale j)

instance mixedScheduledGoodIndexDecidable (L N j : ℕ) :
    Decidable (mixedScheduledGoodIndex L N j) :=
  Classical.propDecidable _

/-- Indices on which the weighted box argument is valid but the explicit
residual Mertens envelope may be unavailable. -/
def mixedScheduledResidualAvailable (_L j : ℕ) : Prop :=
  mixedClampedSieveCutoff j ≤ dyadicScale j

instance mixedScheduledResidualAvailableDecidable (L j : ℕ) :
    Decidable (mixedScheduledResidualAvailable L j) :=
  Classical.propDecidable _

/-- Every block beyond `L` is available for the exact-residual fallback. -/
theorem mixedScheduledResidualAvailable_of_le
    {L j : ℕ} (hL : 3 ≤ L) (hLX : L ≤ dyadicScale j) :
    mixedScheduledResidualAvailable L j :=
  mixedClampedSieveCutoff_le_dyadicScale hL hLX

/-- Under the standing cutoff hypothesis, every literal exact-cardinality
block has dyadic scale below the fixed cutoff `L`.  In particular, this
regime contains only finitely many indices independent of `N`. -/
theorem dyadicScale_lt_L_of_not_mixedScheduledResidualAvailable
    {L j : ℕ} (hL : 3 ≤ L)
    (hj : ¬mixedScheduledResidualAvailable L j) :
    dyadicScale j < L := by
  by_contra hnot
  exact hj <|
    mixedScheduledResidualAvailable_of_le hL
      (Nat.le_of_not_gt hnot)

/-- Fully explicit scheduled mixed-block bound. -/
def mixedScheduledExplicitBlockBound
    (L N : ℕ) (Ab Kb Ao Ko qb qo : ℝ) (j : ℕ) : ℝ :=
  mixedBlockPrefactor L (dyadicScale j) Ab Kb Ao Ko qb qo *
    mixedAllCutoffSharpBoxBound
      L (sieveCutoff j) (dyadicScale j) (sieveRadius j) qb qo *
    mixedBlockResidualBound L N (dyadicScale j) qb qo

/-- Scheduled all-cutoff sieve bound with the exact residual moment. -/
def mixedScheduledExactResidualBlockBound
    (L N : ℕ) (Ab Kb Ao Ko qb qo : ℝ) (j : ℕ) : ℝ :=
  mixedBlockPrefactor L (dyadicScale j) Ab Kb Ao Ko qb qo *
    mixedAllCutoffSharpBoxBound
      L (mixedClampedSieveCutoff j)
        (dyadicScale j) (sieveRadius j) qb qo *
    mixedExactResidualMoment L N (dyadicScale j) qb qo

/-- Literal finite fallback for the initial blocks outside the weighted
analytic range. -/
def mixedScheduledExactCardBlockBound
    (L N : ℕ) (Ab Kb Ao Ko : ℝ) (j : ℕ) : ℝ :=
  ((mixedCoordinateBoxBlock L N Ab Kb Ao Ko
    (dyadicScale j)).card : ℝ)

/-- The non-good branch visibly distinguishes exact-residual blocks from
literal exact-cardinality blocks. -/
def mixedScheduledFallbackBlockBound
    (L N : ℕ) (Ab Kb Ao Ko qb qo : ℝ) (j : ℕ) : ℝ :=
  if mixedScheduledResidualAvailable L j then
    mixedScheduledExactResidualBlockBound
      L N Ab Kb Ao Ko qb qo j
  else
    mixedScheduledExactCardBlockBound L N Ab Kb Ao Ko j

/-- Three-way scheduled bound for a mixed block. -/
def mixedScheduledBlockBound
    (L N : ℕ) (Ab Kb Ao Ko qb qo : ℝ) (j : ℕ) : ℝ :=
  if mixedScheduledGoodIndex L N j then
    mixedScheduledExplicitBlockBound L N Ab Kb Ao Ko qb qo j
  else
    mixedScheduledFallbackBlockBound L N Ab Kb Ao Ko qb qo j

/-- A good mixed block is bounded by the fully explicit scheduled term. -/
theorem card_mixedCoordinateBoxBlock_le_scheduledExplicit
    {L N j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo)
    (hj : mixedScheduledGoodIndex L N j) :
    ((mixedCoordinateBoxBlock L N Ab Kb Ao Ko
      (dyadicScale j)).card : ℝ) ≤
      mixedScheduledExplicitBlockBound
        L N Ab Kb Ao Ko qb qo j := by
  rcases hj with ⟨hz, hLX, hzX, hY⟩
  exact card_mixedCoordinateBoxBlock_le_allCutoffs_explicit
    (L := L) (N := N) (z := sieveCutoff j)
    (X := dyadicScale j) (R := sieveRadius j)
    (Ab := Ab) (Kb := Kb) (Ao := Ao) (Ko := Ko)
    (qb := qb) (qo := qo)
    hL hLX hz hzX hY hqb hqo hM

/-- An intermediate mixed block is bounded by the scheduled all-cutoff
sieve and its exact residual moment. -/
theorem card_mixedCoordinateBoxBlock_le_scheduledExactResidual
    {L N j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo)
    (hj : mixedScheduledResidualAvailable L j) :
    ((mixedCoordinateBoxBlock L N Ab Kb Ao Ko
      (dyadicScale j)).card : ℝ) ≤
      mixedScheduledExactResidualBlockBound
        L N Ab Kb Ao Ko qb qo j := by
  exact card_mixedCoordinateBoxBlock_le_allCutoffs_mul_exactResidual
    (L := L) (N := N) (z := mixedClampedSieveCutoff j)
    (X := dyadicScale j) (R := sieveRadius j)
    (Ab := Ab) (Kb := Kb) (Ao := Ao) (Ko := Ko)
    (qb := qb) (qo := qo)
    hL (by
      unfold dyadicScale
      exact Nat.one_le_pow j 2 (by omega))
    (two_le_mixedClampedSieveCutoff j) hj
    hqb hqo hM

/-- Uniform pointwise bound for the non-good branch. -/
theorem card_mixedCoordinateBoxBlock_le_scheduledFallback
    {L N j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo) :
    ((mixedCoordinateBoxBlock L N Ab Kb Ao Ko
      (dyadicScale j)).card : ℝ) ≤
      mixedScheduledFallbackBlockBound
        L N Ab Kb Ao Ko qb qo j := by
  by_cases hj : mixedScheduledResidualAvailable L j
  · rw [mixedScheduledFallbackBlockBound, if_pos hj]
    exact card_mixedCoordinateBoxBlock_le_scheduledExactResidual
      hL hqb hqo hM hj
  · rw [mixedScheduledFallbackBlockBound, if_neg hj]
    exact le_rfl

/-- Uniform pointwise scheduled bound for every mixed dyadic box. -/
theorem card_mixedCoordinateBoxBlock_le_scheduledBlock
    {L N j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo) :
    ((mixedCoordinateBoxBlock L N Ab Kb Ao Ko
      (dyadicScale j)).card : ℝ) ≤
      mixedScheduledBlockBound L N Ab Kb Ao Ko qb qo j := by
  by_cases hj : mixedScheduledGoodIndex L N j
  · rw [mixedScheduledBlockBound, if_pos hj]
    exact card_mixedCoordinateBoxBlock_le_scheduledExplicit
      hL hqb hqo hM hj
  · rw [mixedScheduledBlockBound, if_neg hj]
    exact card_mixedCoordinateBoxBlock_le_scheduledFallback
      hL hqb hqo hM

/-- The main mixed-coordinate set is covered by the standard analytic boxes
through the finite range `0 ≤ j ≤ log₂ N`. -/
theorem card_mixedMainCoordinateSet_le_sum_boxes
    (L N : ℕ) (Ab Kb Ao Ko : ℝ) :
    ((mixedMainCoordinateSet L N Ab Kb Ao Ko).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        ((mixedCoordinateBoxBlock L N Ab Kb Ao Ko
          (dyadicScale j)).card : ℝ) := by
  have hpos :
      ∀ q ∈ mixedMainCoordinateSet L N Ab Kb Ao Ko,
        1 ≤ mixedU q := by
    intro q hq
    have hcoord := (mem_mixedMainCoordinateSet.mp hq).1
    rw [mixedCoordinateSet, mem_filter] at hcoord
    exact
      (mem_Icc.mp (mem_product.mp (mem_product.mp hcoord.1).1).2).1
  have hupper :
      ∀ q ∈ mixedMainCoordinateSet L N Ab Kb Ao Ko,
        mixedU q ≤ N := by
    intro q hq
    have hcoord := (mem_mixedMainCoordinateSet.mp hq).1
    rw [mixedCoordinateSet, mem_filter] at hcoord
    exact
      (mem_Icc.mp (mem_product.mp (mem_product.mp hcoord.1).1).2).2
  have hcover :=
    card_real_le_sum_card_dyadicSlice
      (S := mixedMainCoordinateSet L N Ab Kb Ao Ko)
      (coord := mixedU) hpos hupper
  refine hcover.trans ?_
  apply sum_le_sum
  intro j hj
  have hsubset :
      dyadicSlice
          (mixedMainCoordinateSet L N Ab Kb Ao Ko) mixedU j ⊆
        mixedCoordinateBoxBlock L N Ab Kb Ao Ko
          (dyadicScale j) := by
    intro q hq
    apply mixedMainCoordinateDyadicBlock_subset_box
    rw [mem_mixedMainCoordinateDyadicBlock]
    simpa [dyadicSlice, dyadicScale] using hq
  exact_mod_cast card_le_card hsubset

/-- Exact finite global bound for the main mixed-coordinate set. -/
theorem card_mixedMainCoordinateSet_le_scheduled_sum
    {L N : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo) :
    ((mixedMainCoordinateSet L N Ab Kb Ao Ko).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        mixedScheduledBlockBound
          L N Ab Kb Ao Ko qb qo j := by
  refine
    (card_mixedMainCoordinateSet_le_sum_boxes
      L N Ab Kb Ao Ko).trans ?_
  apply sum_le_sum
  intro j hj
  exact card_mixedCoordinateBoxBlock_le_scheduledBlock
    hL hqb hqo hM

/-- The canonical mixed-edge cardinality is bounded by the finite scheduled
sum, plus the one possible exceptional endpoint edge. -/
theorem card_mixedEdges_le_scheduled_sum_add_one
    {L N : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N)
    (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo) :
    ((Erdos327.mixedEdges
      (regularOddHost L Ao Ko N)
      (Erdos327.rankFilteredSource (Erdos327.upto N)
        (regularSource L Ab Kb N)
        ArithmeticFunction.cardFactors)).card : ℝ) ≤
      (∑ j ∈ range (Nat.log 2 N + 1),
        mixedScheduledBlockBound
          L N Ab Kb Ao Ko qb qo j) + 1 := by
  have hreductionNat :=
    card_mixedEdges_le_mixedMainCoordinateSet_add_one
      (L := L) (N := N) (Ab := Ab) (Kb := Kb)
      (Ao := Ao) (Ko := Ko) hL hN
  have hreduction :
      ((Erdos327.mixedEdges
        (regularOddHost L Ao Ko N)
        (Erdos327.rankFilteredSource (Erdos327.upto N)
          (regularSource L Ab Kb N)
          ArithmeticFunction.cardFactors)).card : ℝ) ≤
        ((mixedMainCoordinateSet L N Ab Kb Ao Ko).card : ℝ) + 1 := by
    exact_mod_cast hreductionNat
  exact hreduction.trans
    (add_le_add
      (card_mixedMainCoordinateSet_le_scheduled_sum
        hL hqb hqo hM)
      (le_refl 1))

/-- The scheduled sum splits into good explicit blocks and its non-good
fallback. -/
theorem mixed_scheduled_sum_eq_good_add_fallback
    (L N : ℕ) (Ab Kb Ao Ko qb qo : ℝ) :
    (∑ j ∈ range (Nat.log 2 N + 1),
        mixedScheduledBlockBound
          L N Ab Kb Ao Ko qb qo j) =
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (mixedScheduledGoodIndex L N),
        mixedScheduledExplicitBlockBound
          L N Ab Kb Ao Ko qb qo j) +
      ∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦ ¬mixedScheduledGoodIndex L N j),
        mixedScheduledFallbackBlockBound
          L N Ab Kb Ao Ko qb qo j := by
  rw [← sum_filter_add_sum_filter_not
    (range (Nat.log 2 N + 1))
    (mixedScheduledGoodIndex L N)]
  apply congrArg₂ (· + ·)
  · apply sum_congr rfl
    intro j hj
    have hgood := (mem_filter.mp hj).2
    simp [mixedScheduledBlockBound, hgood]
  · apply sum_congr rfl
    intro j hj
    have hbad := (mem_filter.mp hj).2
    simp [mixedScheduledBlockBound, hbad]

/-- The non-good sum further splits into exact-residual blocks and literal
exact-cardinality blocks. -/
theorem mixed_fallback_sum_eq_residual_add_exact
    (L N : ℕ) (Ab Kb Ao Ko qb qo : ℝ) :
    (∑ j ∈ (range (Nat.log 2 N + 1)).filter
        (fun j ↦ ¬mixedScheduledGoodIndex L N j),
      mixedScheduledFallbackBlockBound
        L N Ab Kb Ao Ko qb qo j) =
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦
            ¬mixedScheduledGoodIndex L N j ∧
              mixedScheduledResidualAvailable L j),
        mixedScheduledExactResidualBlockBound
          L N Ab Kb Ao Ko qb qo j) +
      ∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦
            ¬mixedScheduledGoodIndex L N j ∧
              ¬mixedScheduledResidualAvailable L j),
        mixedScheduledExactCardBlockBound
          L N Ab Kb Ao Ko j := by
  let bad :=
    (range (Nat.log 2 N + 1)).filter
      (fun j ↦ ¬mixedScheduledGoodIndex L N j)
  rw [← sum_filter_add_sum_filter_not
    bad (mixedScheduledResidualAvailable L)]
  apply congrArg₂ (· + ·)
  · apply sum_congr
    · ext j
      simp [bad, and_assoc]
    · intro j hj
      have havailable := (mem_filter.mp hj).2
      simp [mixedScheduledFallbackBlockBound, havailable]
  · apply sum_congr
    · ext j
      simp [bad, and_assoc]
    · intro j hj
      have hunavailable := (mem_filter.mp hj).2
      simp [mixedScheduledFallbackBlockBound, hunavailable]

/-- Three-way display of the exact finite scheduled sum. -/
theorem mixed_scheduled_sum_eq_explicit_add_residual_add_exact
    (L N : ℕ) (Ab Kb Ao Ko qb qo : ℝ) :
    (∑ j ∈ range (Nat.log 2 N + 1),
        mixedScheduledBlockBound
          L N Ab Kb Ao Ko qb qo j) =
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (mixedScheduledGoodIndex L N),
        mixedScheduledExplicitBlockBound
          L N Ab Kb Ao Ko qb qo j) +
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦
            ¬mixedScheduledGoodIndex L N j ∧
              mixedScheduledResidualAvailable L j),
        mixedScheduledExactResidualBlockBound
          L N Ab Kb Ao Ko qb qo j) +
      ∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦
            ¬mixedScheduledGoodIndex L N j ∧
              ¬mixedScheduledResidualAvailable L j),
        mixedScheduledExactCardBlockBound
          L N Ab Kb Ao Ko j := by
  rw [mixed_scheduled_sum_eq_good_add_fallback,
    mixed_fallback_sum_eq_residual_add_exact]
  ring

/-- Canonical mixed-edge bound with all three finite block regimes displayed
in the theorem statement. -/
theorem card_mixedEdges_le_explicit_add_residual_add_exact_add_one
    {L N : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N)
    (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo) :
    ((Erdos327.mixedEdges
      (regularOddHost L Ao Ko N)
      (Erdos327.rankFilteredSource (Erdos327.upto N)
        (regularSource L Ab Kb N)
        ArithmeticFunction.cardFactors)).card : ℝ) ≤
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (mixedScheduledGoodIndex L N),
        mixedScheduledExplicitBlockBound
          L N Ab Kb Ao Ko qb qo j) +
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦
            ¬mixedScheduledGoodIndex L N j ∧
              mixedScheduledResidualAvailable L j),
        mixedScheduledExactResidualBlockBound
          L N Ab Kb Ao Ko qb qo j) +
      (∑ j ∈ (range (Nat.log 2 N + 1)).filter
          (fun j ↦
            ¬mixedScheduledGoodIndex L N j ∧
              ¬mixedScheduledResidualAvailable L j),
        mixedScheduledExactCardBlockBound
          L N Ab Kb Ao Ko j) + 1 := by
  rw [← mixed_scheduled_sum_eq_explicit_add_residual_add_exact
    L N Ab Kb Ao Ko qb qo]
  exact card_mixedEdges_le_scheduled_sum_add_one
    hL hN hqb hqo hM

end

end Erdos327.Analytic
