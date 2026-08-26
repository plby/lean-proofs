import ErdosProblems.Erdos327.Analytic.MixedGlobalAssembly

/-!
# Initial mixed blocks

The common rough linear form in a mixed block is at most `16X`.
Consequently a block is empty when `16X < L`.  Moreover, the scheduled
cutoff fits every dyadic scale after the zeroth one, so for `L ≥ 17` the
literal-cardinality fallback is never needed by a nonempty block.
-/

namespace Erdos327.Analytic

open Finset

noncomputable section

/-- A mixed block whose common rough linear form lies entirely below `L`
is empty. -/
theorem mixedCoordinateBoxBlock_eq_empty_of_sixteen_mul_lt
    {L N X : ℕ} {Ab Kb Ao Ko : ℝ} (hXL : 16 * X < L) :
    mixedCoordinateBoxBlock L N Ab Kb Ao Ko X = ∅ := by
  ext q
  constructor
  · intro hq
    have hblock := mem_mixedCoordinateBoxBlock.mp hq
    have hlinearUpper := (mixedLinear_mem_block_bounds hq).2
    have hcoord := hblock.1
    rw [mixedCoordinateSet, mem_filter] at hcoord
    have hu0 : 0 < mixedU q :=
      (mem_Icc.mp
        (mem_product.mp (mem_product.mp hcoord.1).1).2).1
    rcases hcoord.2 with
      ⟨_hcop, _hw6u, _hx8u, _haHost, _hbLower, _hbUpper,
        _htRough, _huRough, hxRough, _htOdd, _huOdd, _hwOdd,
        _hxOdd, _hbRegular, _haRegular⟩
    have hw0 : 0 < mixedW q :=
      (mem_Icc.mp hblock.2.2).1
    have hx2 : 2 ≤ mixedLinear q := by
      simp only [mixedLinear]
      omega
    have hLx : L ≤ mixedLinear q :=
      cutoff_le_of_rough hx2 hxRough
    omega
  · simp

/-- Every scheduled mixed cutoff fits its dyadic block after the zeroth
scale. -/
theorem mixedScheduledResidualAvailable_of_one_le_index
    {L j : ℕ} (hj : 1 ≤ j) :
    mixedScheduledResidualAvailable L j := by
  unfold mixedScheduledResidualAvailable mixedClampedSieveCutoff
  apply max_le
  · unfold dyadicScale
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  · exact sieveCutoff_le_dyadicScale j

/-- Thus an unavailable scheduled residual cutoff can occur only at the
zeroth dyadic scale. -/
theorem index_eq_zero_of_not_mixedScheduledResidualAvailable
    {L j : ℕ} (hj : ¬mixedScheduledResidualAvailable L j) :
    j = 0 := by
  by_contra hj0
  exact hj
    (mixedScheduledResidualAvailable_of_one_le_index
      (Nat.one_le_iff_ne_zero.mpr hj0))

/-- At `L ≥ 17`, any block that would use literal cardinality is empty. -/
theorem mixedCoordinateBoxBlock_eq_empty_of_not_residualAvailable
    {L N j : ℕ} {Ab Kb Ao Ko : ℝ}
    (hL : 17 ≤ L)
    (hj : ¬mixedScheduledResidualAvailable L j) :
    mixedCoordinateBoxBlock L N Ab Kb Ao Ko (dyadicScale j) = ∅ := by
  have hj0 := index_eq_zero_of_not_mixedScheduledResidualAvailable hj
  subst j
  apply mixedCoordinateBoxBlock_eq_empty_of_sixteen_mul_lt
  simp [dyadicScale]
  omega

/-- Refined mixed summand, with all provably empty blocks replaced by
zero exactly. -/
def mixedRefinedScheduledBlockBound
    (L N : ℕ) (Ab Kb Ao Ko qb qo : ℝ) (j : ℕ) : ℝ :=
  if 16 * dyadicScale j < L then 0
  else mixedScheduledBlockBound L N Ab Kb Ao Ko qb qo j

/-- Pointwise refined scheduled mixed estimate. -/
theorem card_mixedCoordinateBoxBlock_le_refinedScheduledBlock
    {L N j : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * Real.log qb + Ao * Real.log qo) :
    ((mixedCoordinateBoxBlock L N Ab Kb Ao Ko
      (dyadicScale j)).card : ℝ) ≤
      mixedRefinedScheduledBlockBound
        L N Ab Kb Ao Ko qb qo j := by
  by_cases hfar : 16 * dyadicScale j < L
  · rw [mixedRefinedScheduledBlockBound, if_pos hfar,
      mixedCoordinateBoxBlock_eq_empty_of_sixteen_mul_lt hfar]
    simp
  · rw [mixedRefinedScheduledBlockBound, if_neg hfar]
    exact card_mixedCoordinateBoxBlock_le_scheduledBlock
      hL hqb hqo hM

/-- The main mixed-coordinate set is bounded by the refined finite
scheduled sum. -/
theorem card_mixedMainCoordinateSet_le_refinedScheduled_sum
    {L N : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * Real.log qb + Ao * Real.log qo) :
    ((mixedMainCoordinateSet L N Ab Kb Ao Ko).card : ℝ) ≤
      ∑ j ∈ range (Nat.log 2 N + 1),
        mixedRefinedScheduledBlockBound
          L N Ab Kb Ao Ko qb qo j := by
  refine
    (card_mixedMainCoordinateSet_le_sum_boxes
      L N Ab Kb Ao Ko).trans ?_
  apply sum_le_sum
  intro j hj
  exact card_mixedCoordinateBoxBlock_le_refinedScheduledBlock
    hL hqb hqo hM

/-- The canonical mixed-edge count is bounded by the refined sum plus
the one possible exceptional endpoint edge. -/
theorem card_mixedEdges_le_refinedScheduled_sum_add_one
    {L N : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N)
    (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * Real.log qb + Ao * Real.log qo) :
    ((Erdos327.mixedEdges
      (regularOddHost L Ao Ko N)
      (Erdos327.rankFilteredSource (Erdos327.upto N)
        (regularSource L Ab Kb N)
        ArithmeticFunction.cardFactors)).card : ℝ) ≤
      (∑ j ∈ range (Nat.log 2 N + 1),
        mixedRefinedScheduledBlockBound
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
      (card_mixedMainCoordinateSet_le_refinedScheduled_sum
        hL hqb hqo hM)
      (le_refl 1))

end

end Erdos327.Analytic
