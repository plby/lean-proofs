/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricPaddedRemoteRenewal
import ErdosProblems.Erdos1165.AnnularRecursiveProfileTailUpper
import ErdosProblems.Erdos1165.AnnularRecursiveConstrainedProfileTailUpper
import ErdosProblems.Erdos1165.AnnularRecursiveProfileEndpointTail

/-!
# Recursive profile rows inside the padded remote renewal

This file inserts one fixed refinement-chain row into the remote renewal.
The recursive row costs retain their exact product, while the endpoint
oscillation of all top-level children is paid only once through the reserved
`exp (1/2)` factor.
-/

open Filter
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricPaddedRecursiveRenewal

open AnnularIntegratedProfileKernel AnnularRecursiveDecoratedProfileCode
open AnnularLiteralNestedProfileTailUpper
open AnnularRecursiveProfileEndpointTail
open AnnularRecursiveProfileTailUpper
open AnnularRecursiveConstrainedProfileTailUpper
open AnnularRecursiveProfileShape AnnularRecursiveWeightedRenewal
open AppendixFirstMoment AppendixPair AppendixPairMoment
open AsymmetricActualFarPairData AsymmetricPaddedRemoteRenewal
open ProfileGapChain ProfileListExponent ProfileSmallBall ProfileWeightUpper
open ProfileConditionalTailUpper
open ThickPoint
open Proposition13Scales

noncomputable section

/-- A fixed weak-composition genealogy, with all of its recursively decorated
children, is dominated by its exact radial reference mass times the unmarked
remote endpoint kernel. -/
theorem profileRefinementChainPaddedRenewalKernel_le_expHalf_unmarked
    {q l a : ℕ} {rest : List ℕ}
    (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 2 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (ha : a ≤ 3 * q ^ 2)
    (chain : GapChain (a :: rest)) (center : Point)
    (htreeRow : ∀ (i : Fin a)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center),
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
          center (profileRefinementTrees a rest chain i) z v ≤
        ENNReal.ofReal
          (profileRefinementTreeCost
            ((1 + 1 / (q : ℝ) ^ 6) / 2)
            (profileRefinementTrees a rest chain i)))
    (u : PaddedMiddlePoint q (pairPrefixScale q l) center)
    (w : PaddedOuterPoint q l center) :
    heterogeneousRenewalKernel
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        (List.ofFn fun i : Fin a ↦
          profileRefinementTrees a rest chain i) u w ≤
      ENNReal.ofReal
          ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center u w := by
  classical
  let halfRow : ℝ := (1 + 1 / (q : ℝ) ^ 6) / 2
  let tree : Fin a → ProfileRefinementTree := fun i ↦
    profileRefinementTrees a rest chain i
  let trees : List ProfileRefinementTree := List.ofFn tree
  let loss : ProfileRefinementTree → ℝ≥0∞ := fun t ↦
    if ht : ∃ i, tree i = t then
      ENNReal.ofReal (profileRefinementTreeCost halfRow
        (tree (Classical.choose ht)))
    else ∞
  have hcost0 (i : Fin a) :
      0 ≤ profileRefinementTreeCost halfRow (tree i) := by
    apply profileRefinementTreeCost_nonneg
    dsimp only [halfRow]
    positivity
  have hloss_tree (i : Fin a) : loss (tree i) =
      ENNReal.ofReal (profileRefinementTreeCost halfRow (tree i)) := by
    dsimp only [loss]
    split
    next h =>
      congr 2
      exact Classical.choose_spec h
    next h => exact (h ⟨i, rfl⟩).elim
  have hrow (t : ProfileRefinementTree)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center) :
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
          center t z v ≤ loss t := by
    by_cases ht : ∃ i, tree i = t
    · let i := Classical.choose ht
      have hi : tree i = t := Classical.choose_spec ht
      rw [← hi, hloss_tree i]
      simpa only [halfRow, tree] using htreeRow i z
    · simp only [loss, dif_neg ht]
      exact le_top
  have hpopulation : trees.length ≤ 3 * q ^ 2 := by
    simpa only [trees, List.length_ofFn] using ha
  have hsubstitute :=
    heterogeneousRecursivePaddedRenewalKernel_le_expHalf_unmarked
      hq hl hpadding hpadPos hconstant center loss hrow trees hpopulation u w
  have hloss : (trees.map loss).prod =
      ENNReal.ofReal
        ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
          gapChainMass (a :: rest) chain) := by
    calc
      (trees.map loss).prod =
          ∏ i : Fin a, ENNReal.ofReal
            (profileRefinementTreeCost halfRow (tree i)) := by
              simp only [trees, List.map_ofFn, List.prod_ofFn,
                Function.comp_apply, hloss_tree]
      _ = ENNReal.ofReal
          (∏ i : Fin a, profileRefinementTreeCost halfRow (tree i)) := by
            symm
            apply ENNReal.ofReal_prod_of_nonneg
            intro i _
            exact hcost0 i
      _ = ENNReal.ofReal
          ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) := by
            rw [show (∏ i : Fin a,
              profileRefinementTreeCost halfRow (tree i)) =
                (2 * halfRow) ^ radialWordLength (a :: rest) *
                  gapChainMass (a :: rest) chain by
              exact prod_profileRefinementTreeCost_eq a rest chain halfRow]
            congr 2
            dsimp only [halfRow]
            ring
  convert hsubstitute using 1 <;>
    simp only [trees, tree, hloss]

/-- Multi-segment form of the fixed-genealogy padded row.  The children are
allocated in chronological order among all retained remote bridge segments,
while their exact recursive row-cost product is unchanged. -/
theorem profileRefinementChainPaddedMultiRenewalKernel_le_expHalf_unmarked
    {q l a : ℕ} {rest : List ℕ}
    (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 2 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (ha : a ≤ 3 * q ^ 2)
    (chain : GapChain (a :: rest)) (center : Point)
    (htreeRow : ∀ (i : Fin a)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center),
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
          center (profileRefinementTrees a rest chain i) z v ≤
        ENNReal.ofReal
          (profileRefinementTreeCost
            ((1 + 1 / (q : ℝ) ^ 6) / 2)
            (profileRefinementTrees a rest chain i)))
    (segments : List
      (PaddedMiddlePoint q (pairPrefixScale q l) center ×
        PaddedOuterPoint q l center)) :
    heterogeneousMultiRenewalKernel
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        segments (List.ofFn fun i : Fin a ↦
          profileRefinementTrees a rest chain i) ≤
      ENNReal.ofReal
          ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          (segments.map fun segment ↦
            paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
              center segment.1 segment.2).prod := by
  classical
  let halfRow : ℝ := (1 + 1 / (q : ℝ) ^ 6) / 2
  let tree : Fin a → ProfileRefinementTree := fun i ↦
    profileRefinementTrees a rest chain i
  let trees : List ProfileRefinementTree := List.ofFn tree
  let loss : ProfileRefinementTree → ℝ≥0∞ := fun t ↦
    if ht : ∃ i, tree i = t then
      ENNReal.ofReal (profileRefinementTreeCost halfRow
        (tree (Classical.choose ht)))
    else ∞
  have hcost0 (i : Fin a) :
      0 ≤ profileRefinementTreeCost halfRow (tree i) := by
    apply profileRefinementTreeCost_nonneg
    dsimp only [halfRow]
    positivity
  have hloss_tree (i : Fin a) : loss (tree i) =
      ENNReal.ofReal (profileRefinementTreeCost halfRow (tree i)) := by
    dsimp only [loss]
    split
    next h =>
      congr 2
      exact Classical.choose_spec h
    next h => exact (h ⟨i, rfl⟩).elim
  have hrow (t : ProfileRefinementTree)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center) :
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
          center t z v ≤ loss t := by
    by_cases ht : ∃ i, tree i = t
    · let i := Classical.choose ht
      have hi : tree i = t := Classical.choose_spec ht
      rw [← hi, hloss_tree i]
      simpa only [halfRow, tree] using htreeRow i z
    · simp only [loss, dif_neg ht]
      exact le_top
  have hpopulation : trees.length ≤ 3 * q ^ 2 := by
    simpa only [trees, List.length_ofFn] using ha
  have hsubstitute :=
    heterogeneousMultiRecursivePaddedRenewalKernel_le_expHalf_unmarked
      hq hl hpadding hpadPos hconstant center loss hrow trees hpopulation
        segments
  have hloss : (trees.map loss).prod =
      ENNReal.ofReal
        ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
          gapChainMass (a :: rest) chain) := by
    calc
      (trees.map loss).prod =
          ∏ i : Fin a, ENNReal.ofReal
            (profileRefinementTreeCost halfRow (tree i)) := by
              simp only [trees, List.map_ofFn, List.prod_ofFn,
                Function.comp_apply, hloss_tree]
      _ = ENNReal.ofReal
          (∏ i : Fin a, profileRefinementTreeCost halfRow (tree i)) := by
            symm
            apply ENNReal.ofReal_prod_of_nonneg
            intro i _
            exact hcost0 i
      _ = ENNReal.ofReal
          ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) := by
            rw [show (∏ i : Fin a,
              profileRefinementTreeCost halfRow (tree i)) =
                (2 * halfRow) ^ radialWordLength (a :: rest) *
                  gapChainMass (a :: rest) chain by
              exact prod_profileRefinementTreeCost_eq a rest chain halfRow]
            congr 2
            dsimp only [halfRow]
            ring
  simpa only [trees, tree, hloss] using hsubstitute

/-- Fixed-genealogy row for several coarse bridges that begin at level
`l + 1`, before the padded predecessor boundary is reached. -/
theorem profileRefinementChainPaddedPreludeMultiRenewalKernel_le_expHalf_unmarked
    {q l a : ℕ} {rest : List ℕ}
    (hq : 10000 ≤ q)
    (hl : l ≤ decorrelationCutoff q)
    (hpadding : decorrelationPadding q ≤ q)
    (hpadPos : 2 ≤ decorrelationPadding q)
    (hconstant : PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ))
    (ha : a ≤ 3 * q ^ 2)
    (chain : GapChain (a :: rest)) (center : Point)
    (htreeRow : ∀ (i : Fin a)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center),
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
          center (profileRefinementTrees a rest chain i) z v ≤
        ENNReal.ofReal
          (profileRefinementTreeCost
            ((1 + 1 / (q : ℝ) ^ 6) / 2)
            (profileRefinementTrees a rest chain i)))
    (segments : List
      ((PaddedNearPoint q l center ⊕
          PaddedMiddlePoint q (pairPrefixScale q l) center) ×
        PaddedOuterPoint q l center)) :
    heterogeneousPreludeMultiRenewalKernel
        (paddedPreludeEntryKernelENNReal q l (pairPrefixScale q l) center)
        (paddedPreludeDirectKernelENNReal q l (pairPrefixScale q l) center)
        (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
        (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
        (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
        segments (List.ofFn fun i : Fin a ↦
          profileRefinementTrees a rest chain i) ≤
      ENNReal.ofReal
          ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          (segments.map fun segment ↦ match segment.1 with
            | Sum.inl start =>
                paddedNearUnmarkedKernelENNReal q l center start segment.2
            | Sum.inr u =>
                paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                  center u segment.2).prod := by
  classical
  let halfRow : ℝ := (1 + 1 / (q : ℝ) ^ 6) / 2
  let tree : Fin a → ProfileRefinementTree := fun i ↦
    profileRefinementTrees a rest chain i
  let trees : List ProfileRefinementTree := List.ofFn tree
  let loss : ProfileRefinementTree → ℝ≥0∞ := fun t ↦
    if ht : ∃ i, tree i = t then
      ENNReal.ofReal (profileRefinementTreeCost halfRow
        (tree (Classical.choose ht)))
    else ∞
  have hcost0 (i : Fin a) :
      0 ≤ profileRefinementTreeCost halfRow (tree i) := by
    apply profileRefinementTreeCost_nonneg
    dsimp only [halfRow]
    positivity
  have hloss_tree (i : Fin a) : loss (tree i) =
      ENNReal.ofReal (profileRefinementTreeCost halfRow (tree i)) := by
    dsimp only [loss]
    split
    next h =>
      congr 2
      exact Classical.choose_spec h
    next h => exact (h ⟨i, rfl⟩).elim
  have hrow (t : ProfileRefinementTree)
      (z : PaddedInnerPoint q (pairPrefixScale q l) center) :
      ∑ v, recursiveProfileGapKernelENNReal q (pairPrefixScale q l)
          center t z v ≤ loss t := by
    by_cases ht : ∃ i, tree i = t
    · let i := Classical.choose ht
      have hi : tree i = t := Classical.choose_spec ht
      rw [← hi, hloss_tree i]
      simpa only [halfRow, tree] using htreeRow i z
    · simp only [loss, dif_neg ht]
      exact le_top
  have hpopulation : trees.length ≤ 3 * q ^ 2 := by
    simpa only [trees, List.length_ofFn] using ha
  have hsubstitute :=
    heterogeneousPreludeMultiRecursivePaddedRenewalKernel_le_expHalf_unmarked
      hq hl hpadding hpadPos hconstant center loss hrow trees hpopulation
        segments
  have hloss : (trees.map loss).prod =
      ENNReal.ofReal
        ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
          gapChainMass (a :: rest) chain) := by
    calc
      (trees.map loss).prod =
          ∏ i : Fin a, ENNReal.ofReal
            (profileRefinementTreeCost halfRow (tree i)) := by
              simp only [trees, List.map_ofFn, List.prod_ofFn,
                Function.comp_apply, hloss_tree]
      _ = ENNReal.ofReal
          (∏ i : Fin a, profileRefinementTreeCost halfRow (tree i)) := by
            symm
            apply ENNReal.ofReal_prod_of_nonneg
            intro i _
            exact hcost0 i
      _ = ENNReal.ofReal
          ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) := by
            rw [show (∏ i : Fin a,
              profileRefinementTreeCost halfRow (tree i)) =
                (2 * halfRow) ^ radialWordLength (a :: rest) *
                  gapChainMass (a :: rest) chain by
              exact prod_profileRefinementTreeCost_eq a rest chain halfRow]
            congr 2
            dsimp only [halfRow]
            ring
  convert hsubstitute using 1
  · rw [← hloss]
    congr 1

/-- Eventual uniform form of the padded fixed-chain row, with every analytic
and regularity parameter discharged at the ambient profile scale. -/
theorem eventually_profileRefinementChainPaddedRenewalKernel_le_expHalf_unmarked :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      ∀ (a : ℕ) (rest : List ℕ),
        pairPrefixScale q l + rest.length ≤ q →
        a ≤ 3 * q ^ 2 →
      ∀ (chain : GapChain (a :: rest)) (center : Point)
        (u : PaddedMiddlePoint q (pairPrefixScale q l) center)
        (w : PaddedOuterPoint q l center),
        heterogeneousRenewalKernel
            (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
            (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
            (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
            (List.ofFn fun i : Fin a ↦
              profileRefinementTrees a rest chain i) u w ≤
          ENNReal.ofReal
              ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
                gapChainMass (a :: rest) chain) *
            ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
              paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                center u w := by
  have hconstant : ∀ᶠ q : ℕ in atTop,
      PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ) := by
    filter_upwards
        [eventually_ge_atTop
          ⌈PotentialRadialGlobal.globalRadialConstant⌉₊]
        with q hq
    exact (Nat.le_ceil PotentialRadialGlobal.globalRadialConstant).trans
      (by exact_mod_cast hq)
  filter_upwards
      [AnnularRecursiveProfileRow.eventually_profileRefinementTreeKernel_row_le,
       eventually_ge_atTop 10000,
       AppendixPairMoment.eventually_geometricCutoff_le_decorrelationPadding,
       AppendixPairMoment.eventually_decorrelationPadding_lt,
       hconstant]
      with q htree hq hpaddingLower hpaddingUpper hconstantQ
  intro l hl a rest hdepth ha chain center u w
  have hpadding : decorrelationPadding q ≤ q := hpaddingUpper.le
  have hpadPos : 2 ≤ decorrelationPadding q :=
    (show 2 ≤ 32 by omega).trans
      (GaussianGeometricCutoff.geometricCutoff_ge_thirty_two.trans
        hpaddingLower)
  apply profileRefinementChainPaddedRenewalKernel_le_expHalf_unmarked
    hq hl hpadding hpadPos hconstantQ ha chain center
  intro i z
  exact htree (pairPrefixScale q l) (by
      have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
        pairPrefixScale_eq_of_add_le
          (Nat.add_le_of_le_sub hpadding hl)
      omega)
    a rest hdepth chain i center z

/-- After summing every genealogy for one constrained suffix, the recursive
half-budget and the remote endpoint half-budget combine to the canonical
`exp 1` profile-tail coefficient. -/
theorem eventually_sum_profileRefinementChainPaddedRenewalKernel_le_unmarked :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      ∀ (delta : ℝ) (m : Profile q),
        IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (a : ℕ) (rest : List ℕ),
        profileSegmentValues m (pairPrefixScale q l) = a :: rest →
      ∀ (center : Point)
        (u : PaddedMiddlePoint q (pairPrefixScale q l) center)
        (w : PaddedOuterPoint q l center),
        (∑ chain : GapChain (a :: rest),
          heterogeneousRenewalKernel
            (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
            (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
            (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
            (List.ofFn fun i : Fin a ↦
              profileRefinementTrees a rest chain i) u w) ≤
          ENNReal.ofReal
              (Real.exp 1 * transitionSegmentProduct
                (pairPrefixScale q l) (q - pairPrefixScale q l)
                (profileAtScale m)) *
            paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
              center u w := by
  have hconstant : ∀ᶠ q : ℕ in atTop,
      PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ) := by
    filter_upwards
        [eventually_ge_atTop
          ⌈PotentialRadialGlobal.globalRadialConstant⌉₊]
        with q hq
    exact (Nat.le_ceil PotentialRadialGlobal.globalRadialConstant).trans
      (by exact_mod_cast hq)
  filter_upwards
      [AnnularRecursiveProfileRow.eventually_profileRefinementTreeKernel_row_le,
       eventually_ge_atTop 10000,
       AppendixPairMoment.eventually_geometricCutoff_le_decorrelationPadding,
       AppendixPairMoment.eventually_decorrelationPadding_lt,
       hconstant]
      with q htree hq hpaddingLower hpaddingUpper hconstantQ
  intro l hl delta m hm hdelta a rest hvalues center u w
  let start := pairPrefixScale q l
  have hpadding : decorrelationPadding q ≤ q := hpaddingUpper.le
  have hpadPos : 2 ≤ decorrelationPadding q :=
    (show 2 ≤ 32 by omega).trans
      (GaussianGeometricCutoff.geometricCutoff_ge_thirty_two.trans
        hpaddingLower)
  have hstart : 2 ≤ start := by
    have hpref : start = l + decorrelationPadding q :=
      pairPrefixScale_eq_of_add_le
        (Nat.add_le_of_le_sub hpadding hl)
    omega
  have hstartq : start ≤ q := by
    have hpref : start = l + decorrelationPadding q :=
      pairPrefixScale_eq_of_add_le
        (Nat.add_le_of_le_sub hpadding hl)
    rw [hpref]
    exact Nat.add_le_of_le_sub hpadding hl
  have hdepth : start + rest.length ≤ q := by
    have hlength : (a :: rest).length = q + 1 - start := by
      rw [← hvalues, profileSegmentValues_length]
    simp only [List.length_cons] at hlength
    omega
  have ha : a ≤ 3 * q ^ 2 :=
    profileSegmentValues_head_le_three_mul_sq
      hstart hstartq hm hdelta hvalues
  have hchain (chain : GapChain (a :: rest)) :
      heterogeneousRenewalKernel
          (paddedInwardKernelENNReal q l start center)
          (recursiveProfileGapKernelENNReal q start center)
          (paddedEscapeKernelENNReal q l start center)
          (List.ofFn fun i : Fin a ↦
            profileRefinementTrees a rest chain i) u w ≤
        ENNReal.ofReal
            ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain) *
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
            paddedUnmarkedKernelENNReal q l start center u w := by
    apply profileRefinementChainPaddedRenewalKernel_le_expHalf_unmarked
      hq hl hpadding hpadPos hconstantQ ha chain center
    intro i z
    exact htree start (by omega) a rest hdepth chain i center z
  have hreference := sum_profileRefinementChainReferenceCost_le_expHalf
    (n := q) (start := start) (a := a) (rest := rest)
    (by omega) hstart hstartq hm hdelta hvalues
  calc
    (∑ chain : GapChain (a :: rest),
        heterogeneousRenewalKernel
          (paddedInwardKernelENNReal q l start center)
          (recursiveProfileGapKernelENNReal q start center)
          (paddedEscapeKernelENNReal q l start center)
          (List.ofFn fun i : Fin a ↦
            profileRefinementTrees a rest chain i) u w) ≤
      ∑ chain : GapChain (a :: rest),
        ENNReal.ofReal
            ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain) *
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
            paddedUnmarkedKernelENNReal q l start center u w := by
          exact Finset.sum_le_sum fun chain _ ↦ hchain chain
    _ = (∑ chain : GapChain (a :: rest),
          ENNReal.ofReal
            ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain)) *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          paddedUnmarkedKernelENNReal q l start center u w := by
            rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ENNReal.ofReal
          (Real.exp (1 / 2 : ℝ) *
            transitionSegmentProduct start (q - start) (profileAtScale m)) *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          paddedUnmarkedKernelENNReal q l start center u w := by
            gcongr
    _ = ENNReal.ofReal
          (Real.exp 1 *
            transitionSegmentProduct start (q - start) (profileAtScale m)) *
        paddedUnmarkedKernelENNReal q l start center u w := by
      have hfactor0 : 0 ≤ Real.exp (1 / 2 : ℝ) *
          transitionSegmentProduct start (q - start) (profileAtScale m) :=
        mul_nonneg (Real.exp_nonneg _)
          (transitionSegmentProduct_nonneg _ _ _)
      rw [← ENNReal.ofReal_mul hfactor0]
      congr 2
      calc
        Real.exp (1 / 2 : ℝ) *
              transitionSegmentProduct start (q - start) (profileAtScale m) *
            Real.exp (1 / 2 : ℝ) =
            (Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ)) *
              transitionSegmentProduct start (q - start)
                (profileAtScale m) := by ring
        _ = Real.exp 1 * transitionSegmentProduct start (q - start)
              (profileAtScale m) := by
            rw [← Real.exp_add]
            norm_num

/-- Summing all genealogies with their children distributed among several
retained bridge segments gives the same canonical `exp 1` profile-tail
coefficient, times the product of the unmarked segment kernels. -/
theorem eventually_sum_profileRefinementChainPaddedMultiRenewalKernel_le_unmarked :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      ∀ (delta : ℝ) (m : Profile q),
        IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (a : ℕ) (rest : List ℕ),
        profileSegmentValues m (pairPrefixScale q l) = a :: rest →
      ∀ (center : Point)
        (segments : List
          (PaddedMiddlePoint q (pairPrefixScale q l) center ×
            PaddedOuterPoint q l center)),
        (∑ chain : GapChain (a :: rest),
          heterogeneousMultiRenewalKernel
            (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
            (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
            (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
            segments (List.ofFn fun i : Fin a ↦
              profileRefinementTrees a rest chain i)) ≤
          ENNReal.ofReal
              (Real.exp 1 * transitionSegmentProduct
                (pairPrefixScale q l) (q - pairPrefixScale q l)
                (profileAtScale m)) *
            (segments.map fun segment ↦
              paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                center segment.1 segment.2).prod := by
  have hconstant : ∀ᶠ q : ℕ in atTop,
      PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ) := by
    filter_upwards
        [eventually_ge_atTop
          ⌈PotentialRadialGlobal.globalRadialConstant⌉₊]
        with q hq
    exact (Nat.le_ceil PotentialRadialGlobal.globalRadialConstant).trans
      (by exact_mod_cast hq)
  filter_upwards
      [AnnularRecursiveProfileRow.eventually_profileRefinementTreeKernel_row_le,
       eventually_ge_atTop 10000,
       AppendixPairMoment.eventually_geometricCutoff_le_decorrelationPadding,
       AppendixPairMoment.eventually_decorrelationPadding_lt,
       hconstant]
      with q htree hq hpaddingLower hpaddingUpper hconstantQ
  intro l hl delta m hm hdelta a rest hvalues center segments
  let start := pairPrefixScale q l
  have hpadding : decorrelationPadding q ≤ q := hpaddingUpper.le
  have hpadPos : 2 ≤ decorrelationPadding q :=
    (show 2 ≤ 32 by omega).trans
      (GaussianGeometricCutoff.geometricCutoff_ge_thirty_two.trans
        hpaddingLower)
  have hstart : 2 ≤ start := by
    have hpref : start = l + decorrelationPadding q :=
      pairPrefixScale_eq_of_add_le
        (Nat.add_le_of_le_sub hpadding hl)
    omega
  have hstartq : start ≤ q := by
    have hpref : start = l + decorrelationPadding q :=
      pairPrefixScale_eq_of_add_le
        (Nat.add_le_of_le_sub hpadding hl)
    rw [hpref]
    exact Nat.add_le_of_le_sub hpadding hl
  have hdepth : start + rest.length ≤ q := by
    have hlength : (a :: rest).length = q + 1 - start := by
      rw [← hvalues, profileSegmentValues_length]
    simp only [List.length_cons] at hlength
    omega
  have ha : a ≤ 3 * q ^ 2 :=
    profileSegmentValues_head_le_three_mul_sq
      hstart hstartq hm hdelta hvalues
  have hchain (chain : GapChain (a :: rest)) :
      heterogeneousMultiRenewalKernel
          (paddedInwardKernelENNReal q l start center)
          (recursiveProfileGapKernelENNReal q start center)
          (paddedEscapeKernelENNReal q l start center)
          segments (List.ofFn fun i : Fin a ↦
            profileRefinementTrees a rest chain i) ≤
        ENNReal.ofReal
            ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain) *
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
            (segments.map fun segment ↦
              paddedUnmarkedKernelENNReal q l start
                center segment.1 segment.2).prod := by
    apply profileRefinementChainPaddedMultiRenewalKernel_le_expHalf_unmarked
      hq hl hpadding hpadPos hconstantQ ha chain center
    · intro i z
      exact htree start (by omega) a rest hdepth chain i center z
  have hreference := sum_profileRefinementChainReferenceCost_le_expHalf
    (n := q) (start := start) (a := a) (rest := rest)
    (by omega) hstart hstartq hm hdelta hvalues
  calc
    (∑ chain : GapChain (a :: rest),
        heterogeneousMultiRenewalKernel
          (paddedInwardKernelENNReal q l start center)
          (recursiveProfileGapKernelENNReal q start center)
          (paddedEscapeKernelENNReal q l start center)
          segments (List.ofFn fun i : Fin a ↦
            profileRefinementTrees a rest chain i)) ≤
      ∑ chain : GapChain (a :: rest),
        ENNReal.ofReal
            ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain) *
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
            (segments.map fun segment ↦
              paddedUnmarkedKernelENNReal q l start
                center segment.1 segment.2).prod := by
          exact Finset.sum_le_sum fun chain _ ↦ hchain chain
    _ = (∑ chain : GapChain (a :: rest),
          ENNReal.ofReal
            ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain)) *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          (segments.map fun segment ↦
            paddedUnmarkedKernelENNReal q l start
              center segment.1 segment.2).prod := by
            rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ENNReal.ofReal
          (Real.exp (1 / 2 : ℝ) *
            transitionSegmentProduct start (q - start) (profileAtScale m)) *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          (segments.map fun segment ↦
            paddedUnmarkedKernelENNReal q l start
              center segment.1 segment.2).prod := by
            gcongr
    _ = ENNReal.ofReal
          (Real.exp 1 *
            transitionSegmentProduct start (q - start) (profileAtScale m)) *
        (segments.map fun segment ↦
          paddedUnmarkedKernelENNReal q l start
            center segment.1 segment.2).prod := by
      have hfactor0 : 0 ≤ Real.exp (1 / 2 : ℝ) *
          transitionSegmentProduct start (q - start) (profileAtScale m) :=
        mul_nonneg (Real.exp_nonneg _)
          (transitionSegmentProduct_nonneg _ _ _)
      rw [← ENNReal.ofReal_mul hfactor0]
      congr 2
      calc
        Real.exp (1 / 2 : ℝ) *
              transitionSegmentProduct start (q - start) (profileAtScale m) *
            Real.exp (1 / 2 : ℝ) =
            (Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ)) *
              transitionSegmentProduct start (q - start)
                (profileAtScale m) := by ring
        _ = Real.exp 1 * transitionSegmentProduct start (q - start)
              (profileAtScale m) := by
            rw [← Real.exp_add]
            norm_num

/-- Summing all genealogies for preliminary-entrance coarse bridges gives
the canonical `exp 1` profile-tail coefficient times the original unmarked
coarse bridge product. -/
theorem eventually_sum_profileRefinementChainPaddedPreludeMultiRenewalKernel_le_unmarked :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      ∀ (delta : ℝ) (m : Profile q),
        IsConstrainedProfile delta m → delta ≤ 1 →
      ∀ (a : ℕ) (rest : List ℕ),
        profileSegmentValues m (pairPrefixScale q l) = a :: rest →
      ∀ (center : Point)
        (segments : List
          ((PaddedNearPoint q l center ⊕
              PaddedMiddlePoint q (pairPrefixScale q l) center) ×
            PaddedOuterPoint q l center)),
        (∑ chain : GapChain (a :: rest),
          heterogeneousPreludeMultiRenewalKernel
            (paddedPreludeEntryKernelENNReal q l
              (pairPrefixScale q l) center)
            (paddedPreludeDirectKernelENNReal q l
              (pairPrefixScale q l) center)
            (paddedInwardKernelENNReal q l (pairPrefixScale q l) center)
            (recursiveProfileGapKernelENNReal q (pairPrefixScale q l) center)
            (paddedEscapeKernelENNReal q l (pairPrefixScale q l) center)
            segments (List.ofFn fun i : Fin a ↦
              profileRefinementTrees a rest chain i)) ≤
          ENNReal.ofReal
              (Real.exp 1 * transitionSegmentProduct
                (pairPrefixScale q l) (q - pairPrefixScale q l)
                (profileAtScale m)) *
            (segments.map fun segment ↦ match segment.1 with
              | Sum.inl start =>
                  paddedNearUnmarkedKernelENNReal q l center start segment.2
              | Sum.inr u =>
                  paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                    center u segment.2).prod := by
  have hconstant : ∀ᶠ q : ℕ in atTop,
      PotentialRadialGlobal.globalRadialConstant ≤ (q : ℝ) := by
    filter_upwards
        [eventually_ge_atTop
          ⌈PotentialRadialGlobal.globalRadialConstant⌉₊]
        with q hq
    exact (Nat.le_ceil PotentialRadialGlobal.globalRadialConstant).trans
      (by exact_mod_cast hq)
  filter_upwards
      [AnnularRecursiveProfileRow.eventually_profileRefinementTreeKernel_row_le,
       eventually_ge_atTop 10000,
       AppendixPairMoment.eventually_geometricCutoff_le_decorrelationPadding,
       AppendixPairMoment.eventually_decorrelationPadding_lt,
       hconstant]
      with q htree hq hpaddingLower hpaddingUpper hconstantQ
  intro l hl delta m hm hdelta a rest hvalues center segments
  let start := pairPrefixScale q l
  have hpadding : decorrelationPadding q ≤ q := hpaddingUpper.le
  have hpadPos : 2 ≤ decorrelationPadding q :=
    (show 2 ≤ 32 by omega).trans
      (GaussianGeometricCutoff.geometricCutoff_ge_thirty_two.trans
        hpaddingLower)
  have hstart : 2 ≤ start := by
    have hpref : start = l + decorrelationPadding q :=
      pairPrefixScale_eq_of_add_le
        (Nat.add_le_of_le_sub hpadding hl)
    omega
  have hstartq : start ≤ q := by
    have hpref : start = l + decorrelationPadding q :=
      pairPrefixScale_eq_of_add_le
        (Nat.add_le_of_le_sub hpadding hl)
    rw [hpref]
    exact Nat.add_le_of_le_sub hpadding hl
  have hdepth : start + rest.length ≤ q := by
    have hlength : (a :: rest).length = q + 1 - start := by
      rw [← hvalues, profileSegmentValues_length]
    simp only [List.length_cons] at hlength
    omega
  have ha : a ≤ 3 * q ^ 2 :=
    profileSegmentValues_head_le_three_mul_sq
      hstart hstartq hm hdelta hvalues
  have hchain (chain : GapChain (a :: rest)) :
      heterogeneousPreludeMultiRenewalKernel
          (paddedPreludeEntryKernelENNReal q l start center)
          (paddedPreludeDirectKernelENNReal q l start center)
          (paddedInwardKernelENNReal q l start center)
          (recursiveProfileGapKernelENNReal q start center)
          (paddedEscapeKernelENNReal q l start center)
          segments (List.ofFn fun i : Fin a ↦
            profileRefinementTrees a rest chain i) ≤
        ENNReal.ofReal
            ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain) *
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
            (segments.map fun segment ↦ match segment.1 with
              | Sum.inl initial =>
                  paddedNearUnmarkedKernelENNReal q l center initial segment.2
              | Sum.inr u =>
                  paddedUnmarkedKernelENNReal q l start
                    center u segment.2).prod := by
    apply
      profileRefinementChainPaddedPreludeMultiRenewalKernel_le_expHalf_unmarked
        hq hl hpadding hpadPos hconstantQ ha chain center
    intro i z
    exact htree start (by omega) a rest hdepth chain i center z
  have hreference := sum_profileRefinementChainReferenceCost_le_expHalf
    (n := q) (start := start) (a := a) (rest := rest)
    (by omega) hstart hstartq hm hdelta hvalues
  calc
    _ ≤ ∑ chain : GapChain (a :: rest),
        ENNReal.ofReal
            ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain) *
          ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
            (segments.map fun segment ↦ match segment.1 with
              | Sum.inl initial =>
                  paddedNearUnmarkedKernelENNReal q l center initial segment.2
              | Sum.inr u =>
                  paddedUnmarkedKernelENNReal q l start
                    center u segment.2).prod := by
          exact Finset.sum_le_sum fun chain _ ↦ hchain chain
    _ = (∑ chain : GapChain (a :: rest),
          ENNReal.ofReal
            ((1 + 1 / (q : ℝ) ^ 6) ^ radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain)) *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          (segments.map fun segment ↦ match segment.1 with
            | Sum.inl initial =>
                paddedNearUnmarkedKernelENNReal q l center initial segment.2
            | Sum.inr u =>
                paddedUnmarkedKernelENNReal q l start
                  center u segment.2).prod := by
            rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ENNReal.ofReal
          (Real.exp (1 / 2 : ℝ) *
            transitionSegmentProduct start (q - start) (profileAtScale m)) *
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          (segments.map fun segment ↦ match segment.1 with
            | Sum.inl initial =>
                paddedNearUnmarkedKernelENNReal q l center initial segment.2
            | Sum.inr u =>
                paddedUnmarkedKernelENNReal q l start
                  center u segment.2).prod := by
            gcongr
    _ = ENNReal.ofReal
          (Real.exp 1 *
            transitionSegmentProduct start (q - start) (profileAtScale m)) *
        (segments.map fun segment ↦ match segment.1 with
          | Sum.inl initial =>
              paddedNearUnmarkedKernelENNReal q l center initial segment.2
          | Sum.inr u =>
              paddedUnmarkedKernelENNReal q l start
                center u segment.2).prod := by
      have hfactor0 : 0 ≤ Real.exp (1 / 2 : ℝ) *
          transitionSegmentProduct start (q - start) (profileAtScale m) :=
        mul_nonneg (Real.exp_nonneg _)
          (transitionSegmentProduct_nonneg _ _ _)
      rw [← ENNReal.ofReal_mul hfactor0]
      congr 2
      calc
        Real.exp (1 / 2 : ℝ) *
              transitionSegmentProduct start (q - start) (profileAtScale m) *
            Real.exp (1 / 2 : ℝ) =
            (Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ)) *
              transitionSegmentProduct start (q - start)
                (profileAtScale m) := by ring
        _ = Real.exp 1 * transitionSegmentProduct start (q - start)
              (profileAtScale m) := by
            rw [← Real.exp_add]
            norm_num

/-- The complete recursively decorated continuation row attached to one full
constrained profile, starting at the padded separation-prefix scale. -/
def paddedRecursiveProfileContinuation
    (q l : ℕ) (center : Point) (m : Profile q)
    (u : PaddedMiddlePoint q (pairPrefixScale q l) center)
    (w : PaddedOuterPoint q l center) : ℝ≥0∞ :=
  let start := pairPrefixScale q l
  let a := profileAtScale m start
  let rest := (profileSegmentValues m start).tail
  ∑ chain : GapChain (a :: rest),
    heterogeneousRenewalKernel
      (paddedInwardKernelENNReal q l start center)
      (recursiveProfileGapKernelENNReal q start center)
      (paddedEscapeKernelENNReal q l start center)
      (List.ofFn fun i : Fin a ↦
        profileRefinementTrees a rest chain i) u w

/-- The recursively decorated continuation row when one full constrained
profile is distributed chronologically among several retained padded remote
segments. -/
def paddedMultiRecursiveProfileContinuation
    (q l : ℕ) (center : Point) (m : Profile q)
    (segments : List
      (PaddedMiddlePoint q (pairPrefixScale q l) center ×
        PaddedOuterPoint q l center)) : ℝ≥0∞ :=
  let start := pairPrefixScale q l
  let a := profileAtScale m start
  let rest := (profileSegmentValues m start).tail
  ∑ chain : GapChain (a :: rest),
    heterogeneousMultiRenewalKernel
      (paddedInwardKernelENNReal q l start center)
      (recursiveProfileGapKernelENNReal q start center)
      (paddedEscapeKernelENNReal q l start center)
      segments (List.ofFn fun i : Fin a ↦
        profileRefinementTrees a rest chain i)

/-- The recursively decorated continuation row for coarse bridges beginning
at level `l + 1`; each bridge may exit directly or enter the padded renewal. -/
def paddedPreludeMultiRecursiveProfileContinuation
    (q l : ℕ) (center : Point) (m : Profile q)
    (segments : List
      ((PaddedNearPoint q l center ⊕
          PaddedMiddlePoint q (pairPrefixScale q l) center) ×
        PaddedOuterPoint q l center)) : ℝ≥0∞ :=
  let start := pairPrefixScale q l
  let a := profileAtScale m start
  let rest := (profileSegmentValues m start).tail
  ∑ chain : GapChain (a :: rest),
    heterogeneousPreludeMultiRenewalKernel
      (paddedPreludeEntryKernelENNReal q l start center)
      (paddedPreludeDirectKernelENNReal q l start center)
      (paddedInwardKernelENNReal q l start center)
      (recursiveProfileGapKernelENNReal q start center)
      (paddedEscapeKernelENNReal q l start center)
      segments (List.ofFn fun i : Fin a ↦
        profileRefinementTrees a rest chain i)

/-- All constrained full-profile continuations of one fixed padded prefix are
bounded by that prefix's exact constrained tail weight times the common
unmarked remote renewal kernel. -/
theorem eventually_sum_fixedPrefix_paddedRecursiveProfileContinuation_le :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      ∀ (delta : ℝ), delta ≤ 1 →
      ∀ (hstart : 2 ≤ pairPrefixScale q l)
        (hstartq : pairPrefixScale q l ≤ q),
      ∀ (pref : Profile (pairPrefixScale q l)) (center : Point)
        (u : PaddedMiddlePoint q (pairPrefixScale q l) center)
        (w : PaddedOuterPoint q l center),
        (∑ m ∈ (constrainedProfiles q delta).filter
          (fun m ↦ profilePrefix
            hstart hstartq m = pref),
          paddedRecursiveProfileContinuation q l center m u w) ≤
            ENNReal.ofReal (Real.exp 1 *
              constrainedProfileTailWeight q (pairPrefixScale q l)
                hstart hstartq pref delta) *
              paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                center u w := by
  filter_upwards
      [eventually_sum_profileRefinementChainPaddedRenewalKernel_le_unmarked,
       AppendixPairMoment.eventually_geometricCutoff_le_decorrelationPadding,
       AppendixPairMoment.eventually_decorrelationPadding_lt]
      with q hprofile hpaddingLower hpaddingUpper
  intro l hl delta hdelta hstart hstartq pref center u w
  have hpadding : decorrelationPadding q ≤ q := hpaddingUpper.le
  have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le (Nat.add_le_of_le_sub hpadding hl)
  apply sum_fixedPrefix_rows_le_coefficient_mul hstart hstartq pref delta
    (Real.exp 1) (Real.exp_nonneg _)
    (paddedUnmarkedKernelENNReal q l (pairPrefixScale q l) center u w)
    (fun m ↦ paddedRecursiveProfileContinuation q l center m u w)
  intro m hm
  have hmConstrained : IsConstrainedProfile delta m :=
    mem_constrainedProfiles.mp (Finset.mem_filter.mp hm).1
  unfold paddedRecursiveProfileContinuation
  exact hprofile l hl delta m hmConstrained hdelta
    (profileAtScale m (pairPrefixScale q l))
    (profileSegmentValues m (pairPrefixScale q l)).tail
    (profileSegmentValues_eq_head_cons_tail hstartq m) center u w

/-- The multi-segment continuation has the same constrained fixed-prefix
tail bound, with the common remote factor equal to the product of the
unmarked segment kernels. -/
theorem eventually_sum_fixedPrefix_paddedMultiRecursiveProfileContinuation_le :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      ∀ (delta : ℝ), delta ≤ 1 →
      ∀ (hstart : 2 ≤ pairPrefixScale q l)
        (hstartq : pairPrefixScale q l ≤ q),
      ∀ (pref : Profile (pairPrefixScale q l)) (center : Point)
        (segments : List
          (PaddedMiddlePoint q (pairPrefixScale q l) center ×
            PaddedOuterPoint q l center)),
        (∑ m ∈ (constrainedProfiles q delta).filter
          (fun m ↦ profilePrefix hstart hstartq m = pref),
          paddedMultiRecursiveProfileContinuation q l center m segments) ≤
            ENNReal.ofReal (Real.exp 1 *
              constrainedProfileTailWeight q (pairPrefixScale q l)
                hstart hstartq pref delta) *
              (segments.map fun segment ↦
                paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                  center segment.1 segment.2).prod := by
  filter_upwards
      [eventually_sum_profileRefinementChainPaddedMultiRenewalKernel_le_unmarked,
       AppendixPairMoment.eventually_geometricCutoff_le_decorrelationPadding,
       AppendixPairMoment.eventually_decorrelationPadding_lt]
      with q hprofile hpaddingLower hpaddingUpper
  intro l hl delta hdelta hstart hstartq pref center segments
  have hpadding : decorrelationPadding q ≤ q := hpaddingUpper.le
  have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le (Nat.add_le_of_le_sub hpadding hl)
  apply sum_fixedPrefix_rows_le_coefficient_mul hstart hstartq pref delta
    (Real.exp 1) (Real.exp_nonneg _)
    ((segments.map fun segment ↦
      paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
        center segment.1 segment.2).prod)
    (fun m ↦ paddedMultiRecursiveProfileContinuation q l center m segments)
  intro m hm
  have hmConstrained : IsConstrainedProfile delta m :=
    mem_constrainedProfiles.mp (Finset.mem_filter.mp hm).1
  unfold paddedMultiRecursiveProfileContinuation
  exact hprofile l hl delta m hmConstrained hdelta
    (profileAtScale m (pairPrefixScale q l))
    (profileSegmentValues m (pairPrefixScale q l)).tail
    (profileSegmentValues_eq_head_cons_tail hstartq m) center segments

/-- Fixed-prefix tail bound for coarse bridges with a preliminary entrance
layer. -/
theorem eventually_sum_fixedPrefix_paddedPreludeMultiRecursiveProfileContinuation_le :
    ∀ᶠ q : ℕ in atTop, ∀ l ≤ decorrelationCutoff q,
      ∀ (delta : ℝ), delta ≤ 1 →
      ∀ (hstart : 2 ≤ pairPrefixScale q l)
        (hstartq : pairPrefixScale q l ≤ q),
      ∀ (pref : Profile (pairPrefixScale q l)) (center : Point)
        (segments : List
          ((PaddedNearPoint q l center ⊕
              PaddedMiddlePoint q (pairPrefixScale q l) center) ×
            PaddedOuterPoint q l center)),
        (∑ m ∈ (constrainedProfiles q delta).filter
          (fun m ↦ profilePrefix hstart hstartq m = pref),
          paddedPreludeMultiRecursiveProfileContinuation
            q l center m segments) ≤
          ENNReal.ofReal (Real.exp 1 *
            constrainedProfileTailWeight q (pairPrefixScale q l)
              hstart hstartq pref delta) *
            (segments.map fun segment ↦ match segment.1 with
              | Sum.inl initial =>
                  paddedNearUnmarkedKernelENNReal q l center initial segment.2
              | Sum.inr u =>
                  paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
                    center u segment.2).prod := by
  filter_upwards
      [eventually_sum_profileRefinementChainPaddedPreludeMultiRenewalKernel_le_unmarked,
       AppendixPairMoment.eventually_geometricCutoff_le_decorrelationPadding,
       AppendixPairMoment.eventually_decorrelationPadding_lt]
      with q hprofile hpaddingLower hpaddingUpper
  intro l hl delta hdelta hstart hstartq pref center segments
  have hpadding : decorrelationPadding q ≤ q := hpaddingUpper.le
  have hpref : pairPrefixScale q l = l + decorrelationPadding q :=
    pairPrefixScale_eq_of_add_le (Nat.add_le_of_le_sub hpadding hl)
  apply sum_fixedPrefix_rows_le_coefficient_mul hstart hstartq pref delta
    (Real.exp 1) (Real.exp_nonneg _)
    ((segments.map fun segment ↦ match segment.1 with
      | Sum.inl initial =>
          paddedNearUnmarkedKernelENNReal q l center initial segment.2
      | Sum.inr u =>
          paddedUnmarkedKernelENNReal q l (pairPrefixScale q l)
            center u segment.2).prod)
    (fun m ↦ paddedPreludeMultiRecursiveProfileContinuation
      q l center m segments)
  intro m hm
  have hmConstrained : IsConstrainedProfile delta m :=
    mem_constrainedProfiles.mp (Finset.mem_filter.mp hm).1
  unfold paddedPreludeMultiRecursiveProfileContinuation
  exact hprofile l hl delta m hmConstrained hdelta
    (profileAtScale m (pairPrefixScale q l))
    (profileSegmentValues m (pairPrefixScale q l)).tail
    (profileSegmentValues_eq_head_cons_tail hstartq m) center segments

/-- At selected scales, the canonical `expOne` radial certificate absorbs all
constrained full profiles extending one retained padded prefix, without
integrating out the common remote endpoint kernel. -/
theorem eventually_sum_fixedPrefix_paddedRecursiveProfileContinuation_le_radialTail
    {delta : ℝ} :
    ∀ᶠ blockIndex : ℕ in atTop, ∀ (center x y : Point)
      (hlevel : separationLevel (scaleIndex delta blockIndex) x y ≤
        decorrelationCutoff (scaleIndex delta blockIndex))
      (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
        pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y)),
      ∀ (pref : Profile (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y)))
        (u : PaddedMiddlePoint (scaleIndex delta blockIndex)
          (pairPrefixScale (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y)) center)
        (w : PaddedOuterPoint (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y) center),
        (∑ m ∈ (constrainedProfiles (scaleIndex delta blockIndex)
            profileUpperDelta).filter (fun m ↦
              profilePrefix
                ((show 2 ≤ profileUpperTailStart by
                    norm_num [profileUpperTailStart]).trans
                  (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
                (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale
                m = pref),
          paddedRecursiveProfileContinuation
            (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y)
            center m u w) ≤
          ENNReal.ofReal
              (ProfileRadialTailCertificate.expOne hcutoff).radialTail *
            paddedUnmarkedKernelENNReal (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y)
              (pairPrefixScale (scaleIndex delta blockIndex)
                (separationLevel (scaleIndex delta blockIndex) x y))
              center u w := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hrows := hscaleNat.eventually
    eventually_sum_fixedPrefix_paddedRecursiveProfileContinuation_le
  filter_upwards [hrows] with blockIndex hrow
  intro center x y hlevel hcutoff pref u w
  let q := scaleIndex delta blockIndex
  let l := separationLevel q x y
  let start := pairPrefixScale q l
  let certificate : ProfileRadialTailCertificate delta blockIndex x y :=
    ProfileRadialTailCertificate.expOne hcutoff
  let hstart : 2 ≤ start :=
    (show 2 ≤ profileUpperTailStart by
      norm_num [profileUpperTailStart]).trans certificate.tailStart
  have hsum := hrow l hlevel profileUpperDelta
    (by norm_num [profileUpperDelta]) hstart certificate.start_le_scale
    pref center u w
  calc
    _ ≤ ENNReal.ofReal (Real.exp 1 *
          constrainedProfileTailWeight q start hstart
            certificate.start_le_scale pref profileUpperDelta) *
        paddedUnmarkedKernelENNReal q l start center u w := by
      simpa only [q, l, start, certificate] using hsum
    _ ≤ ENNReal.ofReal certificate.radialTail *
        paddedUnmarkedKernelENNReal q l start center u w := by
      gcongr
      simpa only [certificate, ProfileRadialTailCertificate.expOne,
        ProfileRadialTailCertificate.of_geometricCutoff] using
          certificate.coefficient_mul_constrainedTail_le pref
    _ = ENNReal.ofReal
          (ProfileRadialTailCertificate.expOne hcutoff).radialTail *
        paddedUnmarkedKernelENNReal (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y)
          (pairPrefixScale (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y))
          center u w := by
      rfl

/-- Selected-scale radial-tail certificate for the multi-segment padded
continuation. -/
theorem eventually_sum_fixedPrefix_paddedMultiRecursiveProfileContinuation_le_radialTail
    {delta : ℝ} :
    ∀ᶠ blockIndex : ℕ in atTop, ∀ (center x y : Point)
      (_hlevel : separationLevel (scaleIndex delta blockIndex) x y ≤
        decorrelationCutoff (scaleIndex delta blockIndex))
      (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
        pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y)),
      ∀ (pref : Profile (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y)))
        (segments : List
          (PaddedMiddlePoint (scaleIndex delta blockIndex)
              (pairPrefixScale (scaleIndex delta blockIndex)
                (separationLevel (scaleIndex delta blockIndex) x y)) center ×
            PaddedOuterPoint (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y) center)),
        (∑ m ∈ (constrainedProfiles (scaleIndex delta blockIndex)
            profileUpperDelta).filter (fun m ↦
              profilePrefix
                ((show 2 ≤ profileUpperTailStart by
                    norm_num [profileUpperTailStart]).trans
                  (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
                (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale
                m = pref),
          paddedMultiRecursiveProfileContinuation
            (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y)
            center m segments) ≤
          ENNReal.ofReal
              (ProfileRadialTailCertificate.expOne hcutoff).radialTail *
            (segments.map fun segment ↦
              paddedUnmarkedKernelENNReal (scaleIndex delta blockIndex)
                (separationLevel (scaleIndex delta blockIndex) x y)
                (pairPrefixScale (scaleIndex delta blockIndex)
                  (separationLevel (scaleIndex delta blockIndex) x y))
                center segment.1 segment.2).prod := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hrows := hscaleNat.eventually
    eventually_sum_fixedPrefix_paddedMultiRecursiveProfileContinuation_le
  filter_upwards [hrows] with blockIndex hrow
  intro center x y hlevel hcutoff pref segments
  let q := scaleIndex delta blockIndex
  let l := separationLevel q x y
  let start := pairPrefixScale q l
  let certificate : ProfileRadialTailCertificate delta blockIndex x y :=
    ProfileRadialTailCertificate.expOne hcutoff
  have hsum := hrow l hlevel profileUpperDelta
    (by norm_num [profileUpperDelta])
    ((show 2 ≤ profileUpperTailStart by
        norm_num [profileUpperTailStart]).trans
      (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
    (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale
    pref center segments
  calc
    _ ≤ ENNReal.ofReal (Real.exp 1 *
          constrainedProfileTailWeight q start
            ((show 2 ≤ profileUpperTailStart by
                norm_num [profileUpperTailStart]).trans
              (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
            (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale
            pref profileUpperDelta) *
        (segments.map fun segment ↦
          paddedUnmarkedKernelENNReal q l start
            center segment.1 segment.2).prod := by
      simpa only [q, l, start, certificate] using hsum
    _ ≤ ENNReal.ofReal certificate.radialTail *
        (segments.map fun segment ↦
          paddedUnmarkedKernelENNReal q l start
            center segment.1 segment.2).prod := by
      gcongr
      simpa only [certificate, ProfileRadialTailCertificate.expOne,
        ProfileRadialTailCertificate.of_geometricCutoff] using
          certificate.coefficient_mul_constrainedTail_le pref
    _ = ENNReal.ofReal
          (ProfileRadialTailCertificate.expOne hcutoff).radialTail *
        (segments.map fun segment ↦
          paddedUnmarkedKernelENNReal (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y)
            (pairPrefixScale (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y))
            center segment.1 segment.2).prod := by
      rfl

/-- Selected-scale radial certificate for preliminary-entrance coarse
bridges.  The final factor is the product of their original unmarked
level-`l` kernels. -/
theorem eventually_sum_fixedPrefix_paddedPreludeMultiRecursiveProfileContinuation_le_radialTail
    {delta : ℝ} :
    ∀ᶠ blockIndex : ℕ in atTop, ∀ (center x y : Point)
      (hlevel : separationLevel (scaleIndex delta blockIndex) x y ≤
        decorrelationCutoff (scaleIndex delta blockIndex))
      (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
        pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y)),
      ∀ (pref : Profile (pairPrefixScale (scaleIndex delta blockIndex)
          (separationLevel (scaleIndex delta blockIndex) x y)))
        (segments : List
          ((PaddedNearPoint (scaleIndex delta blockIndex)
                (separationLevel (scaleIndex delta blockIndex) x y) center ⊕
              PaddedMiddlePoint (scaleIndex delta blockIndex)
                (pairPrefixScale (scaleIndex delta blockIndex)
                  (separationLevel (scaleIndex delta blockIndex) x y)) center) ×
            PaddedOuterPoint (scaleIndex delta blockIndex)
              (separationLevel (scaleIndex delta blockIndex) x y) center)),
        (∑ m ∈ (constrainedProfiles (scaleIndex delta blockIndex)
            profileUpperDelta).filter (fun m ↦
              profilePrefix
                ((show 2 ≤ profileUpperTailStart by
                    norm_num [profileUpperTailStart]).trans
                  (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
                (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale
                m = pref),
          paddedPreludeMultiRecursiveProfileContinuation
            (scaleIndex delta blockIndex)
            (separationLevel (scaleIndex delta blockIndex) x y)
            center m segments) ≤
          ENNReal.ofReal
              (ProfileRadialTailCertificate.expOne hcutoff).radialTail *
            (segments.map fun segment ↦ match segment.1 with
              | Sum.inl initial =>
                  paddedNearUnmarkedKernelENNReal
                    (scaleIndex delta blockIndex)
                    (separationLevel (scaleIndex delta blockIndex) x y)
                    center initial segment.2
              | Sum.inr u =>
                  paddedUnmarkedKernelENNReal (scaleIndex delta blockIndex)
                    (separationLevel (scaleIndex delta blockIndex) x y)
                    (pairPrefixScale (scaleIndex delta blockIndex)
                      (separationLevel (scaleIndex delta blockIndex) x y))
                    center u segment.2).prod := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hrows := hscaleNat.eventually
    eventually_sum_fixedPrefix_paddedPreludeMultiRecursiveProfileContinuation_le
  filter_upwards [hrows] with blockIndex hrow
  intro center x y hlevel hcutoff pref segments
  let q := scaleIndex delta blockIndex
  let l := separationLevel q x y
  let start := pairPrefixScale q l
  let certificate : ProfileRadialTailCertificate delta blockIndex x y :=
    ProfileRadialTailCertificate.expOne hcutoff
  have hsum := hrow l hlevel profileUpperDelta
    (by norm_num [profileUpperDelta])
    ((show 2 ≤ profileUpperTailStart by
        norm_num [profileUpperTailStart]).trans
      (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
    (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale
    pref center segments
  calc
    _ ≤ ENNReal.ofReal (Real.exp 1 *
          constrainedProfileTailWeight q start
            ((show 2 ≤ profileUpperTailStart by
                norm_num [profileUpperTailStart]).trans
              (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
            (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale
            pref profileUpperDelta) *
        (segments.map fun segment ↦ match segment.1 with
          | Sum.inl initial =>
              paddedNearUnmarkedKernelENNReal q l center initial segment.2
          | Sum.inr u =>
                paddedUnmarkedKernelENNReal q l start
                center u segment.2).prod := by
      convert hsum using 1 <;> simp only [q, l, start]
      congr 2
      apply congrArg (fun f => List.map f segments)
      funext segment
      rcases segment with ⟨stage, exit⟩
      cases stage <;> rfl
    _ ≤ ENNReal.ofReal certificate.radialTail *
        (segments.map fun segment ↦ match segment.1 with
          | Sum.inl initial =>
              paddedNearUnmarkedKernelENNReal q l center initial segment.2
          | Sum.inr u =>
              paddedUnmarkedKernelENNReal q l start
                center u segment.2).prod := by
      gcongr
      simpa only [certificate, ProfileRadialTailCertificate.expOne,
        ProfileRadialTailCertificate.of_geometricCutoff] using
          certificate.coefficient_mul_constrainedTail_le pref
    _ = _ := by rfl

end

end Erdos1165.AsymmetricPaddedRecursiveRenewal
