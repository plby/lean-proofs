/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.AugmentationExposureAssembly
import ErdosProblems.Erdos636.CrowdedInstantiation

/-!
# Literal window bounds on a selected crowded path

This file discharges the two graph-window fields of
`AugmentationExposureCrowd.CrowdLargeBounds`.  The estimates are deliberately
literal.  In particular, the `K^2 * (nS + 1)` term in the candidate window
contains both the edges induced inside the final candidate cell and its
edges into the other selected cells.
-/

open Classical SimpleGraph

namespace Erdos636
namespace AugmentationExposureWindowBounds

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

open AugmentationExposureAssembly

private lemma degreeInto_cellUnion_eq_sum
    (G : SimpleGraph V) (U : Finset V) (M : Finset (Finset V))
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id) :
    degreeInto G U (AugmentationGraphFull.cellUnion M) =
      ∑ x ∈ M, degreeInto G U x := by
  unfold AugmentationGraphFull.cellUnion degreeInto
  rw [Finset.sum_biUnion hpair]
  simp only [id_eq]

private lemma selectedReverseState_subset_crowd
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (hsource : source ⊆ path.crowd time)
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (j : ℕ) (hj : j ≤ nS) :
    graphSelectedReverseState G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected j ⊆ path.crowd time := by
  have hjlt : j < nS + 1 := by omega
  let i : Fin (nS + 1) := ⟨j, hjlt⟩
  rw [show graphSelectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected j =
      graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i.rev by
    simpa [i] using graphSelectedReverseState_apply_fin G D1 source
      rawCandidates degreeCenter degreeRadius nS gap badBudget selected i]
  exact (graphSelectedState_subset_source G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected i.rev).trans hsource

private lemma card_selectedReverseState
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (j : ℕ) (hj : j ≤ nS) :
    (graphSelectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected j).card = nS := by
  have hjlt : j < nS + 1 := by omega
  let i : Fin (nS + 1) := ⟨j, hjlt⟩
  rw [show graphSelectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected j =
      graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i.rev by
    simpa [i] using graphSelectedReverseState_apply_fin G D1 source
      rawCandidates degreeCenter degreeRadius nS gap badBudget selected i]
  exact card_graphSelectedState G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i.rev

private lemma selectedReverseState_disjoint_goodCandidates
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (j : ℕ) (hj : j ≤ nS) :
    Disjoint
      (graphSelectedReverseState G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected j)
      (graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected) := by
  have hjlt : j < nS + 1 := by omega
  let i : Fin (nS + 1) := ⟨j, hjlt⟩
  rw [show graphSelectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected j =
      graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i.rev by
    simpa [i] using graphSelectedReverseState_apply_fin G D1 source
      rawCandidates degreeCenter degreeRadius nS gap badBudget selected i]
  exact (graphSelectedState_disjoint_candidates G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected i.rev).mono_right
      (graphSelectedGoodCandidates_subset G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected)

private lemma selectedReverseState_degreeGood
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (j : ℕ) (hj : j ≤ nS) {x : Finset V}
    (hx : x ∈ graphSelectedReverseState G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected j) :
    AugmentationGraphPartial.DegreeGood G D1 x degreeCenter degreeRadius := by
  have hjlt : j < nS + 1 := by omega
  let i : Fin (nS + 1) := ⟨j, hjlt⟩
  have hx' : x ∈ graphSelectedState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected i.rev := by
    rw [← graphSelectedReverseState_apply_fin G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected i]
    exact hx
  have hxSelected :=
    @AugmentationGraphFullState.SelectedSwitchingData.state_subset_selected
      (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
      source rawCandidates
      (fun z ↦ ¬AugmentationGraphPartial.DegreeGood G D1 z degreeCenter
        degreeRadius)
      (fun z ↦ (degreeInto G D1 z : ℤ)) nS gap badBudget selected i.rev x hx'
  have hxGood :=
    @AugmentationGraphFullState.SelectedSwitchingData.selected_subset_good
      (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
      source rawCandidates
      (fun z ↦ ¬AugmentationGraphPartial.DegreeGood G D1 z degreeCenter
        degreeRadius)
      (fun z ↦ (degreeInto G D1 z : ℤ)) nS gap badBudget selected x
      hxSelected
  have hxPair : x ∈ source ∧
      AugmentationGraphPartial.DegreeGood G D1 x degreeCenter degreeRadius := by
    simpa [AugmentationGraphFullState.goodPart] using hxGood
  exact hxPair.2

private lemma abs_sum_sub_card_mul_le
    {A : Type*} [DecidableEq A] (M : Finset A) (f : A → ℝ) (c r : ℝ)
    (h : ∀ x ∈ M, |f x - c| ≤ r) :
    |(∑ x ∈ M, f x) - M.card * c| ≤ M.card * r := by
  have heq : (∑ x ∈ M, f x) - M.card * c =
      ∑ x ∈ M, (f x - c) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [heq]
  calc
    |∑ x ∈ M, (f x - c)| ≤ ∑ x ∈ M, |f x - c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ M, r := Finset.sum_le_sum h
    _ = M.card * r := by simp

/-!
The candidate contribution is nonnegative.  Its internal part
`e(x) + e(Z,x)` costs `K^2 (nS+1)`; its two external parts cost at most the
anchor degree plus the crowd width and `d0`.  The half deletion subtracts
edges, so it creates no further cost in this one-sided upper bound.
-/
theorem literal_window_of_crowdedPath
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (htime : time ≤ nW) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (hsource : source ⊆ path.crowd time)
    (hraw : rawCandidates ⊆ path.crowd time)
    (nD nS gap badBudget : ℕ)
    (degreeCenter degreeRadius degreeThreshold R : ℝ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hD1 : D1 ⊆ S.U0)
    (hR : (((K ^ 2 * (nS + 1) +
        degreeInto G (path.W time) (path.anchor time) + degreeWindow +
        S.d0 : ℕ) : ℝ)) ≤ R) :
    ∀ omega : AugmentationFull.Sample D1 nD, ∀ j ≤ nS,
      ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected,
      ¬ AugmentationGraphFull.degreeDeviationBad G D1 nD degreeThreshold x omega →
      |(Erdos88.inducedEdges G
          (AugmentationGraphFull.exposedBase (path.W time) S.U0
            (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected) j ∪ x) : ℝ) -
        AugmentationGraphFull.literalGraphPath G (path.W time) S.U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) j| ≤ R := by
  intro omega j hj x hx _hxDegree
  let state := graphSelectedReverseState G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected j
  let Z := AugmentationGraphFull.cellUnion state
  let D := AugmentationGraphFullIdentity.halfDeletion D1 nD omega
  have hstate : state ⊆ path.crowd time :=
    selectedReverseState_subset_crowd S path time D1 source rawCandidates
      hsource degreeCenter degreeRadius nS gap badBudget selected j hj
  have hstateCard : state.card = nS :=
    card_selectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected j hj
  have hxCrowd : x ∈ path.crowd time :=
    hraw (graphSelectedGoodCandidates_subset G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected hx)
  have hxstate : x ∉ state := by
    intro hxs
    exact Finset.disjoint_left.mp
      (selectedReverseState_disjoint_goodCandidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected j hj) hxs hx
  have hpair : (path.crowd time : Set (Finset V)).PairwiseDisjoint id :=
    path.crowd_pairwiseDisjoint htime
  have hpairState : (state : Set (Finset V)).PairwiseDisjoint id := by
    intro y hy z hz hyz
    exact hpair (hstate hy) (hstate hz) hyz
  have hZcardEq : Z.card = state.card * S.k := by
    exact card_matching_biUnion_eq_mul hpairState
      (fun y hy ↦ path.crowd_uniform htime (hstate hy))
  have hZcard : Z.card ≤ K * nS := by
    rw [hZcardEq, hstateCard]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right nS S.k_le
  have hxK : x.card ≤ K :=
    (path.crowd_uniform htime hxCrowd).le.trans S.k_le
  have hcell : Erdos88.inducedEdges G x + (G.interedges Z x).card ≤
      K ^ 2 * (nS + 1) := by
    apply matchingCellIncrement_le G (by omega : 1 ≤ nS + 1)
    · simpa using hZcard
    · exact hxK
  have hWdegree : degreeInto G (path.W time) x ≤
      degreeInto G (path.W time) (path.anchor time) + degreeWindow := by
    have h := path.crowd_degree_window htime hxCrowd
    rw [abs_le] at h
    omega
  have hUdegree : degreeInto G S.U0 x = S.d0 :=
    path.crowd_degree_U0 htime hxCrowd
  have hDU : D ⊆ S.U0 :=
    (AugmentationGraphFullIdentity.halfDeletion_subset D1 nD omega).trans hD1
  have hWZ : Disjoint (path.W time) Z :=
    (AugmentationGraphFull.cellUnion_disjoint_right_of_away hstate
      (fun y hy ↦ path.crowd_away_W htime hy)).symm
  have hUZ : Disjoint S.U0 Z :=
    (AugmentationGraphFull.cellUnion_disjoint_right_of_away hstate
      (fun y hy ↦ path.crowd_away_U0 htime hy)).symm
  have hZx : Disjoint Z x :=
    AugmentationGraphFull.cellUnion_disjoint_cell_of_pairwise
      hpair hstate hxCrowd hxstate
  have hWx : Disjoint (path.W time) x :=
    (path.crowd_away_W htime hxCrowd).symm
  have hUx : Disjoint S.U0 x :=
    (path.crowd_away_U0 htime hxCrowd).symm
  have hid :=
    AugmentationGraphFullIdentity.literalCandidateExtension_sub_base_int
      G (path.W time) S.U0 D Z x hDU (path.disjoint_W_U0 time)
        hWZ hUZ hWx hUx hZx
  simp only [AugmentationGraphFullIdentity.candidateOffsetInt] at hid
  rw [AugmentationGraphFullIdentity.card_interedges_eq_degreeInto,
    hUdegree] at hid
  have hidReal := congrArg (fun z : ℤ ↦ (z : ℝ)) hid
  push_cast at hidReal
  have hnonneg : 0 ≤
      (Erdos88.inducedEdges G
          (AugmentationGraphFull.exposedBase (path.W time) S.U0 D
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected) j ∪ x) : ℝ) -
        AugmentationGraphFull.literalGraphPath G (path.W time) S.U0 D
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) j := by
    have hn := Augmentation.inducedEdges_mono G
      (Finset.subset_union_left :
        AugmentationGraphFull.exposedBase (path.W time) S.U0 D
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) j ⊆
          AugmentationGraphFull.exposedBase (path.W time) S.U0 D
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected) j ∪ x)
    rw [sub_nonneg]
    simpa [AugmentationGraphFull.literalGraphPath,
      AugmentationGraphFullIdentity.literalPath,
      AugmentationGraphFullIdentity.literalPathNat,
      AugmentationGraphFullIdentity.literalState,
      AugmentationGraphFullIdentity.deletionBase,
      AugmentationGraphFull.exposedBase] using (show
        (Erdos88.inducedEdges G
          (AugmentationGraphFull.exposedBase (path.W time) S.U0 D
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected) j) : ℝ) ≤
          Erdos88.inducedEdges G
            (AugmentationGraphFull.exposedBase (path.W time) S.U0 D
              (graphSelectedReverseState G D1 source rawCandidates degreeCenter
                degreeRadius nS gap badBudget selected) j ∪ x) by
          exact_mod_cast hn)
  rw [abs_of_nonneg hnonneg]
  have hDnonneg : (0 : ℝ) ≤ degreeInto G D x := by positivity
  have hcellReal :
      (Erdos88.inducedEdges G x : ℝ) + (G.interedges Z x).card ≤
        (K ^ 2 * (nS + 1) : ℕ) := by exact_mod_cast hcell
  have hWdegreeReal : (degreeInto G (path.W time) x : ℝ) ≤
      degreeInto G (path.W time) (path.anchor time) + degreeWindow := by
    exact_mod_cast hWdegree
  push_cast at hR hcellReal
  simp only [AugmentationGraphFull.exposedBase,
    AugmentationGraphFull.literalGraphPath,
    AugmentationGraphFullIdentity.literalPath,
    AugmentationGraphFullIdentity.literalPathNat,
    AugmentationGraphFullIdentity.literalState,
    AugmentationGraphFullIdentity.deletionBase, state, Z, D] at hidReal ⊢
  linarith

/-! ## Sharp translated windows -/

/-- The path translated by the common contribution of one crowd cell.
Translation does not change any switching increment or endpoint difference,
but it makes the candidate window genuinely small. -/
def translatedLiteralGraphPath (G : SimpleGraph V) (W U0 D : Finset V)
    (state : ℕ → Finset (Finset V)) (i : ℕ)
    (wAnchor d0 degreeCenter : ℝ) : ℝ :=
  AugmentationGraphFull.literalGraphPath G W U0 D state i +
    (wAnchor + d0 - degreeCenter / 2)

/-- The exact sharp candidate window at one selected crowded-path state.
The term `K²(nS+1)` includes both `e(x)` and all edges from `x` into the
other selected cells. -/
theorem centered_literal_window_le
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (htime : time ≤ nW) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (hsource : source ⊆ path.crowd time)
    (hraw : rawCandidates ⊆ path.crowd time)
    (nD nS gap badBudget : ℕ)
    (degreeCenter degreeRadius degreeThreshold : ℝ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hhalf : D1.card = 2 * nD) (hnD : 0 < nD) (hD1 : D1 ⊆ S.U0)
    (omega : AugmentationFull.Sample D1 nD) (j : ℕ) (hj : j ≤ nS)
    (x : Finset V)
    (hx : x ∈ graphSelectedGoodCandidates G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected)
    (hxDegree : ¬ AugmentationGraphFull.degreeDeviationBad G D1 nD
      degreeThreshold x omega) :
    |(Erdos88.inducedEdges G
        (AugmentationGraphFull.exposedBase (path.W time) S.U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) j ∪ x) : ℝ) -
      translatedLiteralGraphPath G (path.W time) S.U0
        (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
        (graphSelectedReverseState G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected) j
        (degreeInto G (path.W time) (path.anchor time)) S.d0 degreeCenter| ≤
      (K ^ 2 * (nS + 1) : ℕ) + degreeWindow + degreeThreshold +
        degreeRadius / 2 := by
  let state := graphSelectedReverseState G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected j
  have hstate : state ⊆ path.crowd time :=
    selectedReverseState_subset_crowd S path time D1 source rawCandidates
      hsource degreeCenter degreeRadius nS gap badBudget selected j hj
  have hstateCard : state.card = nS :=
    card_selectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected j hj
  have hxCrowd : x ∈ path.crowd time :=
    hraw (graphSelectedGoodCandidates_subset G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected hx)
  have hxstate : x ∉ state := by
    intro hxs
    exact Finset.disjoint_left.mp
      (selectedReverseState_disjoint_goodCandidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected j hj) hxs hx
  have hratio : (nD : ℝ) / D1.card = 1 / 2 := by
    rw [hhalf]
    push_cast
    have hnD' : (nD : ℝ) ≠ 0 := by positivity
    field_simp
  let E : Erdos88.Fourier.BoolSlice D1 nD ≃
      AugmentationFull.Sample D1 nD :=
    Erdos88.Fourier.boolSliceEquivFinsetLen D1 nD
  let beta : Erdos88.Fourier.BoolSlice D1 nD := E.symm omega
  have hround : E beta = omega := Equiv.apply_symm_apply E omega
  have hdecode : AugmentationGraphPartial.sampleFinset D1 nD beta =
      AugmentationGraphFullIdentity.halfDeletion D1 nD omega := by
    change AugmentationGraphPartial.mapSubtypeFinset D1 (E beta).1 =
      AugmentationGraphPartial.mapSubtypeFinset D1 omega.1
    rw [hround]
  have hinner : ¬ AugmentationSmallNZ.innerDegreeBad G D1 nD
      degreeThreshold x beta := by
    rw [AugmentationSmallNZ.innerDegreeBad]
    apply not_le_of_gt
    have hxlt :
        |(degreeInto G
            (AugmentationGraphFullIdentity.halfDeletion D1 nD omega) x : ℝ) -
          (degreeInto G D1 x : ℝ) / 2| < degreeThreshold := by
      apply lt_of_not_ge
      exact hxDegree
    rw [hdecode, hratio]
    simpa [div_eq_mul_inv, mul_comm] using hxlt
  have hWdegree :
      |(degreeInto G (path.W time) x : ℝ) -
        degreeInto G (path.W time) (path.anchor time)| ≤ degreeWindow := by
    exact_mod_cast path.crowd_degree_window htime hxCrowd
  have hbase := AugmentationSmallNZ.oneStateValue_mem_generalSmallNZWindow
    G (path.W time) S.U0 D1 (path.crowd time) S.k K nD (nS + 1) S.d0
      state x (degreeInto G (path.W time) (path.anchor time)) degreeWindow
      degreeCenter degreeRadius degreeThreshold (by omega) hD1
      (path.disjoint_W_U0 time) (path.crowd_pairwiseDisjoint htime)
      (fun z hz ↦ path.crowd_uniform htime hz) S.k_le
      (fun z hz ↦ path.crowd_away_W_union_U0 htime hz) hstate
      (by simpa using hstateCard) hxCrowd hxstate
      (path.crowd_degree_U0 htime hxCrowd) hWdegree
      (graphSelectedGoodCandidates_good G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected hx) beta hinner
  convert hbase using 1 <;>
    simp [AugmentationSmallNZ.oneStateValue,
      AugmentationSmallNZ.generalSmallNZCenter,
      AugmentationSmallNZ.generalSmallNZRadius,
      translatedLiteralGraphPath, hratio, state,
      AugmentationGraphFull.exposedBase,
      AugmentationGraphFull.literalGraphPath,
      AugmentationGraphFullIdentity.literalPath,
      AugmentationGraphFullIdentity.literalPathNat,
      AugmentationGraphFullIdentity.literalState,
      AugmentationGraphFullIdentity.deletionBase,
      hdecode] <;> ring

/-- Scalar-radius form of `centered_literal_window_le`, matching the sharp
literal-window field of the full-exposure certificate. -/
theorem centered_literal_window_of_radius
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (htime : time ≤ nW) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (hsource : source ⊆ path.crowd time)
    (hraw : rawCandidates ⊆ path.crowd time)
    (nD nS gap badBudget : ℕ)
    (degreeCenter degreeRadius degreeThreshold R : ℝ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hhalf : D1.card = 2 * nD) (hnD : 0 < nD) (hD1 : D1 ⊆ S.U0)
    (hR : (K ^ 2 * (nS + 1) : ℕ) + degreeWindow + degreeThreshold +
      degreeRadius / 2 ≤ R) :
    ∀ omega : AugmentationFull.Sample D1 nD, ∀ j ≤ nS,
      ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected,
      ¬ AugmentationGraphFull.degreeDeviationBad G D1 nD degreeThreshold
          x omega →
      |(Erdos88.inducedEdges G
          (AugmentationGraphFull.exposedBase (path.W time) S.U0
            (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected) j ∪ x) : ℝ) -
        translatedLiteralGraphPath G (path.W time) S.U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) j
          (degreeInto G (path.W time) (path.anchor time)) S.d0
          degreeCenter| ≤ R := by
  intro omega j hj x hx hxDegree
  exact (centered_literal_window_le S path time htime D1 source rawCandidates
    hsource hraw nD nS gap badBudget degreeCenter degreeRadius degreeThreshold
    selected hhalf hnD hD1 omega j hj x hx hxDegree).trans hR

/-- Sharp global window for the translated path.  The geometric failure is
exactly the half-deletion deviation of the entire selected state.  Outside
that event, the common `wAnchor + d0` contribution cancels completely. -/
theorem centered_global_window_of_crowdedPath
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (htime : time ≤ nW) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (hsource : source ⊆ path.crowd time)
    (nD nS nZ gap badBudget : ℕ)
    (degreeCenter degreeRadius geomThreshold R globalRadius : ℝ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hnZ : nZ = nS + 1) (hD1 : D1 ⊆ S.U0)
    (hglobal : (K * nS : ℕ) ^ 2 + nS * degreeWindow + geomThreshold +
      nS * degreeRadius / 2 + R ≤ globalRadius) :
    ∀ omega : AugmentationFull.Sample D1 nD, ∀ j ≤ nS,
      ¬ AugmentationGraphFull.degreeDeviationBad G D1 nD geomThreshold
        (AugmentationGraphFull.cellUnion
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected j)) omega →
      |translatedLiteralGraphPath G (path.W time) S.U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) j
          (degreeInto G (path.W time) (path.anchor time)) S.d0 degreeCenter -
        canonicalAugmentationCenter G (path.W time) S.U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega) nZ
          (degreeInto G (path.W time) (path.anchor time)) S.d0
          degreeCenter| + R ≤ globalRadius := by
  intro omega j hj hgeomGood
  let state := graphSelectedReverseState G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected j
  let Z := AugmentationGraphFull.cellUnion state
  let D := AugmentationGraphFullIdentity.halfDeletion D1 nD omega
  let W := path.W time
  let wAnchor := degreeInto G W (path.anchor time)
  have hstate : state ⊆ path.crowd time :=
    selectedReverseState_subset_crowd S path time D1 source rawCandidates
      hsource degreeCenter degreeRadius nS gap badBudget selected j hj
  have hstateCard : state.card = nS :=
    card_selectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected j hj
  have hpair : (path.crowd time : Set (Finset V)).PairwiseDisjoint id :=
    path.crowd_pairwiseDisjoint htime
  have hpairState : (state : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hpair (hstate hx) (hstate hy) hxy
  have hZcardEq : Z.card = state.card * S.k :=
    card_matching_biUnion_eq_mul hpairState
      (fun x hx ↦ path.crowd_uniform htime (hstate hx))
  have hZcard : Z.card ≤ K * nS := by
    rw [hZcardEq, hstateCard]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right nS S.k_le
  have hZedges : (Erdos88.inducedEdges G Z : ℝ) ≤ (K * nS : ℕ) ^ 2 := by
    exact_mod_cast (inducedEdges_le_card_sq G Z).trans
      (Nat.pow_le_pow_left hZcard 2)
  have hWdev : |(degreeInto G W Z : ℝ) - nS * wAnchor| ≤
      nS * degreeWindow := by
    rw [degreeInto_cellUnion_eq_sum G W state hpairState]
    push_cast
    simpa [hstateCard] using abs_sum_sub_card_mul_le state
      (fun x ↦ (degreeInto G W x : ℝ)) wAnchor degreeWindow (by
        intro x hx
        exact_mod_cast path.crowd_degree_window htime (hstate hx))
  have hUeq : degreeInto G S.U0 Z = nS * S.d0 := by
    rw [degreeInto_cellUnion_eq_sum G S.U0 state hpairState]
    calc
      (∑ x ∈ state, degreeInto G S.U0 x) = ∑ _x ∈ state, S.d0 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact path.crowd_degree_U0 htime (hstate hx)
      _ = state.card * S.d0 := by simp
      _ = nS * S.d0 := by rw [hstateCard]
  have hD1dev : |(degreeInto G D1 Z : ℝ) - nS * degreeCenter| ≤
      nS * degreeRadius := by
    rw [degreeInto_cellUnion_eq_sum G D1 state hpairState]
    push_cast
    simpa [hstateCard] using abs_sum_sub_card_mul_le state
      (fun x ↦ (degreeInto G D1 x : ℝ)) degreeCenter degreeRadius (by
        intro x hx
        exact selectedReverseState_degreeGood G D1 source rawCandidates
          degreeCenter degreeRadius nS gap badBudget selected j hj hx)
  have hgeomDev : |(degreeInto G D Z : ℝ) -
      (degreeInto G D1 Z : ℝ) / 2| ≤ geomThreshold := by
    have hlt := lt_of_not_ge hgeomGood
    exact hlt.le
  have hDdev : |(nS : ℝ) * degreeCenter / 2 - degreeInto G D Z| ≤
      (nS : ℝ) * degreeRadius / 2 + geomThreshold := by
    calc
      |(nS : ℝ) * degreeCenter / 2 - degreeInto G D Z| =
          |((nS : ℝ) * degreeCenter - degreeInto G D1 Z) / 2 +
            ((degreeInto G D1 Z : ℝ) / 2 - degreeInto G D Z)| := by ring_nf
      _ ≤ |((nS : ℝ) * degreeCenter - degreeInto G D1 Z) / 2| +
          |(degreeInto G D1 Z : ℝ) / 2 - degreeInto G D Z| := abs_add_le _ _
      _ = |(degreeInto G D1 Z : ℝ) - (nS : ℝ) * degreeCenter| / 2 +
          |(degreeInto G D Z : ℝ) - degreeInto G D1 Z / 2| := by
        rw [abs_div]
        norm_num
        rw [abs_sub_comm ((nS : ℝ) * degreeCenter),
          abs_sub_comm ((degreeInto G D1 Z : ℝ) / 2)]
      _ ≤ (nS : ℝ) * degreeRadius / 2 + geomThreshold :=
        add_le_add (div_le_div_of_nonneg_right hD1dev (by norm_num)) hgeomDev
  have hDU : D ⊆ S.U0 :=
    (AugmentationGraphFullIdentity.halfDeletion_subset D1 nD omega).trans hD1
  have hWZ : Disjoint W Z :=
    (AugmentationGraphFull.cellUnion_disjoint_right_of_away hstate
      (fun x hx ↦ path.crowd_away_W htime hx)).symm
  have hUZ : Disjoint S.U0 Z :=
    (AugmentationGraphFull.cellUnion_disjoint_right_of_away hstate
      (fun x hx ↦ path.crowd_away_U0 htime hx)).symm
  have hid :=
    AugmentationGraphFullIdentity.literalCandidateExtension_sub_base_int
      G W S.U0 D ∅ Z hDU (path.disjoint_W_U0 time)
        (by simp) (by simp) hWZ hUZ (by simp)
  simp only [AugmentationGraphFullIdentity.candidateOffsetInt,
    Erdos88.inducedEdges_empty, SimpleGraph.interedges_empty_left,
    Finset.card_empty, Nat.cast_zero, zero_add] at hid
  rw [AugmentationGraphFullIdentity.card_interedges_eq_degreeInto, hUeq] at hid
  have hidReal := congrArg (fun z : ℤ ↦ (z : ℝ)) hid
  push_cast at hidReal
  have hidentity :
      translatedLiteralGraphPath G W S.U0 D
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) j wAnchor S.d0
          degreeCenter -
        canonicalAugmentationCenter G W S.U0 D nZ wAnchor S.d0
          degreeCenter =
      (Erdos88.inducedEdges G Z : ℝ) +
        ((degreeInto G W Z : ℝ) - nS * wAnchor) +
        ((nS : ℝ) * degreeCenter / 2 - degreeInto G D Z) := by
    simp only [translatedLiteralGraphPath,
      AugmentationGraphFull.literalGraphPath,
      AugmentationGraphFullIdentity.literalPath,
      AugmentationGraphFullIdentity.literalPathNat,
      AugmentationGraphFullIdentity.literalState,
      AugmentationGraphFullIdentity.deletionBase,
      canonicalAugmentationCenter, state, Z, W, D, wAnchor,
      Finset.union_empty] at hidReal ⊢
    rw [hnZ]
    push_cast
    ring_nf at hidReal ⊢
    linarith
  rw [hidentity]
  have hmain :
      |(Erdos88.inducedEdges G Z : ℝ) +
          ((degreeInto G W Z : ℝ) - nS * wAnchor) +
          ((nS : ℝ) * degreeCenter / 2 - degreeInto G D Z)| ≤
        (K * nS : ℕ) ^ 2 + nS * degreeWindow +
          nS * degreeRadius / 2 + geomThreshold := by
    calc
      |(Erdos88.inducedEdges G Z : ℝ) +
          ((degreeInto G W Z : ℝ) - nS * wAnchor) +
          ((nS : ℝ) * degreeCenter / 2 - degreeInto G D Z)| ≤
        |(Erdos88.inducedEdges G Z : ℝ)| +
          |(degreeInto G W Z : ℝ) - nS * wAnchor| +
          |(nS : ℝ) * degreeCenter / 2 - degreeInto G D Z| := by
        calc
          _ ≤ |(Erdos88.inducedEdges G Z : ℝ) +
              ((degreeInto G W Z : ℝ) - nS * wAnchor)| +
              |(nS : ℝ) * degreeCenter / 2 - degreeInto G D Z| :=
            abs_add_le _ _
          _ ≤ _ := by
            gcongr
            exact abs_add_le _ _
      _ = (Erdos88.inducedEdges G Z : ℝ) +
          |(degreeInto G W Z : ℝ) - nS * wAnchor| +
          |(nS : ℝ) * degreeCenter / 2 - degreeInto G D Z| := by
        rw [abs_of_nonneg (by positivity)]
      _ ≤ (K * nS : ℕ) ^ 2 + nS * degreeWindow +
          ((nS : ℝ) * degreeRadius / 2 + geomThreshold) := by
        exact add_le_add (add_le_add hZedges hWdev) hDdev
      _ = (K * nS : ℕ) ^ 2 + nS * degreeWindow +
          nS * degreeRadius / 2 + geomThreshold := by ring
  linarith

/-- The selected-state geometric failure has the same explicit half-slice
tail as one degree statistic, with coefficient bound `K*nS`. -/
theorem uniformProbability_selectedStateGeometricBad_le
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (htime : time ≤ nW) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (hsource : source ⊆ path.crowd time)
    (nD nS gap badBudget : ℕ) (degreeCenter degreeRadius geomThreshold : ℝ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (j : ℕ) (hj : j ≤ nS)
    (hhalf : D1.card = 2 * nD) (hnD : 0 < nD) (hnS : 0 < nS)
    (hgeom : 0 ≤ geomThreshold) :
    Erdos88.Concentration.uniformProbability
        (AugmentationGraphFull.degreeDeviationBad G D1 nD geomThreshold
          (AugmentationGraphFull.cellUnion
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected j))) ≤
      AugmentationGraphFull.graphDegreeRisk geomThreshold nD (K * nS) := by
  let state := graphSelectedReverseState G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected j
  let Z := AugmentationGraphFull.cellUnion state
  have hstate : state ⊆ path.crowd time :=
    selectedReverseState_subset_crowd S path time D1 source rawCandidates
      hsource degreeCenter degreeRadius nS gap badBudget selected j hj
  have hstateCard : state.card = nS :=
    card_selectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected j hj
  have hpair : (path.crowd time : Set (Finset V)).PairwiseDisjoint id :=
    path.crowd_pairwiseDisjoint htime
  have hpairState : (state : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hpair (hstate hx) (hstate hy) hxy
  have hZcardEq : Z.card = state.card * S.k :=
    card_matching_biUnion_eq_mul hpairState
      (fun x hx ↦ path.crowd_uniform htime (hstate hx))
  have hZcard : Z.card ≤ K * nS := by
    rw [hZcardEq, hstateCard]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right nS S.k_le
  have hK : 0 < K := S.k_pos.trans S.k_le
  simpa [state, Z, AugmentationGraphFull.graphDegreeRisk] using
    AugmentationGraphFull.uniformProbability_degreeDeviationBad_le
      G D1 Z nD (K * nS) geomThreshold hhalf hnD
        (Nat.mul_pos hK hnS) hgeom hZcard

end

end AugmentationExposureWindowBounds
end Erdos636
