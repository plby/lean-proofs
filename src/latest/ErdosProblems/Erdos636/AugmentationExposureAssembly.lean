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

import ErdosProblems.Erdos636.AugmentationGraphFull
import ErdosProblems.Erdos636.AugmentationGraphFullState
import ErdosProblems.Erdos636.AugmentationGraphPartial
import ErdosProblems.Erdos636.AugmentationSmallNZ

/-!
# Assembly of the two graph exposure stages

This file contains the finite, one-time composition used by the balanced
augmentation argument.  It has three jobs.

* It fixes the deletion-only centre common to the large- and bounded-state
  branches.
* It packages the literal graph equalities and inequalities required by the
  canonical full-exposure theorem, without retaining an abstract probability
  space or abstract event as a hypothesis.
* It combines the `3/4` partial exposure with the conditional `1/3` full
  exposure through the exact nested-slice marginal, giving probability at
  least `1/4` on the final deletion layer.

The large-state theorem selects the collision-thinned switching data inside
each successful intermediate reservoir.  The bounded-state theorem chooses
one state before the intermediate reservoir is exposed and recentres its
one-state window at the same deletion-only centre.
-/

open Classical SimpleGraph

namespace Erdos636
namespace AugmentationExposureAssembly

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## The common deletion-only centre -/

/--
The centre used at one time of the outer switching path.  It contains no
intermediate reservoir and no selected switching state.  The first term is
the edge count of the revealed base graph; the second is the deterministic
contribution of `nZ` matching cells at the prescribed degree centre.
-/
def canonicalAugmentationCenter (G : SimpleGraph V) (W U0 D : Finset V)
    (nZ : ℕ) (wCenter d0 outerCenter : ℝ) : ℝ :=
  (Erdos88.inducedEdges G (W ∪ (U0 \ D)) : ℝ) +
    nZ * (wCenter + d0 - outerCenter / 2)

/-- Diversity threshold produced by the partial exposure. -/
def partialDiversityThreshold (nD : ℕ) (theta divDev : ℝ) : ℝ :=
  ((2 * nD : ℕ) : ℝ) * theta - divDev

/-- Degree centre produced by the partial exposure. -/
def partialDegreeCenter (U0 : Finset V) (nD d0 : ℕ) : ℝ :=
  ((2 * nD : ℕ) : ℝ) / U0.card * d0

/--
The finite hypotheses of the graph partial-exposure theorem.  Keeping them
in one proof-only record makes the two final branch theorems use literally
the same outer event.
-/
structure PartialExposureCertificate
    (G : SimpleGraph V) (U0 : Finset V) (M : Finset (Finset V))
    (K nD s0 d0 : ℕ) (c theta divDev degreeDev tS tX tCollision : ℝ) :
    Prop where
  nD_pos : 0 < nD
  K_pos : 1 ≤ K
  feasible : 2 * nD ≤ U0.card
  families : 2 * s0 ≤ M.card
  cell_card : ∀ x ∈ M, x.card ≤ K
  reservoir_degree : ∀ x ∈ M, degreeInto G U0 x = d0
  diverse : ∀ x ∈ M, ∀ y ∈ M, x ≠ y →
    theta * U0.card ≤ incidenceDiffMass G U0 x y
  c_pos : 0 < c
  c_le_half : c ≤ 1 / 2
  theta_pos : 0 < theta
  selected_balance : c * U0.card ≤ ((2 * nD : ℕ) : ℝ)
  unselected_balance : c * U0.card ≤ ((U0.card - 2 * nD : ℕ) : ℝ)
  divDev_pos : 0 < divDev
  degreeDev_pos : 0 < degreeDev
  tS_pos : 0 < tS
  tX_pos : 0 < tX
  tCollision_pos : 0 < tCollision
  risk_budget :
    let pDiv := AugmentationGraphPartial.outerLinearFailure nD K divDev
    let pDegree := AugmentationGraphPartial.outerLinearFailure nD K degreeDev
    let pCollision :=
      AntiConcentration.variancePointMassConstant
          c (theta ^ 2 / 4) (2 * K) /
        Real.sqrt (U0.card : ℝ)
    s0.choose 2 * pDiv +
        s0 * pDegree / tS +
        s0 * pDegree / tX +
        s0.choose 2 * pCollision / tCollision ≤ 1 / 4

/-- A partial certificate supplies the exact outer `3/4` estimate. -/
theorem PartialExposureCertificate.three_fourths_le_layerProbability
    {G : SimpleGraph V} {U0 : Finset V} {M : Finset (Finset V)}
    {K nD s0 d0 : ℕ} {c theta divDev degreeDev tS tX tCollision : ℝ}
    (H : PartialExposureCertificate G U0 M K nD s0 d0 c theta
      divDev degreeDev tS tX tCollision) :
    (3 / 4 : ℝ) ≤ NestedUniform.layerProbability U0 (2 * nD)
      (AugmentationGraphPartial.PartialGood G M s0
        (partialDiversityThreshold nD theta divDev)
        (partialDegreeCenter U0 nD d0)
        degreeDev tS tX tCollision) := by
  unfold partialDiversityThreshold partialDegreeCenter
  convert
    AugmentationGraphPartial.three_fourths_le_layerProbability_partialGood_thresholds
      G U0 M K nD s0 d0 c theta divDev degreeDev tS tX tCollision
      H.nD_pos H.K_pos H.feasible H.families H.cell_card
      H.reservoir_degree H.diverse H.c_pos H.c_le_half H.theta_pos
      H.selected_balance H.unselected_balance H.divDev_pos H.degreeDev_pos
      H.tS_pos H.tX_pos H.tCollision_pos H.risk_budget using 1

/-! ## Literal certificate for the large-state exposure -/

/-- State projection with the exact cell-order decidable equality used by
`GraphSelectedSwitchingData`. -/
noncomputable def graphSelectedState
    (G : SimpleGraph V) (D1 : Finset V)
    (source candidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source candidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin (nS + 1)) : Finset (Finset V) :=
  @AugmentationGraphFullState.SelectedSwitchingData.state
    (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    source candidates
    (fun x ↦ ¬AugmentationGraphPartial.DegreeGood
      G D1 x degreeCenter degreeRadius)
    (fun x ↦ (degreeInto G D1 x : ℤ)) nS gap badBudget selected i

lemma graphSelectedState_subset_source
    (G : SimpleGraph V) (D1 : Finset V)
    (source candidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source candidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin (nS + 1)) :
    graphSelectedState G D1 source candidates degreeCenter degreeRadius
      nS gap badBudget selected i ⊆ source := by
  exact @AugmentationGraphFullState.SelectedSwitchingData.state_subset_source
    (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    source candidates
    (fun x ↦ ¬AugmentationGraphPartial.DegreeGood
      G D1 x degreeCenter degreeRadius)
    (fun x ↦ (degreeInto G D1 x : ℤ)) nS gap badBudget selected i

@[simp] lemma card_graphSelectedState
    (G : SimpleGraph V) (D1 : Finset V)
    (source candidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source candidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin (nS + 1)) :
    (graphSelectedState G D1 source candidates degreeCenter degreeRadius
      nS gap badBudget selected i).card = nS := by
  exact @AugmentationGraphFullState.SelectedSwitchingData.card_state
    (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    source candidates
    (fun x ↦ ¬AugmentationGraphPartial.DegreeGood
      G D1 x degreeCenter degreeRadius)
    (fun x ↦ (degreeInto G D1 x : ℤ)) nS gap badBudget selected i

lemma graphSelectedState_disjoint_candidates
    (G : SimpleGraph V) (D1 : Finset V)
    (source candidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source candidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin (nS + 1)) :
    Disjoint
      (graphSelectedState G D1 source candidates degreeCenter degreeRadius
        nS gap badBudget selected i) candidates := by
  exact @AugmentationGraphFullState.SelectedSwitchingData.state_disjoint_candidates
    (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    source candidates
    (fun x ↦ ¬AugmentationGraphPartial.DegreeGood
      G D1 x degreeCenter degreeRadius)
    (fun x ↦ (degreeInto G D1 x : ℤ)) nS gap badBudget selected i

/-- The candidate family after deleting the cells that missed the outer
degree window, with the exact cell-order decidability of the selected data. -/
noncomputable def graphSelectedGoodCandidates
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    Finset (Finset V) :=
  rawCandidates.filter fun x ↦
    AugmentationGraphPartial.DegreeGood G D1 x degreeCenter degreeRadius

lemma graphSelectedGoodCandidates_subset
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected ⊆ rawCandidates := by
  exact Finset.filter_subset _ _

lemma graphSelectedGoodCandidates_good
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    {x : Finset V}
    (hx : x ∈ graphSelectedGoodCandidates G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected) :
    AugmentationGraphPartial.DegreeGood G D1 x degreeCenter degreeRadius := by
  simpa [graphSelectedGoodCandidates,
    AugmentationGraphFullState.SelectedSwitchingData.goodCandidates,
    AugmentationGraphFullState.goodPart] using (Finset.mem_filter.mp hx).2

noncomputable def graphSelectedLowCell
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) : Finset V := by
  let B := @AugmentationGraphFullState.SelectedSwitchingData.blocks
    (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    source rawCandidates
    (fun x ↦ ¬AugmentationGraphPartial.DegreeGood
      G D1 x degreeCenter degreeRadius)
    (fun x ↦ (degreeInto G D1 x : ℤ)) nS gap badBudget selected
  exact ((@AugmentationGraphFullState.EnumeratedBlocks.lowEquiv
    (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    _ _ nS B) i).1

noncomputable def graphSelectedHighCell
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) : Finset V := by
  let B := @AugmentationGraphFullState.SelectedSwitchingData.blocks
    (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    source rawCandidates
    (fun x ↦ ¬AugmentationGraphPartial.DegreeGood
      G D1 x degreeCenter degreeRadius)
    (fun x ↦ (degreeInto G D1 x : ℤ)) nS gap badBudget selected
  exact ((@AugmentationGraphFullState.EnumeratedBlocks.highEquiv
    (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    _ _ nS B) i).1

noncomputable def graphSelectedRestFamily
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) : Finset (Finset V) :=
  @Finset.erase (Finset V)
    AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    (graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected i.castSucc)
    (graphSelectedLowCell G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected i)

/-- The selected one-cell path, oriented from its high-degree endpoint to
its low-degree endpoint. -/
noncomputable def graphSelectedReverseState
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : ℕ) : Finset (Finset V) :=
  if hi : i < nS + 1 then
    graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected (Fin.rev ⟨i, hi⟩)
  else ∅

noncomputable def graphSelectedStepRest
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : ℕ) : Finset V :=
  if hi : i < nS then
    AugmentationGraphFull.cellUnion
      (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected (Fin.rev ⟨i, hi⟩))
  else ∅

noncomputable def graphSelectedStepLow
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : ℕ) : Finset V :=
  if hi : i < nS then
    graphSelectedLowCell G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected (Fin.rev ⟨i, hi⟩)
  else ∅

noncomputable def graphSelectedStepHigh
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : ℕ) : Finset V :=
  if hi : i < nS then
    graphSelectedHighCell G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected (Fin.rev ⟨i, hi⟩)
  else ∅

@[simp] lemma graphSelectedReverseState_apply_fin
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin (nS + 1)) :
    graphSelectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected i =
      graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i.rev := by
  simp [graphSelectedReverseState, i.isLt]

/--
All non-probabilistic data needed to apply the canonical graph full-exposure
theorem.  Every field is a literal finite graph relation or a numerical
inequality.  In particular, this structure contains no abstract exposure
datum, event, probability estimate, or moment estimate.
-/
structure LargeExposureCertificate
    (G : SimpleGraph V) (W U0 D1 : Finset V)
    (M rawCandidates : Finset (Finset V))
    (nD nS tau m K : ℕ) (canonicalCenter : Finset V → ℝ)
    (degreeCenter degreeRadius c theta pathShift geometricThreshold
      degreeThreshold meanRadius
      lam E Q kappa sigma R globalRadius : ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ)
    (source : Finset (Finset V)) (gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) where
  state : ℕ → Finset (Finset V)
  stepRest : ℕ → Finset V
  stepLow : ℕ → Finset V
  stepHigh : ℕ → Finset V
  tau_eq_nS : tau = nS
  state_reverse : ∀ i : Fin (nS + 1), state i =
    graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected i.rev
  half : D1.card = 2 * nD
  nD_pos : 0 < nD
  nS_pos : 0 < nS
  K_pos : 1 ≤ K
  c_pos : 0 < c
  c_le_half : c ≤ 1 / 2
  theta_pos : 0 < theta
  selected_balance : c * D1.card ≤ nD
  unselected_balance : c * D1.card ≤ D1.card - nD
  geometricThreshold_nonneg : 0 ≤ geometricThreshold
  degreeThreshold_nonneg : 0 ≤ degreeThreshold
  meanRadius_nonneg : 0 ≤ meanRadius
  Q_pos : 0 < Q
  kappa_pos : 0 < kappa
  E_pos : 0 < E
  D1_subset : D1 ⊆ U0
  disjoint_W_U0 : Disjoint W U0
  source_subset : source ⊆ M
  rawCandidates_subset : rawCandidates ⊆ M
  pairwiseDisjoint : (M : Set (Finset V)).PairwiseDisjoint id
  away : ∀ x ∈ M, Disjoint x (W ∪ U0)
  cell_card : ∀ x ∈ M, x.card ≤ K
  candidate_diverse :
    ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected,
      ∀ y ∈ graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected, x ≠ y →
    theta * D1.card ≤ incidenceDiffMass G D1 x y
  small_degree_window : 2 * degreeRadius < theta / 2 * D1.card
  step_next : ∀ i < tau,
    AugmentationGraphFull.cellUnion (state (i + 1)) = stepRest i ∪ stepLow i
  step_current : ∀ i < tau,
    AugmentationGraphFull.cellUnion (state i) = stepRest i ∪ stepHigh i
  step_W_rest : ∀ i < tau, Disjoint W (stepRest i)
  step_W_low : ∀ i < tau, Disjoint W (stepLow i)
  step_W_high : ∀ i < tau, Disjoint W (stepHigh i)
  step_U_rest : ∀ i < tau, Disjoint U0 (stepRest i)
  step_U_low : ∀ i < tau, Disjoint U0 (stepLow i)
  step_U_high : ∀ i < tau, Disjoint U0 (stepHigh i)
  step_rest_low : ∀ i < tau, Disjoint (stepRest i) (stepLow i)
  step_rest_high : ∀ i < tau, Disjoint (stepRest i) (stepHigh i)
  step_low_card : ∀ i < tau, (stepLow i).card ≤ K
  step_high_card : ∀ i < tau, (stepHigh i).card ≤ K
  step_mean : ∀ i < tau,
    |(AugmentationGraphFullIdentity.switchOffsetInt G W U0
        (stepRest i) (stepLow i) (stepHigh i) : ℝ) +
      ((degreeInto G D1 (stepHigh i) : ℝ) -
        degreeInto G D1 (stepLow i)) / 2| ≤
      meanRadius * Real.sqrt nD
  mean_rise : lam ≤
    (AugmentationGraphFullIdentity.endpointOffsetInt G W U0
      (AugmentationGraphFull.cellUnion (state 0))
      (AugmentationGraphFull.cellUnion (state tau)) : ℝ) +
    ((degreeInto G D1 (AugmentationGraphFull.cellUnion (state 0)) : ℝ) -
      degreeInto G D1 (AugmentationGraphFull.cellUnion (state tau))) / 2
  literal_window : ∀ omega : AugmentationFull.Sample D1 nD,
    ∀ i ≤ tau,
      ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected,
    ¬ AugmentationGraphFull.degreeDeviationBad G D1 nD degreeThreshold x omega →
      |(Erdos88.inducedEdges G
          (AugmentationGraphFull.exposedBase W U0
            (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
            state i ∪ x) : ℝ) -
        AugmentationGraphFull.translatedLiteralGraphPath G W U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
          state pathShift i| ≤ R
  global_window : ∀ omega : AugmentationFull.Sample D1 nD,
    ∀ i ≤ tau,
      ¬ AugmentationGraphFull.degreeDeviationBad G D1 nD geometricThreshold
          (AugmentationGraphFull.cellUnion (state i)) omega →
      |AugmentationGraphFull.translatedLiteralGraphPath G W U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega) state
            pathShift i -
        canonicalCenter
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)| + R ≤
        globalRadius
  m_pos : 1 ≤ m
  sigma_pos : 0 < sigma
  R_small : 2 * R < sigma
  switching_budget : (m : ℝ) *
      (Q * Real.sqrt
        (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) + sigma) +
        kappa ≤ lam
  collision_budget : E ≤ edgeBudget + 1
  candidate_survivors : badDegree <
    (graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected).card
  piece_bound : piece *
      ((graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected).card + 2 * edgeBudget) ≤
    ((graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected).card - badDegree) ^ 2
  output_bound : L ≤ ((m + 1) - (badGeom + badCollision)) * piece
  risk_budget :
    (tau + 1 : ℕ) *
        AugmentationGraphFull.graphDegreeRisk geometricThreshold nD (K * nS) /
          (badGeom + 1 : ℕ) +
      (tau + 1 : ℕ) *
      ((graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected).card.choose 2 *
            AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
            (badCollision + 1 : ℕ) +
      (graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected).card *
          AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
          (badDegree + 1 : ℕ) +
      (tau *
          (Real.sqrt
            (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) / Q)) /
          kappa ≤ 1 / 6

/-- A literal large-exposure certificate gives the conditional `1/3` bound. -/
theorem LargeExposureCertificate.one_third_le_layerProbability
    {G : SimpleGraph V} {W U0 D1 : Finset V}
    {M rawCandidates : Finset (Finset V)}
    {nD nS tau m K : ℕ} {canonicalCenter : Finset V → ℝ}
    {degreeCenter degreeRadius c theta pathShift geometricThreshold
      degreeThreshold meanRadius
      lam E Q kappa sigma R globalRadius : ℝ}
    {badGeom badCollision badDegree edgeBudget piece L : ℕ}
    {source : Finset (Finset V)} {gap badBudget : ℕ}
    {selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget}
    (H : LargeExposureCertificate G W U0 D1 M rawCandidates
      nD nS tau m K canonicalCenter degreeCenter degreeRadius c theta
      pathShift geometricThreshold degreeThreshold meanRadius lam E Q kappa
      sigma R globalRadius
      badGeom badCollision badDegree edgeBudget piece L
      source gap badBudget selected) :
    (1 / 3 : ℝ) ≤ NestedUniform.layerProbability D1 nD
      (fun D ↦ AugmentationGraphFull.innerWindowGood G W U0 M (nS + 1) L
        (canonicalCenter D) globalRadius D) := by
  let : LinearOrder (Finset V) := AugmentationGraphPartial.cellLinearOrder
  let candidates := graphSelectedGoodCandidates G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected
  have hstate_subset : ∀ i ≤ tau, H.state i ⊆ M := by
    intro i hi
    have htau : tau = nS := H.tau_eq_nS
    have hiN : i < nS + 1 := by omega
    let j : Fin (nS + 1) := ⟨i, hiN⟩
    rw [show H.state i = graphSelectedState G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected j.rev by
      simpa [j] using H.state_reverse j]
    exact (graphSelectedState_subset_source G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected j.rev).trans
      H.source_subset
  have hstate_card : ∀ i ≤ tau, (H.state i).card = nS := by
    intro i hi
    have htau : tau = nS := H.tau_eq_nS
    have hiN : i < nS + 1 := by omega
    let j : Fin (nS + 1) := ⟨i, hiN⟩
    rw [show H.state i = graphSelectedState G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected j.rev by
      simpa [j] using H.state_reverse j]
    exact card_graphSelectedState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected j.rev
  have hstate_away : ∀ i ≤ tau, ∀ x ∈ candidates, x ∉ H.state i := by
    intro i hi x hx hxin
    have htau : tau = nS := H.tau_eq_nS
    have hiN : i < nS + 1 := by omega
    let j : Fin (nS + 1) := ⟨i, hiN⟩
    have hxin' : x ∈ graphSelectedState G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected j.rev := by
      rw [← show H.state i = graphSelectedState G D1 source rawCandidates
          degreeCenter degreeRadius nS gap badBudget selected j.rev by
        simpa [j] using H.state_reverse j]
      exact hxin
    exact Finset.disjoint_left.mp
      (graphSelectedState_disjoint_candidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected j.rev) hxin'
      (graphSelectedGoodCandidates_subset G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected hx)
  have hcandidatesM : candidates ⊆ M :=
    (graphSelectedGoodCandidates_subset G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected).trans
      H.rawCandidates_subset
  have hcandidateGood : ∀ x ∈ candidates,
      AugmentationGraphPartial.DegreeGood G D1 x degreeCenter degreeRadius := by
    intro x hx
    exact graphSelectedGoodCandidates_good G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected hx
  exact AugmentationGraphFull.one_third_le_layerProbability_innerWindowGood_of_graphData
    G W U0 D1 M candidates nD nS tau m K H.state canonicalCenter
    H.stepRest H.stepLow H.stepHigh degreeCenter degreeRadius c theta
    pathShift geometricThreshold degreeThreshold meanRadius lam E Q kappa
    sigma R globalRadius
    badGeom badCollision badDegree edgeBudget piece L H.half H.nD_pos
    H.nS_pos H.K_pos H.c_pos H.c_le_half H.theta_pos H.selected_balance
    H.unselected_balance H.geometricThreshold_nonneg
    H.degreeThreshold_nonneg H.meanRadius_nonneg
    H.Q_pos H.kappa_pos H.E_pos H.D1_subset H.disjoint_W_U0
    hcandidatesM H.pairwiseDisjoint H.away H.cell_card
    hstate_subset hstate_card hstate_away hcandidateGood
    H.candidate_diverse H.small_degree_window H.step_next H.step_current
    H.step_W_rest H.step_W_low H.step_W_high H.step_U_rest H.step_U_low
    H.step_U_high H.step_rest_low H.step_rest_high H.step_low_card
    H.step_high_card H.step_mean H.mean_rise H.literal_window H.global_window
    H.m_pos H.sigma_pos H.R_small H.switching_budget H.collision_budget
    H.candidate_survivors H.piece_bound H.output_bound H.risk_budget

/-! ## Nested large-state assembly -/

/--
Large-state, one-time exposure assembly.  The switching data are selected
inside every successful intermediate reservoir.  The only supplied bridge
is a literal graph certificate for that selected data; no conditional
probability or abstract event is assumed.
-/
theorem one_fourth_le_layerProbability_innerWindowGood_large
    (G : SimpleGraph V) (W U0 : Finset V) (M : Finset (Finset V))
    (K nD nS nZ s0 d0 gap badBudget selectionEdgeBudget m tau : ℕ)
    (c theta divDev degreeDev tS tX tCollision : ℝ)
    (wCenter : ℝ)
    (innerTheta pathShift geometricThreshold degreeThreshold meanRadius lam E
      Q kappa sigma R globalRadius : ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ)
    (P : PartialExposureCertificate G U0 M K nD s0 d0 c theta
      divDev degreeDev tS tX tCollision)
    (hnZ : nS + 1 = nZ)
    (htS : tS ≤ (badBudget : ℝ) + 1)
    (htX : tX ≤ (badBudget : ℝ) + 1)
    (htCollision : tCollision ≤ (selectionEdgeBudget : ℝ) + 1)
    (hTuran :
      (2 * nS + gap + 1) *
          (s0 - badBudget + 2 * selectionEdgeBudget) <
        (s0 - badBudget) ^ 2)
    (hcertificate : ∀ D1 ∈ NestedUniform.layer U0 (2 * nD),
      AugmentationGraphPartial.PartialGood G M s0
        (partialDiversityThreshold nD theta divDev)
        (partialDegreeCenter U0 nD d0)
        degreeDev tS tX tCollision D1 →
      ∀ source candidates : Finset (Finset V),
        source ⊆ M → candidates ⊆ M →
        ∀ T : AugmentationGraphFullState.GraphSelectedSwitchingData
          source candidates G D1 (partialDegreeCenter U0 nD d0)
            degreeDev nS gap badBudget,
          LargeExposureCertificate G W U0 D1 M candidates
            nD nS tau m K
            (fun D ↦ canonicalAugmentationCenter G W U0 D nZ
              wCenter d0 (partialDegreeCenter U0 nD d0))
            (partialDegreeCenter U0 nD d0) degreeDev c innerTheta
            pathShift geometricThreshold degreeThreshold meanRadius lam E Q
            kappa sigma R globalRadius
            badGeom badCollision badDegree edgeBudget piece L
            source gap badBudget T) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability U0 nD
      (fun D ↦ AugmentationGraphFull.innerWindowGood G W U0 M nZ L
        (canonicalAugmentationCenter G W U0 D nZ wCenter d0
          (partialDegreeCenter U0 nD d0)) globalRadius D) := by
  let outerGood := AugmentationGraphPartial.PartialGood G M s0
    (partialDiversityThreshold nD theta divDev)
    (partialDegreeCenter U0 nD d0) degreeDev tS tX tCollision
  let event : Finset V → Prop := fun D ↦
    AugmentationGraphFull.innerWindowGood G W U0 M nZ L
      (canonicalAugmentationCenter G W U0 D nZ wCenter d0
        (partialDegreeCenter U0 nD d0)) globalRadius D
  apply Augmentation.one_fourth_le_layerProbability_of_nested
    U0 nD outerGood event P.feasible
  · exact P.three_fourths_le_layerProbability
  · intro D1 hD1 hpartial
    obtain ⟨source, candidates, hsource, hcandidates, hselected⟩ :=
      AugmentationGraphFullState.exists_selectedSwitchingData_of_partialGood
        G M D1 s0 nS gap badBudget selectionEdgeBudget
        (partialDiversityThreshold nD theta divDev)
        (partialDegreeCenter U0 nD d0) degreeDev tS tX tCollision
        hpartial htS htX htCollision hTuran
    let T := Classical.choice hselected
    have hthird := (hcertificate D1 hD1 hpartial source candidates
      hsource hcandidates T).one_third_le_layerProbability
    simpa only [event, hnZ] using hthird

/-! ## Nested bounded-state assembly -/

/--
Bounded-state, one-time exposure assembly.  A single state is selected from
`M` before the intermediate `2 nD`-set is exposed.  The fixed-state theorem
is then applied on every successful intermediate reservoir and its window is
recentered at `canonicalAugmentationCenter`.  The recentering premise is a
literal inequality on deletion sets, not a probability hypothesis.
-/
theorem one_fourth_le_layerProbability_innerWindowGood_small
    (G : SimpleGraph V) (W U0 : Finset V) (M : Finset (Finset V))
    (k K nD nZ s0 d0 : ℕ)
    (c theta divDev degreeDev tS tX tCollision : ℝ)
    (wCenter wDeviation innerTheta innerDeviation E tDegree L
      globalRadius : ℝ)
    (outerBad edgeBudget badDegree piece : ℕ)
    (P : PartialExposureCertificate G U0 M K nD s0 d0 c theta
      divDev degreeDev tS tX tCollision)
    (hnZ : 1 ≤ nZ) (hstateSize : nZ - 1 ≤ M.card)
    (hWU0 : Disjoint W U0)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (huniform : ∀ x ∈ M, x.card = k) (hk : k ≤ K)
    (haway : ∀ x ∈ M, Disjoint x (W ∪ U0))
    (hWdegree : ∀ x ∈ M,
      |(degreeInto G W x : ℝ) - wCenter| ≤ wDeviation)
    (hdiversityScale :
      innerTheta * ((2 * nD : ℕ) : ℝ) ≤
        partialDiversityThreshold nD theta divDev)
    (hinnerTheta : 0 < innerTheta)
    (hsmall : 2 * degreeDev < innerTheta / 2 * ((2 * nD : ℕ) : ℝ))
    (hinnerDeviation : 0 ≤ innerDeviation)
    (htXBudget : tX ≤ (outerBad : ℝ) + 1)
    (hgoodLower : badDegree < s0 - outerBad - (nZ - 1))
    (hE : 0 < E) (htDegree : 0 < tDegree)
    (hrisk :
      let pCollision := AntiConcentration.variancePointMassConstant
        c (innerTheta ^ 2 / 4) K / Real.sqrt ((2 * nD : ℕ) : ℝ)
      let pDegree :=
        AugmentationSmallNZ.innerLinearFailure nD K innerDeviation
      (s0 : ℝ) ^ 2 * pCollision / E +
          s0 * pDegree / tDegree ≤ 2 / 3)
    (hEbudget : E ≤ (edgeBudget : ℝ) + 1)
    (htDegreeBudget : tDegree ≤ (badDegree : ℝ) + 1)
    (hpiece : piece * (s0 + 2 * edgeBudget) ≤
      (s0 - outerBad - (nZ - 1) - badDegree) ^ 2)
    (hpiecePos : 0 < piece) (hL : L ≤ piece)
    (hrecenter : ∀ state : Finset (Finset V), state ⊆ M →
      state.card = nZ - 1 →
      ∀ D1 ∈ NestedUniform.layer U0 (2 * nD),
        AugmentationGraphPartial.PartialGood G M s0
          (partialDiversityThreshold nD theta divDev)
          (partialDegreeCenter U0 nD d0)
          degreeDev tS tX tCollision D1 →
        ∀ D ∈ NestedUniform.layer D1 nD,
          |AugmentationSmallNZ.fixedStateSmallNZCenter
              G W U0 state wCenter d0 (partialDegreeCenter U0 nD d0) D -
            canonicalAugmentationCenter G W U0 D nZ wCenter d0
              (partialDegreeCenter U0 nD d0)| +
            AugmentationSmallNZ.generalSmallNZRadius K nZ nD D1
              wDeviation innerDeviation degreeDev ≤ globalRadius) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability U0 nD
      (fun D ↦ AugmentationGraphFull.innerWindowGood G W U0 M nZ L
        (canonicalAugmentationCenter G W U0 D nZ wCenter d0
          (partialDegreeCenter U0 nD d0)) globalRadius D) := by
  obtain ⟨state, hstate, hstateCard⟩ :=
    Finset.exists_subset_card_eq hstateSize
  let outerGood := AugmentationGraphPartial.PartialGood G M s0
    (partialDiversityThreshold nD theta divDev)
    (partialDegreeCenter U0 nD d0) degreeDev tS tX tCollision
  let event : Finset V → Prop := fun D ↦
    AugmentationGraphFull.innerWindowGood G W U0 M nZ L
      (canonicalAugmentationCenter G W U0 D nZ wCenter d0
        (partialDegreeCenter U0 nD d0)) globalRadius D
  apply Augmentation.one_fourth_le_layerProbability_of_nested
    U0 nD outerGood event P.feasible
  · exact P.three_fourths_le_layerProbability
  · intro D1 hD1 hpartial
    have hhalf : D1.card = 2 * nD :=
      (NestedUniform.mem_layer.mp hD1).2
    have hD1U0 : D1 ⊆ U0 := (NestedUniform.mem_layer.mp hD1).1
    have hdiversityScale' :
        innerTheta * D1.card ≤ partialDiversityThreshold nD theta divDev := by
      rw [hhalf]
      exact hdiversityScale
    have hsmall' : 2 * degreeDev < innerTheta / 2 * D1.card := by
      rw [hhalf]
      exact hsmall
    have hselected : c * D1.card ≤ (nD : ℝ) := by
      rw [hhalf]
      have hc := P.c_le_half
      push_cast
      nlinarith
    have hunselected : c * D1.card ≤ ((D1.card - nD : ℕ) : ℝ) := by
      have hsub : D1.card - nD = nD := by omega
      rw [hsub]
      exact hselected
    have hrisk' :
        let pCollision := AntiConcentration.variancePointMassConstant
          c (innerTheta ^ 2 / 4) K / Real.sqrt (D1.card : ℝ)
        let pDegree :=
          AugmentationSmallNZ.innerLinearFailure nD K innerDeviation
        (s0 : ℝ) ^ 2 * pCollision / E +
            s0 * pDegree / tDegree ≤ 2 / 3 := by
      rw [hhalf]
      exact hrisk
    have hthird :=
      AugmentationSmallNZ.one_third_le_layerProbability_innerWindowGood_fixedState_of_partialGood
        G W U0 M k K d0 nD nZ s0 state D1
        (partialDiversityThreshold nD theta divDev)
        (partialDegreeCenter U0 nD d0) degreeDev tS tX tCollision
        wCenter wDeviation c innerTheta innerDeviation E tDegree L
        outerBad edgeBudget badDegree piece hpartial P.nD_pos hnZ hhalf
        hD1U0 hWU0 hpair huniform hk haway P.reservoir_degree hWdegree
        hstate hstateCard P.K_pos hdiversityScale' P.c_pos P.c_le_half
        hinnerTheta hsmall' hselected hunselected hinnerDeviation
        htXBudget hgoodLower hE htDegree hrisk' hEbudget htDegreeBudget
        hpiece hpiecePos hL
    have hrecentered :=
      AugmentationGraphFull.layerProbability_innerWindowGood_recenter
        G W U0 D1 M nD nZ L
        (AugmentationSmallNZ.generalSmallNZRadius K nZ nD D1
          wDeviation innerDeviation degreeDev)
        globalRadius (1 / 3 : ℝ)
        (AugmentationSmallNZ.fixedStateSmallNZCenter
          G W U0 state wCenter d0 (partialDegreeCenter U0 nD d0))
        (fun D ↦ canonicalAugmentationCenter G W U0 D nZ wCenter d0
          (partialDegreeCenter U0 nD d0)) hthird
        (fun D hD ↦ hrecenter state hstate hstateCard D1 hD1 hpartial D hD)
    simpa only [event] using hrecentered

end

end AugmentationExposureAssembly
end Erdos636
