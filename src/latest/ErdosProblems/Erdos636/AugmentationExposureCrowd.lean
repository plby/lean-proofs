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
# Selected-path geometry on one structural crowd

This module constructs the literal high-to-low path used by
`AugmentationExposureAssembly.LargeExposureCertificate`.  It is separated
from the already-green probability assembly so intermediate proof work here
cannot invalidate that import boundary.
-/

open Classical SimpleGraph

namespace Erdos636
namespace AugmentationExposureCrowd

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

open AugmentationExposureAssembly

local instance cellDecidableEq : DecidableEq (Finset V) :=
  AugmentationGraphPartial.cellLinearOrder.toDecidableEq

lemma graphSelectedState_succ
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i.succ =
      insert
        (graphSelectedHighCell G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i)
        (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i) := by
  have h :=
    (@AugmentationGraphFullState.SelectedSwitchingData.state_succ
      (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
      source rawCandidates
      (fun x ↦ ¬AugmentationGraphPartial.DegreeGood
        G D1 x degreeCenter degreeRadius)
      (fun x ↦ (degreeInto G D1 x : ℤ)) nS gap badBudget selected i)
  unfold graphSelectedState graphSelectedHighCell graphSelectedRestFamily
    graphSelectedLowCell
  convert h using 1 <;> ext x <;> simp [graphSelectedState]

lemma graphSelectedLowCell_mem_castSucc_state
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    graphSelectedLowCell G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i ∈
      graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i.castSucc := by
  let B := @AugmentationGraphFullState.SelectedSwitchingData.blocks
    (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
    source rawCandidates
    (fun x ↦ ¬AugmentationGraphPartial.DegreeGood
      G D1 x degreeCenter degreeRadius)
    (fun x ↦ (degreeInto G D1 x : ℤ)) nS gap badBudget selected
  unfold graphSelectedState graphSelectedLowCell
  change ((@AugmentationGraphFullState.EnumeratedBlocks.lowEquiv
      (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
      _ _ nS B) i).1 ∈
    @AugmentationGraphFullState.EnumeratedBlocks.state
      (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
      _ _ nS B i.castSucc
  unfold AugmentationGraphFullState.EnumeratedBlocks.state
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  simp [AugmentationGraphFullState.EnumeratedBlocks.value]

lemma graphSelectedCastSucc_eq_insert_low_rest
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i.castSucc =
      insert
        (graphSelectedLowCell G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i)
        (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i) := by
  symm
  unfold graphSelectedRestFamily
  convert Finset.insert_erase
    (graphSelectedLowCell_mem_castSucc_state G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected i) using 1 <;>
    ext x <;> simp

lemma graphSelectedReverseState_succ
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : ℕ) (hi : i < nS) :
    graphSelectedReverseState G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected (i + 1) =
      insert
        (graphSelectedStepLow G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i)
        (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected (Fin.rev ⟨i, hi⟩)) := by
  unfold graphSelectedReverseState graphSelectedStepLow
  simp only [hi, Nat.lt_add_one_iff, ↓reduceDIte]
  have hi1 : i + 1 < nS + 1 := by omega
  have hiLe : i + 1 ≤ nS := by omega
  simp only [hiLe, ↓reduceDIte]
  change graphSelectedState G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected
        (Fin.rev (⟨i + 1, hi1⟩ : Fin (nS + 1))) = _
  have hrev : Fin.rev (⟨i + 1, hi1⟩ : Fin (nS + 1)) =
      (Fin.rev ⟨i, hi⟩).castSucc := by
    apply Fin.ext
    simp [Fin.rev]
  rw [hrev]
  simpa using graphSelectedCastSucc_eq_insert_low_rest G D1 source
    rawCandidates degreeCenter degreeRadius nS gap badBudget selected
      (Fin.rev ⟨i, hi⟩)

lemma graphSelectedReverseState_current
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : ℕ) (hi : i < nS) :
    graphSelectedReverseState G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i =
      insert
        (graphSelectedStepHigh G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i)
        (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected (Fin.rev ⟨i, hi⟩)) := by
  unfold graphSelectedReverseState graphSelectedStepHigh
  have hi' : i < nS + 1 := by omega
  simp only [hi, hi', ↓reduceDIte]
  have hrev : Fin.rev ⟨i, hi'⟩ = (Fin.rev ⟨i, hi⟩).succ := by
    apply Fin.ext
    simp [Fin.rev]
    omega
  rw [hrev]
  simpa using graphSelectedState_succ G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected (Fin.rev ⟨i, hi⟩)

lemma graphSelectedReverseState_step_next
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : ℕ) (hi : i < nS) :
    AugmentationGraphFull.cellUnion
        (graphSelectedReverseState G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected (i + 1)) =
      graphSelectedStepRest G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i ∪
        graphSelectedStepLow G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i := by
  rw [graphSelectedReverseState_succ G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i hi]
  unfold graphSelectedStepRest
  simp only [hi, ↓reduceDIte]
  simp [AugmentationGraphFull.cellUnion, Finset.union_comm]

lemma graphSelectedReverseState_step_current
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : ℕ) (hi : i < nS) :
    AugmentationGraphFull.cellUnion
        (graphSelectedReverseState G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i) =
      graphSelectedStepRest G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i ∪
        graphSelectedStepHigh G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i := by
  rw [graphSelectedReverseState_current G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i hi]
  unfold graphSelectedStepRest
  simp only [hi, ↓reduceDIte]
  simp [AugmentationGraphFull.cellUnion, Finset.union_comm]

lemma graphSelectedRestFamily_subset_source
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i ⊆ source := by
  intro x hx
  apply graphSelectedState_subset_source G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected i.castSucc
  exact Finset.mem_of_mem_erase hx

lemma graphSelectedLowCell_mem_source
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    graphSelectedLowCell G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected i ∈ source := by
  exact graphSelectedState_subset_source G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected i.castSucc
      (graphSelectedLowCell_mem_castSucc_state G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected i)

lemma graphSelectedHighCell_mem_source
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    graphSelectedHighCell G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected i ∈ source := by
  apply graphSelectedState_subset_source G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected i.succ
  rw [graphSelectedState_succ G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i]
  simp

lemma graphSelectedState_degreeGood
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin (nS + 1)) {x : Finset V}
    (hx : x ∈ graphSelectedState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected i) :
    AugmentationGraphPartial.DegreeGood G D1 x degreeCenter degreeRadius := by
  have hxSelected :=
    @AugmentationGraphFullState.SelectedSwitchingData.state_subset_selected
      (Finset V) AugmentationGraphPartial.cellLinearOrder.toDecidableEq
      source rawCandidates
      (fun z ↦ ¬AugmentationGraphPartial.DegreeGood G D1 z degreeCenter
        degreeRadius)
      (fun z ↦ (degreeInto G D1 z : ℤ)) nS gap badBudget selected i x hx
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

lemma graphSelectedLowCell_degreeGood
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    AugmentationGraphPartial.DegreeGood G D1
      (graphSelectedLowCell G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i) degreeCenter degreeRadius := by
  exact graphSelectedState_degreeGood G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i.castSucc
      (graphSelectedLowCell_mem_castSucc_state G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected i)

lemma graphSelectedHighCell_degreeGood
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    AugmentationGraphPartial.DegreeGood G D1
      (graphSelectedHighCell G D1 source rawCandidates degreeCenter degreeRadius
        nS gap badBudget selected i) degreeCenter degreeRadius := by
  apply graphSelectedState_degreeGood G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i.succ
  rw [graphSelectedState_succ G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i]
  simp

lemma graphSelectedLowCell_not_mem_rest
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    graphSelectedLowCell G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected i ∉
      graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i := by
  simp [graphSelectedRestFamily]

lemma card_graphSelectedRestFamily
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected i).card + 1 = nS := by
  unfold graphSelectedRestFamily
  rw [Finset.card_erase_of_mem
    (graphSelectedLowCell_mem_castSucc_state G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected i)]
  rw [card_graphSelectedState G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i.castSucc]
  have hnS : 0 < nS := Nat.zero_lt_of_lt i.isLt
  omega

lemma graphSelectedHighCell_not_mem_rest
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (i : Fin nS) :
    graphSelectedHighCell G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected i ∉
      graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i := by
  intro hmem
  have hinsert : insert
      (graphSelectedHighCell G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i)
      (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i) =
      graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i :=
    Finset.insert_eq_self.mpr hmem
  have hcardState := card_graphSelectedState G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected i.succ
  rw [graphSelectedState_succ G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i, hinsert] at hcardState
  have hcardRest := card_graphSelectedRestFamily G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected i
  omega

/-! ## Finite crowd certificate -/

/--
The numerical and literal graph inequalities which are not consequences of
the crowd geometry itself.  The state, its one-cell decomposition, all
disjointness statements, the cell-size bounds, and candidate diversity are
deliberately absent: `largeExposureCertificate_of_crowdedPath` derives those
fields from the structural witness and the crowded path.
-/
structure CrowdLargeBounds
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (nD nS m : ℕ) (canonicalCenter : Finset V → ℝ)
    (degreeCenter degreeRadius c theta pathShift geometricThreshold
      degreeThreshold meanRadius
      lam E qScale kappa sigma R globalRadius : ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ)
    (gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    Prop where
  half : D1.card = 2 * nD
  nD_pos : 0 < nD
  nS_pos : 0 < nS
  c_pos : 0 < c
  c_le_half : c ≤ 1 / 2
  theta_pos : 0 < theta
  selected_balance : c * D1.card ≤ nD
  unselected_balance : c * D1.card ≤ D1.card - nD
  geometricThreshold_nonneg : 0 ≤ geometricThreshold
  degreeThreshold_nonneg : 0 ≤ degreeThreshold
  meanRadius_nonneg : 0 ≤ meanRadius
  qScale_pos : 0 < qScale
  kappa_pos : 0 < kappa
  E_pos : 0 < E
  D1_subset : D1 ⊆ S.U0
  candidate_diverse :
    ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected,
      ∀ y ∈ graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected, x ≠ y →
      theta * D1.card ≤ incidenceDiffMass G D1 x y
  small_degree_window : 2 * degreeRadius < theta / 2 * D1.card
  step_mean : ∀ j < nS,
    |(AugmentationGraphFullIdentity.switchOffsetInt G (path.W time) S.U0
        (graphSelectedStepRest G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected j)
        (graphSelectedStepLow G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected j)
        (graphSelectedStepHigh G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected j) : ℝ) +
      ((degreeInto G D1
          (graphSelectedStepHigh G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected j) : ℝ) -
        degreeInto G D1
          (graphSelectedStepLow G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected j)) / 2| ≤
      meanRadius * Real.sqrt nD
  mean_rise : lam ≤
    (AugmentationGraphFullIdentity.endpointOffsetInt G (path.W time) S.U0
      (AugmentationGraphFull.cellUnion
        (graphSelectedReverseState G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected 0))
      (AugmentationGraphFull.cellUnion
        (graphSelectedReverseState G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected nS)) : ℝ) +
    ((degreeInto G D1
        (AugmentationGraphFull.cellUnion
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected 0)) : ℝ) -
      degreeInto G D1
        (AugmentationGraphFull.cellUnion
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected nS))) / 2
  literal_window : ∀ omega : AugmentationFull.Sample D1 nD,
    ∀ j ≤ nS,
      ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected,
    ¬ AugmentationGraphFull.degreeDeviationBad G D1 nD degreeThreshold x omega →
      |(Erdos88.inducedEdges G
          (AugmentationGraphFull.exposedBase (path.W time) S.U0
            (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected) j ∪ x) : ℝ) -
        AugmentationGraphFull.translatedLiteralGraphPath G (path.W time) S.U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) pathShift j| ≤ R
  global_window : ∀ omega : AugmentationFull.Sample D1 nD,
    ∀ j ≤ nS,
      ¬ AugmentationGraphFull.degreeDeviationBad G D1 nD geometricThreshold
          (AugmentationGraphFull.cellUnion
            (graphSelectedReverseState G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected j)) omega →
      |AugmentationGraphFull.translatedLiteralGraphPath G (path.W time) S.U0
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)
          (graphSelectedReverseState G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected) pathShift j -
        canonicalCenter
          (AugmentationGraphFullIdentity.halfDeletion D1 nD omega)| + R ≤
        globalRadius
  m_pos : 1 ≤ m
  sigma_pos : 0 < sigma
  R_small : 2 * R < sigma
  switching_budget : (m : ℝ) *
      (qScale * Real.sqrt
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
    (nS + 1 : ℕ) *
        AugmentationGraphFull.graphDegreeRisk geometricThreshold nD (K * nS) /
          (badGeom + 1 : ℕ) +
      (nS + 1 : ℕ) *
      ((graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected).card.choose 2 *
          AugmentationGraphFull.graphCollisionRisk c theta K D1 / E) /
          (badCollision + 1 : ℕ) +
      (graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected).card *
          AugmentationGraphFull.graphDegreeRisk degreeThreshold nD K /
          (badDegree + 1 : ℕ) +
      (nS *
          (Real.sqrt
            (AugmentationGraphFull.graphSwitchVariance K meanRadius nD) /
              qScale)) /
          kappa ≤ 1 / 6

/--
At a fixed time of a crowded outer path, the selected degree-sorted blocks
canonically furnish every finite geometry field of the large graph exposure.
Only the explicit inequalities in `CrowdLargeBounds` remain to be checked by
the quantitative parameter layer.
-/
noncomputable def largeExposureCertificate_of_crowdedPath
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (htime : time ≤ nW) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (hsource : source ⊆ path.crowd time)
    (hraw : rawCandidates ⊆ path.crowd time)
    (nD nS m : ℕ) (canonicalCenter : Finset V → ℝ)
    (degreeCenter degreeRadius c theta pathShift geometricThreshold
      degreeThreshold meanRadius
      lam E qScale kappa sigma R globalRadius : ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ)
    (gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (B : CrowdLargeBounds S path time D1 source rawCandidates nD nS m
      canonicalCenter degreeCenter degreeRadius c theta pathShift
      geometricThreshold degreeThreshold meanRadius lam E qScale kappa sigma
      R globalRadius badGeom badCollision badDegree edgeBudget piece L gap
      badBudget selected) :
    LargeExposureCertificate G (path.W time) S.U0 D1 (path.crowd time)
      rawCandidates nD nS nS m K canonicalCenter degreeCenter degreeRadius c
      theta pathShift geometricThreshold degreeThreshold meanRadius lam E
      qScale kappa sigma R globalRadius badGeom badCollision badDegree
      edgeBudget piece L source gap badBudget selected := by
  let state : ℕ → Finset (Finset V) :=
    graphSelectedReverseState G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected
  let stepRest : ℕ → Finset V :=
    graphSelectedStepRest G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected
  let stepLow : ℕ → Finset V :=
    graphSelectedStepLow G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected
  let stepHigh : ℕ → Finset V :=
    graphSelectedStepHigh G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected
  have hpair : (path.crowd time : Set (Finset V)).PairwiseDisjoint id :=
    path.crowd_pairwiseDisjoint htime
  have haway : ∀ x ∈ path.crowd time,
      Disjoint x (path.W time ∪ S.U0) := by
    intro x hx
    exact path.crowd_away_W_union_U0 htime hx
  have hcell : ∀ x ∈ path.crowd time, x.card ≤ K := by
    intro x hx
    rw [path.crowd_uniform htime hx]
    exact S.k_le
  refine {
    state := state
    stepRest := stepRest
    stepLow := stepLow
    stepHigh := stepHigh
    tau_eq_nS := rfl
    state_reverse := ?_
    half := B.half
    nD_pos := B.nD_pos
    nS_pos := B.nS_pos
    K_pos := S.k_pos.trans S.k_le
    c_pos := B.c_pos
    c_le_half := B.c_le_half
    theta_pos := B.theta_pos
    selected_balance := B.selected_balance
    unselected_balance := B.unselected_balance
    geometricThreshold_nonneg := B.geometricThreshold_nonneg
    degreeThreshold_nonneg := B.degreeThreshold_nonneg
    meanRadius_nonneg := B.meanRadius_nonneg
    Q_pos := B.qScale_pos
    kappa_pos := B.kappa_pos
    E_pos := B.E_pos
    D1_subset := B.D1_subset
    disjoint_W_U0 := path.disjoint_W_U0 time
    source_subset := hsource
    rawCandidates_subset := hraw
    pairwiseDisjoint := hpair
    away := haway
    cell_card := hcell
    candidate_diverse := ?_
    small_degree_window := B.small_degree_window
    step_next := ?_
    step_current := ?_
    step_W_rest := ?_
    step_W_low := ?_
    step_W_high := ?_
    step_U_rest := ?_
    step_U_low := ?_
    step_U_high := ?_
    step_rest_low := ?_
    step_rest_high := ?_
    step_low_card := ?_
    step_high_card := ?_
    step_mean := B.step_mean
    mean_rise := B.mean_rise
    literal_window := B.literal_window
    global_window := B.global_window
    m_pos := B.m_pos
    sigma_pos := B.sigma_pos
    R_small := B.R_small
    switching_budget := B.switching_budget
    collision_budget := B.collision_budget
    candidate_survivors := B.candidate_survivors
    piece_bound := B.piece_bound
    output_bound := B.output_bound
    risk_budget := B.risk_budget }
  · intro j
    exact graphSelectedReverseState_apply_fin G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected j
  · exact B.candidate_diverse
  · intro j hj
    exact graphSelectedReverseState_step_next G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected j hj
  · intro j hj
    exact graphSelectedReverseState_step_current G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected j hj
  · intro j hj
    simpa [stepRest, graphSelectedStepRest, hj] using
      (AugmentationGraphFull.cellUnion_disjoint_right_of_away
      ((graphSelectedRestFamily_subset_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)).trans
        hsource) (fun x hx ↦ path.crowd_away_W htime hx)).symm
  · intro j hj
    simpa [stepLow, graphSelectedStepLow, hj] using
      (path.crowd_away_W htime
      (hsource (graphSelectedLowCell_mem_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)))).symm
  · intro j hj
    simpa [stepHigh, graphSelectedStepHigh, hj] using
      (path.crowd_away_W htime
      (hsource (graphSelectedHighCell_mem_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)))).symm
  · intro j hj
    simpa [stepRest, graphSelectedStepRest, hj] using
      (AugmentationGraphFull.cellUnion_disjoint_right_of_away
      ((graphSelectedRestFamily_subset_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)).trans
        hsource) (fun x hx ↦ path.crowd_away_U0 htime hx)).symm
  · intro j hj
    simpa [stepLow, graphSelectedStepLow, hj] using
      (path.crowd_away_U0 htime
      (hsource (graphSelectedLowCell_mem_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)))).symm
  · intro j hj
    simpa [stepHigh, graphSelectedStepHigh, hj] using
      (path.crowd_away_U0 htime
      (hsource (graphSelectedHighCell_mem_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)))).symm
  · intro j hj
    simpa [stepRest, stepLow, graphSelectedStepRest, graphSelectedStepLow, hj] using
      AugmentationGraphFull.cellUnion_disjoint_cell_of_pairwise hpair
      ((graphSelectedRestFamily_subset_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)).trans
        hsource)
      (hsource (graphSelectedLowCell_mem_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)))
      (graphSelectedLowCell_not_mem_rest G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩))
  · intro j hj
    simpa [stepRest, stepHigh, graphSelectedStepRest, graphSelectedStepHigh, hj] using
      AugmentationGraphFull.cellUnion_disjoint_cell_of_pairwise hpair
      ((graphSelectedRestFamily_subset_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)).trans
        hsource)
      (hsource (graphSelectedHighCell_mem_source G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩)))
      (graphSelectedHighCell_not_mem_rest G D1 source rawCandidates
        degreeCenter degreeRadius nS gap badBudget selected (Fin.rev ⟨j, hj⟩))
  · intro j hj
    simpa [stepLow, graphSelectedStepLow, hj] using
      hcell _ (hsource (graphSelectedLowCell_mem_source G D1 source
      rawCandidates degreeCenter degreeRadius nS gap badBudget selected
        (Fin.rev ⟨j, hj⟩)))
  · intro j hj
    simpa [stepHigh, graphSelectedStepHigh, hj] using
      hcell _ (hsource (graphSelectedHighCell_mem_source G D1 source
      rawCandidates degreeCenter degreeRadius nS gap badBudget selected
        (Fin.rev ⟨j, hj⟩)))

/-! ## Diversity-preserving deterministic selection -/

/--
The graph-state selector with the candidate-diversity witness retained.
`PartialGood` already contains this fact for its `X₀`; the basic selector
forgets it because the probability theorem does not need to expose the
witness.  The crowd assembly does need it to fill the anti-concentration
field of `LargeExposureCertificate`.
-/
theorem exists_selectedSwitchingData_of_partialGood_with_diversity
    (G : SimpleGraph V) (M : Finset (Finset V)) (D1 : Finset V)
    (s0 nS gap badBudget edgeBudget : ℕ)
    (diversityThreshold degreeCenter degreeRadius tS tX tCollision : ℝ)
    (hgood : AugmentationGraphPartial.PartialGood G M s0 diversityThreshold
      degreeCenter degreeRadius tS tX tCollision D1)
    (htS : tS ≤ (badBudget : ℝ) + 1)
    (htX : tX ≤ (badBudget : ℝ) + 1)
    (htCollision : tCollision ≤ (edgeBudget : ℝ) + 1)
    (hTuran :
      (2 * nS + gap + 1) * (s0 - badBudget + 2 * edgeBudget) <
        (s0 - badBudget) ^ 2) :
    ∃ source rawCandidates : Finset (Finset V),
      source ⊆ M ∧ rawCandidates ⊆ M ∧
      rawCandidates.card = s0 ∧
      (∀ x ∈ rawCandidates, ∀ y ∈ rawCandidates, x ≠ y →
        diversityThreshold ≤ incidenceDiffMass G D1 x y) ∧
      Nonempty (AugmentationGraphFullState.GraphSelectedSwitchingData
        source rawCandidates G D1 degreeCenter degreeRadius nS gap
          badBudget) := by
  let : LinearOrder (Finset V) := AugmentationGraphPartial.cellLinearOrder
  obtain ⟨S0, X0, hS0M, hX0M, hS0card, hX0card, hdisjoint,
    hdiverse, hbadS, hbadX, hcoll⟩ := hgood
  let bad : Finset V → Prop := fun x ↦
    ¬AugmentationGraphPartial.DegreeGood G D1 x degreeCenter degreeRadius
  let degree : Finset V → ℤ := fun x ↦ (degreeInto G D1 x : ℤ)
  have hbadSNat : (S0.filter bad).card ≤ badBudget := by
    have hlt : ((S0.filter bad).card : ℝ) < (badBudget : ℝ) + 1 :=
      hbadS.trans_le htS
    have hltNat : (S0.filter bad).card < badBudget + 1 := by
      exact_mod_cast hlt
    omega
  have hbadXNat : (X0.filter bad).card ≤ badBudget := by
    have hlt : ((X0.filter bad).card : ℝ) < (badBudget : ℝ) + 1 :=
      hbadX.trans_le htX
    have hltNat : (X0.filter bad).card < badBudget + 1 := by
      exact_mod_cast hlt
    omega
  have hcollisionNat :
      (AugmentationGraphPartial.cellCollisionEdges S0
        (degreeInto G D1)).card ≤ edgeBudget := by
    have hlt :
        ((AugmentationGraphPartial.cellCollisionEdges S0
          (degreeInto G D1)).card : ℝ) < (edgeBudget : ℝ) + 1 :=
      hcoll.trans_le htCollision
    have hltNat :
        (AugmentationGraphPartial.cellCollisionEdges S0
          (degreeInto G D1)).card < edgeBudget + 1 := by
      exact_mod_cast hlt
    omega
  have hcollisionEq :
      CollisionCounting.collisionEdges S0
          (fun x (_ : Unit) ↦ degree x) () =
        AugmentationGraphPartial.cellCollisionEdges S0 (degreeInto G D1) := by
    unfold AugmentationGraphPartial.cellCollisionEdges
    change CollisionCounting.collisionEdges S0
        (fun x (_ : Unit) ↦ degree x) () =
      CollisionCounting.collisionEdges S0
        (fun x (_ : Unit) ↦ degreeInto G D1 x) ()
    ext e
    rw [CollisionCounting.mem_collisionEdges,
      CollisionCounting.mem_collisionEdges]
    simp [degree]
  have hcollision :
      (CollisionCounting.collisionEdges S0
        (fun x (_ : Unit) ↦ degree x) ()).card ≤ edgeBudget := by
    rw [hcollisionEq]
    exact hcollisionNat
  have hgoodCard : s0 - badBudget ≤
      (AugmentationGraphFullState.goodPart S0 bad).card := by
    have hpartial := AugmentationGraphPartial.card_sub_lt_add_card_goodCells
      G D1 degreeCenter degreeRadius tS S0 hbadS
    have hgoodEq : AugmentationGraphFullState.goodPart S0 bad =
        AugmentationGraphPartial.goodCells G D1 degreeCenter degreeRadius S0 := by
      ext x
      simp [AugmentationGraphFullState.goodPart, bad,
        AugmentationGraphPartial.goodCells]
    rw [hS0card] at hpartial
    rw [hgoodEq]
    have hsreal : (s0 : ℝ) < (badBudget : ℝ) + 1 +
        (AugmentationGraphPartial.goodCells G D1 degreeCenter degreeRadius
          S0).card := by
      linarith
    have hsnat : s0 < badBudget + 1 +
        (AugmentationGraphPartial.goodCells G D1 degreeCenter degreeRadius
          S0).card := by
      exact_mod_cast hsreal
    omega
  have hselected :=
    AugmentationGraphFullState.exists_selectedSwitchingData_of_goodPart_card_lower
      S0 X0 bad degree nS gap badBudget edgeBudget (s0 - badBudget)
        hdisjoint
        (by
          convert hbadSNat using 1
          exact congrArg Finset.card
            (Finset.filter_congr_decidable S0 bad _))
        (by
          convert hbadXNat using 1
          exact congrArg Finset.card
            (Finset.filter_congr_decidable X0 bad _))
        hcollision hgoodCard hTuran
  refine ⟨S0, X0, hS0M, hX0M, hX0card, hdiverse, ?_⟩
  simpa [bad, degree] using hselected

lemma graphSelectedGoodCandidates_card_lower
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget s0 : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hrawCard : rawCandidates.card = s0) :
    s0 - badBudget ≤
      (graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected).card := by
  have hbad := selected.bad_candidates_card_le
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := rawCandidates)
    (fun x ↦ AugmentationGraphPartial.DegreeGood G D1 x degreeCenter
      degreeRadius)
  unfold graphSelectedGoodCandidates
  rw [hrawCard] at hpartition
  have hbad' :
      (rawCandidates.filter fun x ↦
        ¬AugmentationGraphPartial.DegreeGood G D1 x degreeCenter
          degreeRadius).card ≤ badBudget := by
    convert hbad using 1
    apply congrArg Finset.card
    apply Finset.ext
    simp
  omega

lemma graphSelectedGoodCandidates_card_upper
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget s0 : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hrawCard : rawCandidates.card = s0) :
    (graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected).card ≤ s0 := by
  rw [← hrawCard]
  exact Finset.card_le_card (graphSelectedGoodCandidates_subset G D1 source
    rawCandidates degreeCenter degreeRadius nS gap badBudget selected)

/-- The filtered candidate family used by the full exposure inherits every
pairwise diversity estimate carried by the raw `PartialGood` witness. -/
lemma graphSelectedGoodCandidates_diverse_of_raw
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius diversityThreshold : ℝ)
    (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hdiverse : ∀ x ∈ rawCandidates, ∀ y ∈ rawCandidates, x ≠ y →
      diversityThreshold ≤ incidenceDiffMass G D1 x y) :
    ∀ x ∈ graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected,
      ∀ y ∈ graphSelectedGoodCandidates G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected, x ≠ y →
      diversityThreshold ≤ incidenceDiffMass G D1 x y := by
  intro x hx y hy hxy
  exact hdiverse x
    (graphSelectedGoodCandidates_subset G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected hx) y
    (graphSelectedGoodCandidates_subset G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected hy) hxy

/-! ## Direct one-time crowded-path wrapper -/

/--
The large-state exposure at one time of a crowded outer path.  This theorem
performs the partial-exposure choice, retains the diverse candidate witness,
selects the high-to-low collision-thinned path, constructs the finite graph
certificate above, and applies the nested `3/4`--`1/3` composition.

The callback `hBounds` contains only the remaining displayed inequalities
for the particular selected data.  In particular it does not ask for state
decompositions, disjointness, cell cardinalities, or probability estimates.
-/
theorem one_fourth_le_layerProbability_innerWindowGood_large_at_crowdedPath
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (htime : time ≤ nW)
    (nD nS nZ s0 gap badBudget selectionEdgeBudget m : ℕ)
    (c theta divDev degreeDev tS tX tCollision : ℝ)
    (innerTheta geometricThreshold degreeThreshold meanRadius lam E qScale
      kappa sigma R globalRadius : ℝ)
    (badGeom badCollision badDegree edgeBudget piece L : ℕ)
    (P : PartialExposureCertificate G S.U0 (path.crowd time) K nD s0 S.d0
      c theta divDev degreeDev tS tX tCollision)
    (hnZ : nS + 1 = nZ)
    (htS : tS ≤ (badBudget : ℝ) + 1)
    (htX : tX ≤ (badBudget : ℝ) + 1)
    (htCollision : tCollision ≤ (selectionEdgeBudget : ℝ) + 1)
    (hTuran :
      (2 * nS + gap + 1) *
          (s0 - badBudget + 2 * selectionEdgeBudget) <
        (s0 - badBudget) ^ 2)
    (hBounds : ∀ D1 ∈ NestedUniform.layer S.U0 (2 * nD),
      AugmentationGraphPartial.PartialGood G (path.crowd time) s0
        (partialDiversityThreshold nD theta divDev)
        (partialDegreeCenter S.U0 nD S.d0)
        degreeDev tS tX tCollision D1 →
      ∀ source rawCandidates : Finset (Finset V),
        source ⊆ path.crowd time → rawCandidates ⊆ path.crowd time →
        rawCandidates.card = s0 →
        (∀ x ∈ rawCandidates, ∀ y ∈ rawCandidates, x ≠ y →
          partialDiversityThreshold nD theta divDev ≤
            incidenceDiffMass G D1 x y) →
      ∀ selected : AugmentationGraphFullState.GraphSelectedSwitchingData
        source rawCandidates G D1
          (partialDegreeCenter S.U0 nD S.d0) degreeDev nS gap badBudget,
      CrowdLargeBounds S path time D1 source rawCandidates nD nS m
        (fun D ↦ canonicalAugmentationCenter G (path.W time) S.U0 D nZ
          (degreeInto G (path.W time) (path.anchor time)) S.d0
          (partialDegreeCenter S.U0 nD S.d0))
        (partialDegreeCenter S.U0 nD S.d0) degreeDev c innerTheta
        ((degreeInto G (path.W time) (path.anchor time) : ℝ) + S.d0 -
          partialDegreeCenter S.U0 nD S.d0 / 2)
        geometricThreshold degreeThreshold meanRadius lam E qScale kappa sigma
        R globalRadius badGeom badCollision badDegree edgeBudget piece L gap
        badBudget selected) :
    (1 / 4 : ℝ) ≤ NestedUniform.layerProbability S.U0 nD
      (fun D ↦ AugmentationGraphFull.innerWindowGood G (path.W time) S.U0
        (path.crowd time) nZ L
        (canonicalAugmentationCenter G (path.W time) S.U0 D nZ
          (degreeInto G (path.W time) (path.anchor time)) S.d0
          (partialDegreeCenter S.U0 nD S.d0)) globalRadius D) := by
  let outerGood := AugmentationGraphPartial.PartialGood G (path.crowd time) s0
    (partialDiversityThreshold nD theta divDev)
    (partialDegreeCenter S.U0 nD S.d0) degreeDev tS tX tCollision
  let event : Finset V → Prop := fun D ↦
    AugmentationGraphFull.innerWindowGood G (path.W time) S.U0
      (path.crowd time) nZ L
      (canonicalAugmentationCenter G (path.W time) S.U0 D nZ
        (degreeInto G (path.W time) (path.anchor time)) S.d0
        (partialDegreeCenter S.U0 nD S.d0)) globalRadius D
  apply Augmentation.one_fourth_le_layerProbability_of_nested
    S.U0 nD outerGood event P.feasible
  · exact P.three_fourths_le_layerProbability
  · intro D1 hD1 hpartial
    obtain ⟨source, rawCandidates, hsource, hraw, hrawCard, hdiverse,
      hselected⟩ :=
      exists_selectedSwitchingData_of_partialGood_with_diversity G
        (path.crowd time) D1 s0 nS gap badBudget selectionEdgeBudget
        (partialDiversityThreshold nD theta divDev)
        (partialDegreeCenter S.U0 nD S.d0) degreeDev tS tX tCollision
        hpartial htS htX htCollision hTuran
    let selected := Classical.choice hselected
    let canonicalCenter : Finset V → ℝ := fun D ↦
      canonicalAugmentationCenter G (path.W time) S.U0 D nZ
        (degreeInto G (path.W time) (path.anchor time)) S.d0
        (partialDegreeCenter S.U0 nD S.d0)
    let bounds := hBounds D1 hD1 hpartial source rawCandidates hsource hraw
      hrawCard hdiverse selected
    let certificate := largeExposureCertificate_of_crowdedPath S path time htime
      D1 source rawCandidates hsource hraw nD nS m canonicalCenter
      (partialDegreeCenter S.U0 nD S.d0) degreeDev c innerTheta
      ((degreeInto G (path.W time) (path.anchor time) : ℝ) + S.d0 -
        partialDegreeCenter S.U0 nD S.d0 / 2)
      geometricThreshold degreeThreshold meanRadius lam E qScale kappa sigma R
      globalRadius badGeom badCollision badDegree edgeBudget piece L gap
      badBudget selected bounds
    have hthird := certificate.one_third_le_layerProbability
    simpa only [event, canonicalCenter, hnZ] using hthird

end

end AugmentationExposureCrowd
end Erdos636
