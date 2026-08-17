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

import ErdosProblems.Erdos636.AugmentationExposureCrowd

/-!
# Scalar bounds for the selected high-to-low exposure path

This module discharges the graph-dependent scalar fields of the large
exposure certificate.  It sits immediately after `AugmentationExposureCrowd`
and turns the literal geometry proved there into closed-form inequalities.

For a one-cell step, the deterministic mean has three contributions.  The
two cells lie in one crowd degree window, their degrees into `U0` agree, and
the internal change is at most `K^2 * nS`.  For the two endpoints, summing
the integral selected low/high gap gives `nS * (gap + 1)`, while the crowd
window and the possible loss of all high-endpoint internal edges cost at
most `2 * nS * degreeWindow` and `(K * nS)^2`, respectively.
-/

open Classical SimpleGraph

namespace Erdos636
namespace AugmentationExposureStepBounds

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

open AugmentationExposureAssembly
open AugmentationExposureCrowd

local instance cellDecidableEq : DecidableEq (Finset V) :=
  AugmentationGraphPartial.cellLinearOrder.toDecidableEq

private lemma card_cellUnion_eq_mul_of_uniform
    (M : Finset (Finset V)) (k : ℕ)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (huniform : ∀ x ∈ M, x.card = k) :
    (AugmentationGraphFull.cellUnion M).card = M.card * k := by
  exact card_matching_biUnion_eq_mul hpair huniform

/-! ## One-step bound -/

/--
The deterministic centered mean of every selected high-to-low one-cell
switch is controlled by one explicit scalar inequality.  No graph-valued
bound is assumed: all graph terms are discharged from the crowd window,
uniform structural degrees, pairwise-disjoint matching cells, and `k ≤ K`.
-/
theorem graphSelectedStepMean_le_of_scalar
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    {mu degreeWindow : ℕ}
    (path : OuterSwitchingPath.CrowdedPath S mu degreeWindow)
    (time : ℕ) (htime : time ≤ nW)
    (D1 : Finset V) (source rawCandidates : Finset (Finset V))
    (nD nS : ℕ) (degreeCenter degreeRadius meanRadius : ℝ)
    (gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hsource : source ⊆ path.crowd time)
    (hscalar : (2 * degreeWindow : ℝ) + (K ^ 2 * nS : ℕ) +
        degreeRadius ≤ meanRadius * Real.sqrt nD) :
    ∀ j < nS,
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
        meanRadius * Real.sqrt nD := by
  intro j hj
  let i : Fin nS := Fin.rev ⟨j, hj⟩
  let R := AugmentationGraphFull.cellUnion
    (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected i)
  let X := graphSelectedLowCell G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i
  let Y := graphSelectedHighCell G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i
  have hXsource : X ∈ source := graphSelectedLowCell_mem_source G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected i
  have hYsource : Y ∈ source := graphSelectedHighCell_mem_source G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected i
  have hXmatching : X ∈ S.matching :=
    path.crowd_subset time htime (hsource hXsource)
  have hYmatching : Y ∈ S.matching :=
    path.crowd_subset time htime (hsource hYsource)
  have hrestMatching :
      graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i ⊆ S.matching :=
    (graphSelectedRestFamily_subset_source G D1 source rawCandidates degreeCenter degreeRadius
      nS gap badBudget selected i).trans
      (hsource.trans (path.crowd_subset time htime))
  have hpairRest :
      ((graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i : Finset (Finset V)) :
          Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact S.matching_pairwiseDisjoint (hrestMatching hx) (hrestMatching hy) hxy
  have hRcardEq : R.card =
      (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i).card * S.k := by
    exact card_cellUnion_eq_mul_of_uniform _ S.k hpairRest
      (fun x hx ↦ S.matching_uniform x (hrestMatching hx))
  have hRcard : R.card ≤ K * (nS - 1) := by
    rw [hRcardEq]
    have hk := S.k_le
    have hc := card_graphSelectedRestFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected i
    have hc' : (graphSelectedRestFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected i).card = nS - 1 := by omega
    rw [hc']
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right (nS - 1) S.k_le
  have hXcard : X.card ≤ K :=
    (S.matching_uniform X hXmatching).le.trans S.k_le
  have hYcard : Y.card ≤ K :=
    (S.matching_uniform Y hYmatching).le.trans S.k_le
  have hRX : Disjoint R X := by
    exact AugmentationGraphFull.cellUnion_disjoint_cell_of_pairwise
      S.matching_pairwiseDisjoint hrestMatching hXmatching
        (graphSelectedLowCell_not_mem_rest G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i)
  have hRY : Disjoint R Y := by
    exact AugmentationGraphFull.cellUnion_disjoint_cell_of_pairwise
      S.matching_pairwiseDisjoint hrestMatching hYmatching
        (graphSelectedHighCell_not_mem_rest G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected i)
  have hnS : 1 ≤ nS := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hinternalZ := abs_internal_switch_contribution_le G hnS hRcard
    hXcard hYcard hRX hRY
  have hinternal :
      |(Erdos88.inducedEdges G (R ∪ X) : ℝ) -
          Erdos88.inducedEdges G (R ∪ Y)| ≤ (K ^ 2 * nS : ℕ) := by
    exact_mod_cast hinternalZ
  have hWX := path.crowd_degree_window htime (hsource hXsource)
  have hWY := path.crowd_degree_window htime (hsource hYsource)
  have hW :
      |((G.interedges (path.W time) X).card : ℝ) -
          (G.interedges (path.W time) Y).card| ≤ 2 * degreeWindow := by
    rw [AugmentationGraphFullIdentity.card_interedges_eq_degreeInto,
      AugmentationGraphFullIdentity.card_interedges_eq_degreeInto]
    have hWX' : |(degreeInto G (path.W time) X : ℝ) -
        degreeInto G (path.W time) (path.anchor time)| ≤ degreeWindow := by
      exact_mod_cast hWX
    have hWY' : |(degreeInto G (path.W time) Y : ℝ) -
        degreeInto G (path.W time) (path.anchor time)| ≤ degreeWindow := by
      exact_mod_cast hWY
    calc
      |(degreeInto G (path.W time) X : ℝ) -
          degreeInto G (path.W time) Y| =
          |((degreeInto G (path.W time) X : ℝ) -
              degreeInto G (path.W time) (path.anchor time)) -
            ((degreeInto G (path.W time) Y : ℝ) -
              degreeInto G (path.W time) (path.anchor time))| := by ring_nf
      _ ≤ |(degreeInto G (path.W time) X : ℝ) -
              degreeInto G (path.W time) (path.anchor time)| +
            |(degreeInto G (path.W time) Y : ℝ) -
              degreeInto G (path.W time) (path.anchor time)| := by
        calc
          |_ - _| = |((degreeInto G (path.W time) X : ℝ) -
                degreeInto G (path.W time) (path.anchor time)) +
              (-((degreeInto G (path.W time) Y : ℝ) -
                degreeInto G (path.W time) (path.anchor time)))| := by rfl
          _ ≤ |(degreeInto G (path.W time) X : ℝ) -
                degreeInto G (path.W time) (path.anchor time)| +
              |-((degreeInto G (path.W time) Y : ℝ) -
                degreeInto G (path.W time) (path.anchor time))| :=
            abs_add_le _ _
          _ = _ := by rw [abs_neg]
      _ ≤ 2 * degreeWindow := by linarith
  have hU : degreeInto G S.U0 X = degreeInto G S.U0 Y := by
    rw [S.degree_U0 X hXmatching, S.degree_U0 Y hYmatching]
  have hDlow := graphSelectedLowCell_degreeGood G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i
  have hDhigh := graphSelectedHighCell_degreeGood G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected i
  have hD :
      |((degreeInto G D1 Y : ℝ) - degreeInto G D1 X) / 2| ≤
        degreeRadius := by
    unfold AugmentationGraphPartial.DegreeGood at hDlow hDhigh
    have hdiff : |(degreeInto G D1 Y : ℝ) - degreeInto G D1 X| ≤
        2 * degreeRadius := by
      calc
        |(degreeInto G D1 Y : ℝ) - degreeInto G D1 X| =
            |((degreeInto G D1 Y : ℝ) - degreeCenter) -
              ((degreeInto G D1 X : ℝ) - degreeCenter)| := by ring_nf
        _ ≤ |(degreeInto G D1 Y : ℝ) - degreeCenter| +
            |(degreeInto G D1 X : ℝ) - degreeCenter| := by
          calc
            |_ - _| = |((degreeInto G D1 Y : ℝ) - degreeCenter) +
                (-((degreeInto G D1 X : ℝ) - degreeCenter))| := by rfl
            _ ≤ |(degreeInto G D1 Y : ℝ) - degreeCenter| +
                |-((degreeInto G D1 X : ℝ) - degreeCenter)| := abs_add_le _ _
            _ = _ := by rw [abs_neg]
        _ ≤ 2 * degreeRadius := by linarith
    rw [abs_div]
    norm_num
    linarith
  simp only [graphSelectedStepRest, graphSelectedStepLow,
    graphSelectedStepHigh, hj, ↓reduceDIte]
  change |(AugmentationGraphFullIdentity.switchOffsetInt G (path.W time) S.U0
      R X Y : ℝ) +
        ((degreeInto G D1 Y : ℝ) - degreeInto G D1 X) / 2| ≤ _
  simp only [AugmentationGraphFullIdentity.switchOffsetInt]
  push_cast
  rw [hU]
  have heq :
      ((G.interedges (path.W time) X).card : ℝ) -
          (G.interedges (path.W time) Y).card +
          (degreeInto G S.U0 Y : ℝ) - degreeInto G S.U0 Y +
          ((Erdos88.inducedEdges G (R ∪ X) : ℝ) -
            Erdos88.inducedEdges G (R ∪ Y)) +
          ((degreeInto G D1 Y : ℝ) - degreeInto G D1 X) / 2 =
        (((G.interedges (path.W time) X).card : ℝ) -
          (G.interedges (path.W time) Y).card) +
        ((Erdos88.inducedEdges G (R ∪ X) : ℝ) -
          Erdos88.inducedEdges G (R ∪ Y)) +
        ((degreeInto G D1 Y : ℝ) - degreeInto G D1 X) / 2 := by ring
  rw [heq]
  calc
    |(((G.interedges (path.W time) X).card : ℝ) -
          (G.interedges (path.W time) Y).card) +
        ((Erdos88.inducedEdges G (R ∪ X) : ℝ) -
          Erdos88.inducedEdges G (R ∪ Y)) +
        ((degreeInto G D1 Y : ℝ) - degreeInto G D1 X) / 2| ≤
        |((G.interedges (path.W time) X).card : ℝ) -
          (G.interedges (path.W time) Y).card| +
        |(Erdos88.inducedEdges G (R ∪ X) : ℝ) -
          Erdos88.inducedEdges G (R ∪ Y)| +
        |((degreeInto G D1 Y : ℝ) - degreeInto G D1 X) / 2| := by
      calc
        |_ + _ + _| ≤
            |(((G.interedges (path.W time) X).card : ℝ) -
              (G.interedges (path.W time) Y).card) +
              ((Erdos88.inducedEdges G (R ∪ X) : ℝ) -
                Erdos88.inducedEdges G (R ∪ Y))| +
            |((degreeInto G D1 Y : ℝ) - degreeInto G D1 X) / 2| :=
          abs_add_le _ _
        _ ≤ (|((G.interedges (path.W time) X).card : ℝ) -
              (G.interedges (path.W time) Y).card| +
            |(Erdos88.inducedEdges G (R ∪ X) : ℝ) -
              Erdos88.inducedEdges G (R ∪ Y)|) +
            |((degreeInto G D1 Y : ℝ) - degreeInto G D1 X) / 2| := by
          gcongr
          exact abs_add_le _ _
        _ = _ := by ring
    _ ≤ (2 * degreeWindow : ℝ) + (K ^ 2 * nS : ℕ) +
        degreeRadius := by gcongr
    _ ≤ meanRadius * Real.sqrt nD := hscalar

end

end AugmentationExposureStepBounds
end Erdos636
