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

/-!
# Endpoint bounds for the selected augmentation path

This module isolates the deterministic algebra behind the mean-rise field of
the large exposure certificate.  The selected path is traversed from the
high-degree block to the low-degree block.  Consequently the half-deletion
correction contributes a positive multiple of the selected degree gap.

The three remaining endpoint terms are controlled without probabilistic
hypotheses: the internal-edge loss is at most `(K * nS)^2`, the crossing-edge
loss into `W` is at most `2 * nS * degreeWindow`, and the contribution into
`U0` cancels because every selected cell has the same `U0`-degree.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace AugmentationExposureEndpointBounds

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

open AugmentationExposureAssembly

local instance cellDecidableEq : DecidableEq (Finset V) :=
  AugmentationGraphPartial.cellLinearOrder.toDecidableEq

/-! ## Literal selected endpoints -/

/-- The low block carried by graph-selected switching data. -/
noncomputable def graphSelectedLowFamily
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    Finset (Finset V) :=
  selected.split.low

/-- The high block carried by graph-selected switching data. -/
noncomputable def graphSelectedHighFamily
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    Finset (Finset V) :=
  selected.split.high

@[simp] lemma card_graphSelectedLowFamily
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    (graphSelectedLowFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected).card = nS := by
  exact selected.split.low_card

@[simp] lemma card_graphSelectedHighFamily
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    (graphSelectedHighFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected).card = nS := by
  exact selected.split.high_card

lemma graphSelectedLowFamily_subset_source
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    graphSelectedLowFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected ⊆ source := by
  exact selected.split.low_subset.trans
    (selected.selected_subset_good.trans
      (AugmentationGraphFullState.goodPart_subset _ _))

lemma graphSelectedHighFamily_subset_source
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    graphSelectedHighFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected ⊆ source := by
  exact selected.split.high_subset.trans
    (selected.selected_subset_good.trans
      (AugmentationGraphFullState.goodPart_subset _ _))

@[simp] lemma graphSelectedReverseState_zero
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    graphSelectedReverseState G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected 0 =
      graphSelectedHighFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected := by
  unfold graphSelectedReverseState graphSelectedState graphSelectedHighFamily
  simp only [Nat.zero_lt_succ, dite_true]
  rw [show (Fin.rev (⟨0, Nat.zero_lt_succ nS⟩ : Fin (nS + 1))) =
      Fin.last nS by
    apply Fin.ext
    simp [Fin.rev]]
  exact selected.state_last

@[simp] lemma graphSelectedReverseState_last
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget) :
    graphSelectedReverseState G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected nS =
      graphSelectedLowFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected := by
  unfold graphSelectedReverseState graphSelectedState graphSelectedLowFamily
  simp only [Nat.lt_add_one_iff, le_refl, dite_true]
  rw [show (Fin.rev (⟨nS, Nat.lt_add_one nS⟩ : Fin (nS + 1))) = 0 by
    apply Fin.ext
    simp [Fin.rev]]
  exact selected.state_zero

/-! ## Additivity and coarse family bounds -/

/-- `degreeInto` is additive over the vertex union of pairwise-disjoint
cells. -/
lemma degreeInto_cellUnion_eq_sum
    (G : SimpleGraph V) (A : Finset V) (Z : Finset (Finset V))
    (hpair : (Z : Set (Finset V)).PairwiseDisjoint id) :
    degreeInto G A (AugmentationGraphFull.cellUnion Z) =
      ∑ x ∈ Z, degreeInto G A x := by
  unfold AugmentationGraphFull.cellUnion degreeInto
  exact Finset.sum_biUnion hpair

/-- A union of `n` cells, each of size at most `K`, has at most `K*n`
vertices.  Pairwise disjointness is not needed for this upper bound. -/
lemma card_cellUnion_le_mul
    (Z : Finset (Finset V)) (K n : ℕ)
    (hcard : Z.card = n) (hK : ∀ x ∈ Z, x.card ≤ K) :
    (AugmentationGraphFull.cellUnion Z).card ≤ K * n := by
  calc
    (AugmentationGraphFull.cellUnion Z).card ≤ ∑ x ∈ Z, x.card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ Z, K := Finset.sum_le_sum fun x hx ↦ hK x hx
    _ = Z.card * K := by simp
    _ = K * n := by rw [hcard, Nat.mul_comm]

/-! ## The three endpoint contributions -/

/-- The strict integral selected gap upgrades to `gap + 1` and sums across
the two equally sized selected blocks. -/
lemma selected_degreeInto_gap
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hnS : 0 < nS)
    (M : Finset (Finset V))
    (hsource : source ⊆ M)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id) :
    (nS : ℝ) * (gap + 1 : ℝ) ≤
      (degreeInto G D1
          (AugmentationGraphFull.cellUnion
            (graphSelectedHighFamily G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected)) : ℝ) -
        degreeInto G D1
          (AugmentationGraphFull.cellUnion
            (graphSelectedLowFamily G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected)) := by
  let low := graphSelectedLowFamily G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected
  let high := graphSelectedHighFamily G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected
  have hlowSource : low ⊆ source :=
    graphSelectedLowFamily_subset_source G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected
  have hhighSource : high ⊆ source :=
    graphSelectedHighFamily_subset_source G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected
  have hlowPair : (low : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hpair (hsource (hlowSource hx)) (hsource (hlowSource hy)) hxy
  have hhighPair : (high : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hpair (hsource (hhighSource hx)) (hsource (hhighSource hy)) hxy
  have hlowCard : low.card = nS :=
    card_graphSelectedLowFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected
  have hhighCard : high.card = nS :=
    card_graphSelectedHighFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected
  have hlowNonempty : low.Nonempty := Finset.card_pos.mp (hlowCard.symm ▸ hnS)
  have hpoint : ∀ x ∈ low, ∀ y ∈ high,
      (degreeInto G D1 x : ℤ) + (gap + 1 : ℕ) ≤
        (degreeInto G D1 y : ℤ) := by
    intro x hx y hy
    have hgap := selected.gap_lt x hx y hy
    omega
  have hsum := DegreeSorting.card_mul_le_sum_sub_sum_of_pairwise_gap
    (a := fun x : Finset V ↦ (degreeInto G D1 x : ℤ))
    (d := ((gap + 1 : ℕ) : ℤ)) hlowNonempty
    (hlowCard.trans hhighCard.symm) hpoint
  have hlowSum : degreeInto G D1 (AugmentationGraphFull.cellUnion low) =
      ∑ x ∈ low, degreeInto G D1 x :=
    degreeInto_cellUnion_eq_sum G D1 low hlowPair
  have hhighSum : degreeInto G D1 (AugmentationGraphFull.cellUnion high) =
      ∑ x ∈ high, degreeInto G D1 x :=
    degreeInto_cellUnion_eq_sum G D1 high hhighPair
  have hsumReal :
      ((low.card : ℤ) * ((gap + 1 : ℕ) : ℤ) : ℝ) ≤
        (((∑ y ∈ high, (degreeInto G D1 y : ℤ)) -
          ∑ x ∈ low, (degreeInto G D1 x : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast hsum
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_sum] at hsumReal
  rw [hlowCard] at hsumReal
  rw [hhighSum, hlowSum]
  norm_cast at hsumReal ⊢

/-- Equal cell degrees into `U0` make the two endpoint contributions into
`U0` cancel exactly. -/
lemma selected_degreeInto_U0_eq
    (G : SimpleGraph V) (U0 D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget d0 : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (M : Finset (Finset V))
    (hsource : source ⊆ M)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (hdegree : ∀ x ∈ M, degreeInto G U0 x = d0) :
    degreeInto G U0
        (AugmentationGraphFull.cellUnion
          (graphSelectedHighFamily G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected)) =
      degreeInto G U0
        (AugmentationGraphFull.cellUnion
          (graphSelectedLowFamily G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected)) := by
  let low := graphSelectedLowFamily G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected
  let high := graphSelectedHighFamily G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected
  have hlowSource : low ⊆ source :=
    graphSelectedLowFamily_subset_source G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected
  have hhighSource : high ⊆ source :=
    graphSelectedHighFamily_subset_source G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected
  have hlowPair : (low : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hpair (hsource (hlowSource hx)) (hsource (hlowSource hy)) hxy
  have hhighPair : (high : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hpair (hsource (hhighSource hx)) (hsource (hhighSource hy)) hxy
  rw [degreeInto_cellUnion_eq_sum G U0 high hhighPair,
    degreeInto_cellUnion_eq_sum G U0 low hlowPair]
  calc
    ∑ x ∈ high, degreeInto G U0 x = ∑ _x ∈ high, d0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hdegree x (hsource (hhighSource hx))
    _ = high.card * d0 := by simp
    _ = nS * d0 := by
      rw [card_graphSelectedHighFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected]
    _ = low.card * d0 := by
      rw [card_graphSelectedLowFamily G D1 source rawCandidates degreeCenter
        degreeRadius nS gap badBudget selected]
    _ = ∑ _x ∈ low, d0 := by simp
    _ = ∑ x ∈ low, degreeInto G U0 x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (hdegree x (hsource (hlowSource hx))).symm

/-- If all selected cells have `W`-degree in a common integral window, the
high-to-low endpoint crossing term loses at most twice the window per cell. -/
lemma selected_degreeInto_W_lower
    (G : SimpleGraph V) (W D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (M : Finset (Finset V))
    (hsource : source ⊆ M)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (anchorDegree : ℤ) (degreeWindow : ℕ)
    (hwindow : ∀ x ∈ M,
      |(degreeInto G W x : ℤ) - anchorDegree| ≤ degreeWindow) :
    -(2 * (nS : ℤ) * degreeWindow) ≤
      (degreeInto G W
          (AugmentationGraphFull.cellUnion
            (graphSelectedLowFamily G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected)) : ℤ) -
        degreeInto G W
          (AugmentationGraphFull.cellUnion
            (graphSelectedHighFamily G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected)) := by
  let low := graphSelectedLowFamily G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected
  let high := graphSelectedHighFamily G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected
  have hlowSource : low ⊆ source :=
    graphSelectedLowFamily_subset_source G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected
  have hhighSource : high ⊆ source :=
    graphSelectedHighFamily_subset_source G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected
  have hlowPair : (low : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hpair (hsource (hlowSource hx)) (hsource (hlowSource hy)) hxy
  have hhighPair : (high : Set (Finset V)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hpair (hsource (hhighSource hx)) (hsource (hhighSource hy)) hxy
  have hlowBound : ∑ x ∈ low, (anchorDegree - (degreeWindow : ℤ)) ≤
      ∑ x ∈ low, (degreeInto G W x : ℤ) := by
    apply Finset.sum_le_sum
    intro x hx
    have hxw := hwindow x (hsource (hlowSource hx))
    rw [abs_le] at hxw
    omega
  have hhighBound : ∑ x ∈ high, (degreeInto G W x : ℤ) ≤
      ∑ x ∈ high, (anchorDegree + (degreeWindow : ℤ)) := by
    apply Finset.sum_le_sum
    intro x hx
    have hxw := hwindow x (hsource (hhighSource hx))
    rw [abs_le] at hxw
    omega
  have hlowCard : low.card = nS :=
    card_graphSelectedLowFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected
  have hhighCard : high.card = nS :=
    card_graphSelectedHighFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected
  simp only [Finset.sum_const, nsmul_eq_mul] at hlowBound hhighBound
  rw [hlowCard] at hlowBound
  rw [hhighCard] at hhighBound
  have hsum : -(2 * (nS : ℤ) * degreeWindow) ≤
      (∑ x ∈ low, (degreeInto G W x : ℤ)) -
        ∑ x ∈ high, (degreeInto G W x : ℤ) := by
    calc
      -(2 * (nS : ℤ) * degreeWindow) =
          (nS : ℤ) * (anchorDegree - degreeWindow) -
            (nS : ℤ) * (anchorDegree + degreeWindow) := by ring
      _ ≤ (∑ x ∈ low, (degreeInto G W x : ℤ)) -
          ∑ x ∈ high, (degreeInto G W x : ℤ) :=
        sub_le_sub hlowBound hhighBound
  have hlowSum := degreeInto_cellUnion_eq_sum G W low hlowPair
  have hhighSum := degreeInto_cellUnion_eq_sum G W high hhighPair
  rw [hlowSum, hhighSum]
  exact_mod_cast hsum

/-- The internal-edge endpoint term loses at most `(K*nS)^2`. -/
lemma selected_inducedEdges_lower
    (G : SimpleGraph V) (D1 : Finset V)
    (source rawCandidates : Finset (Finset V))
    (degreeCenter degreeRadius : ℝ) (nS gap badBudget K : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (M : Finset (Finset V))
    (hsource : source ⊆ M)
    (hcell : ∀ x ∈ M, x.card ≤ K) :
    -(((K * nS) ^ 2 : ℕ) : ℤ) ≤
      (Erdos88.inducedEdges G
          (AugmentationGraphFull.cellUnion
            (graphSelectedLowFamily G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected)) : ℤ) -
        Erdos88.inducedEdges G
          (AugmentationGraphFull.cellUnion
            (graphSelectedHighFamily G D1 source rawCandidates degreeCenter
              degreeRadius nS gap badBudget selected)) := by
  let high := graphSelectedHighFamily G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected
  have hhighSource : high ⊆ source :=
    graphSelectedHighFamily_subset_source G D1 source rawCandidates
      degreeCenter degreeRadius nS gap badBudget selected
  have hhighCard : high.card = nS :=
    card_graphSelectedHighFamily G D1 source rawCandidates degreeCenter
      degreeRadius nS gap badBudget selected
  have hvertices : (AugmentationGraphFull.cellUnion high).card ≤ K * nS :=
    card_cellUnion_le_mul high K nS hhighCard
      (fun x hx ↦ hcell x (hsource (hhighSource hx)))
  have hedge : Erdos88.inducedEdges G (AugmentationGraphFull.cellUnion high) ≤
      (K * nS) ^ 2 :=
    (inducedEdges_le_card_sq G _).trans (Nat.pow_le_pow_left hvertices 2)
  change -(((K * nS) ^ 2 : ℕ) : ℤ) ≤
    (Erdos88.inducedEdges G
      (AugmentationGraphFull.cellUnion
        (graphSelectedLowFamily G D1 source rawCandidates degreeCenter
          degreeRadius nS gap badBudget selected)) : ℤ) -
      Erdos88.inducedEdges G (AugmentationGraphFull.cellUnion high)
  have hedgeZ :
      (Erdos88.inducedEdges G (AugmentationGraphFull.cellUnion high) : ℤ) ≤
        ((K * nS) ^ 2 : ℕ) := by
    exact_mod_cast hedge
  have hlowZ : 0 ≤
      (Erdos88.inducedEdges G
        (AugmentationGraphFull.cellUnion
          (graphSelectedLowFamily G D1 source rawCandidates degreeCenter
            degreeRadius nS gap badBudget selected)) : ℤ) := by positivity
  omega

/-! ## Combined mean-rise endpoint -/

/-- Direct deterministic discharge of `CrowdLargeBounds.mean_rise`.

The scalar premise is deliberately arranged so that callers only choose a
target rise `lam`; all graph-valued endpoint terms are discharged here. -/
theorem mean_rise_of_selectedReverseState
    (G : SimpleGraph V) (W U0 D1 : Finset V)
    (source rawCandidates M : Finset (Finset V))
    (degreeCenter degreeRadius lam : ℝ)
    (nS gap badBudget K d0 degreeWindow : ℕ)
    (selected : AugmentationGraphFullState.GraphSelectedSwitchingData
      source rawCandidates G D1 degreeCenter degreeRadius nS gap badBudget)
    (hnS : 0 < nS)
    (hsource : source ⊆ M)
    (hpair : (M : Set (Finset V)).PairwiseDisjoint id)
    (hcell : ∀ x ∈ M, x.card ≤ K)
    (hdegreeU0 : ∀ x ∈ M, degreeInto G U0 x = d0)
    (anchorDegree : ℤ)
    (hdegreeW : ∀ x ∈ M,
      |(degreeInto G W x : ℤ) - anchorDegree| ≤ degreeWindow)
    (hscalar :
      lam + (((K * nS) ^ 2 : ℕ) : ℝ) +
          2 * (nS : ℝ) * degreeWindow ≤
        (nS : ℝ) * (gap + 1 : ℝ) / 2) :
    lam ≤
      (AugmentationGraphFullIdentity.endpointOffsetInt G W U0
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
              degreeRadius nS gap badBudget selected nS))) / 2 := by
  rw [graphSelectedReverseState_zero, graphSelectedReverseState_last]
  let low := graphSelectedLowFamily G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected
  let high := graphSelectedHighFamily G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected
  have hD := selected_degreeInto_gap G D1 source rawCandidates degreeCenter
    degreeRadius nS gap badBudget selected hnS M hsource hpair
  have hU := selected_degreeInto_U0_eq G U0 D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget d0 selected M hsource hpair hdegreeU0
  have hWInt := selected_degreeInto_W_lower G W D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget selected M hsource hpair
    anchorDegree degreeWindow hdegreeW
  have hW : -(2 * (nS : ℝ) * degreeWindow) ≤
      (degreeInto G W (AugmentationGraphFull.cellUnion low) : ℝ) -
        degreeInto G W (AugmentationGraphFull.cellUnion high) := by
    exact_mod_cast hWInt
  have hedgeInt := selected_inducedEdges_lower G D1 source rawCandidates
    degreeCenter degreeRadius nS gap badBudget K selected M hsource hcell
  have hedge : -(((K * nS) ^ 2 : ℕ) : ℝ) ≤
      (Erdos88.inducedEdges G (AugmentationGraphFull.cellUnion low) : ℝ) -
        Erdos88.inducedEdges G (AugmentationGraphFull.cellUnion high) := by
    exact_mod_cast hedgeInt
  have hlower :
      (nS : ℝ) * (gap + 1 : ℝ) / 2 -
          (((K * nS) ^ 2 : ℕ) : ℝ) -
          2 * (nS : ℝ) * degreeWindow ≤
        ((Erdos88.inducedEdges G
            (AugmentationGraphFull.cellUnion low) : ℝ) -
          Erdos88.inducedEdges G
            (AugmentationGraphFull.cellUnion high)) +
        ((degreeInto G W (AugmentationGraphFull.cellUnion low) : ℝ) -
          degreeInto G W (AugmentationGraphFull.cellUnion high)) +
        ((degreeInto G U0 (AugmentationGraphFull.cellUnion low) : ℝ) -
          degreeInto G U0 (AugmentationGraphFull.cellUnion high)) +
        ((degreeInto G D1 (AugmentationGraphFull.cellUnion high) : ℝ) -
          degreeInto G D1 (AugmentationGraphFull.cellUnion low)) / 2 := by
    have hUreal :
        (degreeInto G U0 (AugmentationGraphFull.cellUnion low) : ℝ) -
          degreeInto G U0 (AugmentationGraphFull.cellUnion high) = 0 := by
      change degreeInto G U0 (AugmentationGraphFull.cellUnion high) =
        degreeInto G U0 (AugmentationGraphFull.cellUnion low) at hU
      rw [show degreeInto G U0 (AugmentationGraphFull.cellUnion low) =
          degreeInto G U0 (AugmentationGraphFull.cellUnion high) from hU.symm]
      simp
    rw [hUreal]
    linarith
  have hlam : lam ≤
      (nS : ℝ) * (gap + 1 : ℝ) / 2 -
        (((K * nS) ^ 2 : ℕ) : ℝ) -
        2 * (nS : ℝ) * degreeWindow := by
    linarith
  apply hlam.trans
  apply hlower.trans_eq
  simp only [AugmentationGraphFullIdentity.endpointOffsetInt]
  push_cast
  rw [AugmentationGraphFullIdentity.card_interedges_eq_degreeInto,
    AugmentationGraphFullIdentity.card_interedges_eq_degreeInto]
  ring

end

end AugmentationExposureEndpointBounds
end Erdos636
