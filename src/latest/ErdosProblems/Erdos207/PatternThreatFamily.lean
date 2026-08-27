/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PatternVerticalThreats
import ErdosProblems.Erdos207.PatternTriangleGeometry
import ErdosProblems.Erdos207.PatternBaseSelectors
import ErdosProblems.Erdos207.TwoAwayIntersectionEstimates

/-! # One indexed family for vertical and forbidden extension hazards -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

abbrev PatternThreatIndex {V : Type*} [Fintype V] [DecidableEq V] (Q : SimpleGraph V) :=
  (graphSupportFinset Q) ⊕ (graphEdges Q)

def patternThreatFamily
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (S : GreedyStateOn V)
    (u : V) (hu : u ∉ graphSupportFinset Q) : PatternThreatIndex Q → TripleSystemOn V
  | .inl x => availableTrianglesContainingPair S {u, x.1}
  | .inr e => availableTwoAwayForbiddenTriangles F S (patternExtensionTriangle Q e u hu)

theorem card_patternThreatIndex
    {V : Type*} [Fintype V] [DecidableEq V] (Q : SimpleGraph V) :
    Fintype.card (PatternThreatIndex Q) = (graphSupportFinset Q).card + (graphEdges Q).card := by
  simp only [PatternThreatIndex, Fintype.card_sum, Fintype.card_coe]

theorem patternThreatFamily_subset_available
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (S : GreedyStateOn V)
    (u : V) (hu : u ∉ graphSupportFinset Q) (i : PatternThreatIndex Q) :
    patternThreatFamily F Q S u hu i ⊆ S.available := by
  cases i with
  | inl x => exact fun _ h ↦ (mem_availableTrianglesContainingPair_iff.mp h).1
  | inr e => exact inter_subset_left

theorem patternThreatFamily_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q : SimpleGraph V) (S : GreedyStateOn V)
    (u : V) (hu : u ∉ graphSupportFinset Q) :
    univ.biUnion (patternThreatFamily F Q S u hu) =
      patternVerticalPairStars Q S u ∪ patternTwoAwayThreats F Q S u hu := by
  classical
  ext T
  simp only [mem_biUnion, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨x | e, h⟩
    · exact Or.inl (mem_biUnion.mpr ⟨x.1, x.2, h⟩)
    · exact Or.inr (mem_biUnion.mpr ⟨e, mem_attach _ _, h⟩)
  · rintro (h | h)
    · obtain ⟨x, hx, hT⟩ := mem_biUnion.mp h
      exact ⟨.inl ⟨x, hx⟩, hT⟩
    · obtain ⟨e, _, hT⟩ := mem_biUnion.mp h
      exact ⟨.inr e, hT⟩

theorem patternExtensionKillers_eq_restricted_family
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (Q : SimpleGraph V) (U : Finset V) (u : V) (hu : u ∉ graphSupportFinset Q)
    (huY : u ∈ properPatternExtensions S.available Q U) :
    patternExtensionKillers F Q U S u =
      univ.biUnion (fun i : PatternThreatIndex Q ↦
        patternThreatFamily F Q S u hu i \ patternBasePairStars Q S) := by
  classical
  rw [patternExtensionKillers_eq_vertical_union_twoAway hS Q U u hu huY,
    ← patternThreatFamily_biUnion, patternSurvivalSelectors_eq_sdiff_base]
  ext T
  simp only [mem_inter, mem_sdiff, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨⟨_, hnot⟩, i, hi⟩
    exact ⟨i, hi, hnot⟩
  · rintro ⟨i, hi, hnot⟩
    exact ⟨⟨patternThreatFamily_subset_available F Q S u hu i hi, hnot⟩, i, hi⟩

theorem patternThreatFamily_pairwise_inter_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} (hS : GreedyInvariant F S)
    (hpack : ∀ E ∈ F, IsPackingOn E)
    (Q : SimpleGraph V) (u : V) (hu : u ∉ graphSupportFinset Q)
    (halive : ∀ e : graphEdges Q, patternExtensionTriangle Q e u hu ∈ S.available)
    (K : ℕ) (hK : 1 ≤ K)
    (hpair : ∀ T : TripleOn V, ∀ P : PairOn V,
      selectedCount (fun w : PairTwoAwayThreatWitness V F T P ↦ pairTwoAwayThreatRemainder w) S.chosen ≤ K)
    (hcommon : ∀ T T' : TripleOn V,
      selectedCount (fun w : CommonThreatWitness F F T T' ↦ w.remainder) S.chosen ≤ K)
    (i j : PatternThreatIndex Q) (hne : i ≠ j) :
    (patternThreatFamily F Q S u hu i ∩ patternThreatFamily F Q S u hu j).card ≤ K := by
  have hux : ∀ x : graphSupportFinset Q, u ≠ x.1 := fun x h ↦ hu (h ▸ x.2)
  cases i with
  | inl x =>
    cases j with
    | inl y =>
      apply (card_verticalPairStars_inter_le_one S (hux x) (hux y) ?_).trans hK
      intro hxy
      exact hne (congrArg Sum.inl (Subtype.ext hxy))
    | inr e =>
      let P : PairOn V := ⟨{u, x.1}, by simp [hux x]⟩
      have h := (card_pairStar_inter_twoAway_le_selected F S P
        (patternExtensionTriangle Q e u hu) hpack).trans (hpair _ P)
      exact_mod_cast h
  | inr e =>
    cases j with
    | inl x =>
      let P : PairOn V := ⟨{u, x.1}, by simp [hux x]⟩
      have h := (card_pairStar_inter_twoAway_le_selected F S P
        (patternExtensionTriangle Q e u hu) hpack).trans (hpair _ P)
      rw [inter_comm]
      exact_mod_cast h
    | inr f =>
      have hroots : patternExtensionTriangle Q e u hu ≠ patternExtensionTriangle Q f u hu := by
        intro h
        exact hne (congrArg Sum.inr (patternExtensionTriangle_injective Q u hu h))
      have h := (card_twoAway_inter_le_selected hS (halive e) (halive f) hroots).trans (hcommon _ _)
      exact_mod_cast h

end

end Erdos207
