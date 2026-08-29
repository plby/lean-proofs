/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeExplicitPostClosureAssignment
import ErdosProblems.Erdos599.SliceRestrictedDelta
import ErdosProblems.Erdos599.ColouredSafeImaginaryClassification

/-!
# Captured classification of the actual fixed-original assignment

The assigned words lie in the actual captured stage roof. Exposed finite
endpoints therefore give native filtered imaginary edges; an edge which is
not marked has both endpoints on one original uncut row member. Exposed
infinite words give popularity. Covered endpoints retain their actual closed
reference owners, rather than being declared imaginary without a witness.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath
open _root_.Erdos599.Alternating
open ColouredSafeReverseReachability ColouredSafeMovingStages
open ColouredSafeAmbientOccurrence ColouredSafeShortcutGraph
open FracturedFixedSafeAssignment

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {alpha : Ladder.Stage (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace StagePostClosureIntervalTransaction

/-- The actual survivor reference is roofed by its later frontier. -/
theorem intervalReference_vertices_subset_capturedRoof
    (T : StagePostClosureIntervalTransaction C alpha seed z R) :
    Gamma.vertexSet T.intervalReference ⊆ Gamma.roof (C.ladder.frontier R.later.stage) := by
  apply CardinalInduction.SliceRestrictedDelta.linkage_vertexSet_subset_roof_of_initial
    Gamma T.intervalReference_isLinkageBetween
  · intro x hx
    exact C.legal.frontierChronology T.current_lt hx.1
  · exact T.intervalReference_target_pure

/-- Literal edge ownership places every selected vertex in the actual
captured roof. The finite empty-word case uses source absorption. -/
theorem outsideOccurrence_vertices_subset_capturedRoof
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet))
    (A : CurrentSafeOccurrence F.outside.holes.edgeWarp
      (outsideReference T.intervalReference R.closedSet) s.1) :
    A.vertexSet ⊆ Gamma.roof (C.ladder.frontier R.later.stage) := by
  have hrow : Gamma.vertexSet T.interval.ambientInterval ⊆
      Gamma.roof (C.ladder.frontier R.later.stage) := by
    rintro x ⟨p, hp, hxp⟩
    exact T.interval.ambientInterval_in_outerRoof p hp hxp
  have hboth : Gamma.vertexSet F.outside.holes.edgeWarp ∪
      Gamma.vertexSet (outsideReference T.intervalReference R.closedSet) ⊆
      Gamma.roof (C.ladder.frontier R.later.stage) := by
    apply Set.union_subset
    · rw [F.edgeWarp_vertexSet_eq]
      exact (FocusedInsideCut.outsideCarrier_subset_vertexSet _ _).trans hrow
    · rintro x ⟨p, hp, hxp⟩
      exact T.intervalReference_vertices_subset_capturedRoof ⟨p, hp.1, hxp⟩
  cases A with
  | infinite Q =>
      exact Q.vertexSet_subset_forward_union_reference.trans hboth
  | finite t Q _hQ hfirst _hlast =>
      rintro x ⟨i, rfl⟩
      cases i using Fin.cases with
      | zero =>
          rw [hfirst]
          exact R.later.subset_roof (T.uncovered_initials_subset_closedSet F.outside s.2)
      | succ i =>
          have he := Q.actualEdge_spec i
          cases hd : Q.direction i with
          | forward =>
              simp only [hd] at he
              exact hboth (Or.inl (familyEdges_subset_vertexSet_prod _ he).2)
          | backward =>
              simp only [hd] at he
              exact hboth (Or.inr (familyEdges_subset_vertexSet_prod _ he).1)

/-- A finite selected word with exposed global endpoints is classified by
the actual captured closure. Non-marked endpoints share an original owner. -/
theorem finiteOutsideOccurrence_classification_of_exposed
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet))
    (A : CurrentSafeOccurrence F.outside.holes.edgeWarp
      (outsideReference T.intervalReference R.closedSet) s.1)
    (hgeometry : HasCutGeometry R.closedSet A) {t : V}
    (hend : A.terminal? = some t)
    (hterminal : t ∈ Gamma.terminalFrontier F.outside.holes.paths \
      Gamma.vertexSet (outsideReference T.intervalReference R.closedSet))
    (hs : s.1 ∉ Gamma.vertexSet C.ladder.limitWarp)
    (ht : t ∉ Gamma.vertexSet C.ladder.limitWarp) :
    IsFilteredImaginary C.ladder.limitWarp kappa
        (ColouredSafeHammock.CapturedByStageRoof C.ladder) s.1 t ∧
      (s.1 ≠ t → ¬IsMarked C.ladder.limitWarp kappa
        (ColouredSafeHammock.CapturedByStageRoof C.ladder) s.1 t →
        ∃ p ∈ T.interval.ambientInterval, s.1 ∈ p.support ∧ t ∈ p.support) := by
  obtain ⟨B, _hBF, hBV, hBT⟩ := T.exists_globalOccurrence F.outside A
    hgeometry.finite_cut hgeometry.infinite_cut hs (by
      intro v hv
      exact (Option.some.inj (hend.symm.trans hv)) ▸ ht)
  have hBend : B.terminal? = some t := hBT.trans hend
  have hsX := T.uncovered_initials_subset_closedSet F.outside s.2
  have htX := T.finite_terminal_mem_closedSet F.outside hterminal.1 hterminal.2
  have hcap : B.vertexSet ∩ R.closedSet ⊆ {s.1, t} := by
    rw [hBV]
    exact hgeometry.finite_cut t hend
  have hout : ¬B.vertexSet ⊆ R.closedSet := by
    rw [hBV]
    exact hgeometry.not_contained
  have hcaptured : ColouredSafeHammock.CapturedByStageRoof C.ladder s.1
      (toAmbient B) := by
    refine ⟨R.later.stage, ?_⟩
    simpa only [toAmbient_vertexSet, hBV] using
      T.outsideOccurrence_vertices_subset_capturedRoof F s A
  constructor
  · have h := hasFilteredHammock_of_external_occurrence B
      F.outside.holes.edgeWarp_isWarp F.outside.edgeWarpFiniteCharacter
      R.hammock_closed hsX hs
      (fun v hv ↦ (Option.some.inj (hBend.symm.trans hv)) ▸ htX)
      (fun v hv ↦ (Option.some.inj (hBend.symm.trans hv)) ▸ ht)
      hcaptured (by simpa only [hBend, ColouredSafeHammock.endpoints_some] using hcap)
      hout
    simpa only [hBend, IsFilteredImaginary] using h
  · intro hne hnot
    let Q := OutsideRoute.of_fractured F.outside B hBend hne hsX htX hs ht hcap hout
    apply Q.common_owner_of_not_marked T.interval.ambientInterval_linkage.isWarp
      T.interval.ambientInterval_linkage.finiteCharacter
      T.outsideIntervalGlobalReferenceEmbedding.global_isWarp R.hammock_closed
      (extra := ColouredSafeHammock.CapturedByStageRoof C.ladder) ?_ hnot
    simpa only [Q, OutsideRoute.of_fractured, toAmbient_vertexSet,
      ColouredSafeHammock.CapturedByStageRoof, CurrentSafeOccurrence.retypeForward_vertexSet]
      using hcaptured

/-- An infinite selected word with an exposed source certifies popularity
using the actual captured infinite-endpoint closure. -/
theorem infiniteOutsideOccurrence_popular_of_exposed
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet))
    (A : CurrentSafeOccurrence F.outside.holes.edgeWarp
      (outsideReference T.intervalReference R.closedSet) s.1)
    (hgeometry : HasCutGeometry R.closedSet A)
    (hend : A.terminal? = none)
    (hs : s.1 ∉ Gamma.vertexSet C.ladder.limitWarp) :
    ColouredSafeShortcutGraph.IsPopular C.ladder.limitWarp C.persistent kappa s.1 := by
  obtain ⟨B, _hBF, hBV, hBT⟩ := T.exists_globalOccurrence F.outside A
    hgeometry.finite_cut hgeometry.infinite_cut hs (by simp [hend])
  have hBend : B.terminal? = none := hBT.trans hend
  apply isPopular_of_external_infinite B
    F.outside.holes.edgeWarp_isWarp F.outside.edgeWarpFiniteCharacter
    R.hammock_closed (T.uncovered_initials_subset_closedSet F.outside s.2) hs hBend
  · refine ⟨R.later.stage, ?_⟩
    simpa only [toAmbient_vertexSet, hBV] using
      T.outsideOccurrence_vertices_subset_capturedRoof F s A
  · rw [hBV]
    exact hgeometry.infinite_cut hend
  · rw [hBV]
    exact hgeometry.not_contained

/-- One terminal-injective family with its actual cut certificates and
exhaustive native endpoint classifications. The closed-owner alternatives
are retained as data to be resolved by the later simultaneous splice. -/
structure ClassifiedFixedOutsideAssignment
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet) where
  assignment : Assignment F.outside.holes (outsideReference T.intervalReference R.closedSet)
  cut_geometry : ∀ s, HasCutGeometry R.closedSet (assignment.assigned s)
  finite_classification : ∀ s t, (assignment.assigned s).terminal? = some t →
    (IsFilteredImaginary C.ladder.limitWarp kappa
        (ColouredSafeHammock.CapturedByStageRoof C.ladder) s.1 t ∧
      (s.1 ≠ t → ¬IsMarked C.ladder.limitWarp kappa
        (ColouredSafeHammock.CapturedByStageRoof C.ladder) s.1 t →
        ∃ p ∈ T.interval.ambientInterval, s.1 ∈ p.support ∧ t ∈ p.support)) ∨
    (∃ p ∈ C.ladder.limitWarp, s.1 ∈ p.support ∧ p.support ⊆ R.closedSet) ∨
      ∃ p ∈ C.ladder.limitWarp, t ∈ p.support ∧ p.support ⊆ R.closedSet
  infinite_classification : ∀ s, (assignment.assigned s).terminal? = none →
    ColouredSafeShortcutGraph.IsPopular C.ladder.limitWarp C.persistent kappa s.1 ∨
      ∃ p ∈ C.ladder.limitWarp, s.1 ∈ p.support ∧ p.support ⊆ R.closedSet

/-- Classify a specified assignment without choosing a different family.
This preserves its exact words, terminals, and finite-edge relation. -/
def classifyFixedOutsideAssignment
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (A : Assignment F.outside.holes (outsideReference T.intervalReference R.closedSet))
    (hA : ∀ s, HasCutGeometry R.closedSet (A.assigned s)) :
    ClassifiedFixedOutsideAssignment T F := by
  have hsource := fun
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)) ↦
      T.uncovered_initials_subset_closedSet F.outside s.2
  have hterminal : ∀ s t, (A.assigned s).terminal? = some t → t ∈ R.closedSet := by
    intro s t ht
    have hterm := A.finite_terminal s ht
    exact T.finite_terminal_mem_closedSet F.outside hterm.1 hterm.2
  refine {
    assignment := A
    cut_geometry := hA
    finite_classification := ?_
    infinite_classification := ?_ }
  · intro s t ht
    by_cases hsGlobal : s.1 ∈ Gamma.vertexSet C.ladder.limitWarp
    · exact Or.inr (Or.inl
        (exists_closed_limitOwner_of_mem_closed_of_mem_limitWarpVertex R
          (hsource s) hsGlobal))
    by_cases htGlobal : t ∈ Gamma.vertexSet C.ladder.limitWarp
    · exact Or.inr (Or.inr
        (exists_closed_limitOwner_of_mem_closed_of_mem_limitWarpVertex R
          (hterminal s t ht) htGlobal))
    exact Or.inl (T.finiteOutsideOccurrence_classification_of_exposed F s
      (A.assigned s) (hA s) ht (A.finite_terminal s ht) hsGlobal htGlobal)
  · intro s hs
    by_cases hsGlobal : s.1 ∈ Gamma.vertexSet C.ladder.limitWarp
    · exact Or.inr
        (exists_closed_limitOwner_of_mem_closed_of_mem_limitWarpVertex R
          (hsource s) hsGlobal)
    exact Or.inl (T.infiniteOutsideOccurrence_popular_of_exposed F s
      (A.assigned s) (hA s) hs hsGlobal)

/-- The actual fixed-original construction supplies all classification
fields for the same chosen family, without any endpoint-exposure premise. -/
theorem exists_classifiedFixedOutsideAssignment
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (hsub : HasHereditarySubdivisionIncidence Gamma.graph) :
    Nonempty (ClassifiedFixedOutsideAssignment T F) := by
  obtain ⟨A, hA, _hsource, _hterminal, _hcases⟩ := T.exists_fixedOutsideAssignment F hsub
  exact ⟨T.classifyFixedOutsideAssignment F A hA⟩

end StagePostClosureIntervalTransaction

#print axioms
  StagePostClosureIntervalTransaction.outsideOccurrence_vertices_subset_capturedRoof
#print axioms
  StagePostClosureIntervalTransaction.finiteOutsideOccurrence_classification_of_exposed
#print axioms
  StagePostClosureIntervalTransaction.infiniteOutsideOccurrence_popular_of_exposed
#print axioms StagePostClosureIntervalTransaction.classifyFixedOutsideAssignment
#print axioms
  StagePostClosureIntervalTransaction.exists_classifiedFixedOutsideAssignment

end Erdos599.Blueprint.LinkageBlueprint

