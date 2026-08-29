/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeBoundedFeedbackObstruction
import ErdosProblems.Erdos599.ColouredSafeFiniteCarrierHall
import ErdosProblems.Erdos599.ColouredSafeSubdivisionReferenceContact

/-!
# Fixed-original Hall under internal reference incidence

The two ambient carriers may be infinite. The finite source set contains
only sources without an original infinite safe word. The internal-edge
condition is retained explicitly and is derived for a subdivided graph;
it is not silently extended to arbitrary fractured vertex duplication.
-/

namespace Erdos599.Alternating.ColouredSafeInternalReferenceHall

open Set DirectedPath FiniteColouredOccurrenceWord ColouredSafeReverseReachability
open ColouredSafeGraphLift ColouredSafeFiniteCarrierHall

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

def InternalReferenceEdges (W Y : Set Gamma.DPath) : Prop :=
  ∀ {a b}, (a, b) ∈ familyEdges W → a ∈ Gamma.vertexSet Y →
    b ∈ Gamma.vertexSet Y → b ∉ Gamma.initialSet Y →
    a ∉ Gamma.terminalFrontier Y → (a, b) ∈ familyEdges Y

theorem hall_nonterminal_of_auxiliaryAdj
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (hinternal : InternalReferenceEdges W Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1)
    (hnonterminal : ∀ s ∈ J, s.1 ∉ Gamma.terminalFrontier W)
    (hadj : ∀ s ∈ J, ∀ t ∈ safeTerminalUnion J, Gamma.graph.Adj s.1 t) :
    J.ncard ≤ (safeTerminalUnion J).ncard := by
  by_contra hnot
  have hN := safeTerminalUnion_finite hW hY hWfin hYfin hJ hno
  obtain ⟨C, hYC, hYCfin, _hCfinite, hdisjoint, hsource', hterminal', htails,
    hCV, hcover, s, hsJ, hsOff⟩ :=
    ColouredSafeFiniteFeedbackFamily.exists_auxiliaryReference_of_deficit
      hY hYfin hsource hterminal hJ hN hnonterminal hadj (Nat.lt_of_not_ge hnot)
  exact hsOff
    (ColouredSafeBoundedFeedbackObstruction.no_uncoveredSource_of_no_original_safeInfinite
      hW hY hWfin hYfin hYC hYCfin hdisjoint hsource' hterminal'
      hJ hno hnonterminal htails hCV hcover hinternal ⟨s, hsJ, rfl⟩)

theorem hall_nonterminal
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (hinternal : InternalReferenceEdges W Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1)
    (hnonterminal : ∀ s ∈ J, s.1 ∉ Gamma.terminalFrontier W) :
    J.ncard ≤ (safeTerminalUnion J).ncard := by
  let h : ∀ {x y}, Gamma.graph.Adj x y → (completeWeb Gamma).graph.Adj x y :=
    fun _ ↦ True.intro
  have hsource' : (completeWeb Gamma).initialSet (liftFamily h Y) ⊆
      (completeWeb Gamma).initialSet (liftFamily h W) := by
    simpa only [liftFamily_initialSet] using hsource
  have hterminal' : (completeWeb Gamma).terminalFrontier (liftFamily h W) ∩
      (completeWeb Gamma).vertexSet (liftFamily h Y) ⊆
      (completeWeb Gamma).terminalFrontier (liftFamily h Y) := by
    simpa only [liftFamily_terminalFrontier, liftFamily_vertexSet] using hterminal
  have hinternal' : InternalReferenceEdges (liftFamily h W) (liftFamily h Y) := by
    intro a b
    simpa only [liftFamily_edges, liftFamily_vertexSet,
      liftFamily_initialSet, liftFamily_terminalFrontier] using (hinternal (a := a) (b := b))
  have hno' : ∀ s ∈ liftSource h '' J,
      ¬ ∃ Q : InfiniteColouredOccurrenceWord (liftFamily h W) (liftFamily h Y),
        Q.IsIntervalSafe ∧ Q.vertex 0 = s.1 := by
    rintro _ ⟨s, hs, rfl⟩
    exact no_safeInfinite_liftFamily h (hno s hs)
  have hnonterminal' : ∀ s ∈ liftSource h '' J,
      s.1 ∉ (completeWeb Gamma).terminalFrontier (liftFamily h W) := by
    rintro _ ⟨s, hs, rfl⟩
    simpa only [liftSource, liftFamily_terminalFrontier] using hnonterminal s hs
  have hresult := hall_nonterminal_of_auxiliaryAdj
    (liftFamily_isWarp h hW) (liftFamily_isWarp h hY)
    (liftFamily_finiteCharacter h hWfin) (liftFamily_finiteCharacter h hYfin)
    hsource' hterminal' hinternal' (hJ.image (liftSource h)) hno' hnonterminal'
    (fun _ _ _ _ ↦ True.intro)
  simpa only [safeTerminalUnion_liftSource,
    Set.ncard_image_of_injective J (liftSource_injective h)] using hresult

/-- The singleton terminal-source rows are included in the conclusion. -/
theorem hall
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    (hinternal : InternalReferenceEdges W Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) :
    J.ncard ≤ (safeTerminalUnion J).ncard := by
  apply (hall_iff_nonterminalSources hW hY hWfin hYfin hJ hno).mpr
  exact hall_nonterminal hW hY hWfin hYfin hsource hterminal hinternal
    (hJ.subset (nonterminalSources_subset J)) (fun s hs ↦ hno s hs.1) (fun _ hs ↦ hs.2)

/-- The real subdivided graph supplies the internal-edge property. -/
theorem hall_of_subdivision
    (hsub : Blueprint.HasHereditarySubdivisionIncidence Gamma.graph)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {J : Set (ExposedInitial W Y)} (hJ : J.Finite)
    (hno : ∀ s ∈ J, ¬ ∃ Q : InfiniteColouredOccurrenceWord W Y,
      Q.IsIntervalSafe ∧ Q.vertex 0 = s.1) :
    J.ncard ≤ (safeTerminalUnion J).ncard := by
  apply hall hW hY hWfin hYfin hsource hterminal _ hJ hno
  intro a b he ha hb hbI haT
  exact ColouredSafeSubdivisionReferenceContact.referenceEdge_of_internal_pure_subdivision
    hY hYfin (hsub (familyEdges_subset_adj W he)) ha hb hbI haT

#print axioms hall_nonterminal_of_auxiliaryAdj
#print axioms hall_nonterminal
#print axioms hall
#print axioms hall_of_subdivision

end Erdos599.Alternating.ColouredSafeInternalReferenceHall
