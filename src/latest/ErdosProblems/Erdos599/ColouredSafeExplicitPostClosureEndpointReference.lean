/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointReference
import ErdosProblems.Erdos599.ColouredSafeExplicitPostClosureClassification

/-!
# Promoting the unchanged word after excluding its endpoint owners

Only the reference owners through the displayed endpoints are excluded.
Whole-reference closure proves that these owners lie inside the cut, while
every owner of a local outside interval remains. Actual pointwise contact
confinement then promotes the same finite or infinite occurrence, preserving
both coloured relations, its carrier, and its optional terminal.

This is not a global-reference imaginary-edge assertion. Endpoint-dependent
hammock closure and its compatible grounding remain separate constructions.
-/

noncomputable section

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath
open _root_.Erdos599.Alternating
open ColouredSafeReverseReachability ColouredSafeMovingStages
open ColouredSafeHammock
open FracturedFixedSafeAssignment

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {alpha : Ladder.Stage (succ kappa)}
variable {seed : Set V} {z s : V} {e : Option V} {R : LimitClosure C seed}

namespace StagePostClosureIntervalTransaction

/-- A local outside interval's complete limiting owner also avoids the
closed set; otherwise the local interval's own initial gives a contradiction. -/
theorem outsideIntervalOwner_disjoint_closed
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (q : outsideReference T.intervalReference R.closedSet) :
    Disjoint (T.outsideIntervalGlobalReferenceEmbedding.owner q).1.support R.closedSet := by
  apply Set.disjoint_left.mpr
  intro x hxp hxX
  have hpX := R.reference_closed
    (T.outsideIntervalGlobalReferenceEmbedding.owner q).1
    (T.outsideIntervalGlobalReferenceEmbedding.owner q).2 ⟨x, hxp, hxX⟩
  exact Set.disjoint_left.mp q.2.2 q.1.initial_mem_support
    (hpX (T.outsideIntervalGlobalReferenceEmbedding.support_subset q q.1.initial_mem_support))

/-- The same injective owner map has image in the endpoint-pruned reference.
No new reference owners are chosen. -/
def outsideIntervalEndpointReferenceEmbedding
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (s : V) (e : Option V) (hendpoints : endpoints s e ⊆ R.closedSet) :
    ReferenceSubpathEmbedding Gamma (outsideReference T.intervalReference R.closedSet)
      (ColouredSafeEndpointReference.reference C.ladder.limitWarp s e) where
  owner q := ⟨(T.outsideIntervalGlobalReferenceEmbedding.owner q).1,
    (T.outsideIntervalGlobalReferenceEmbedding.owner q).2,
    (T.outsideIntervalOwner_disjoint_closed q).mono_right hendpoints⟩
  owner_injective := by
    intro q r hqr
    apply T.outsideIntervalGlobalReferenceEmbedding.owner_injective
    apply Subtype.ext
    exact congrArg
      (fun p : ColouredSafeEndpointReference.reference C.ladder.limitWarp s e ↦ p.1) hqr
  support_subset q := T.outsideIntervalGlobalReferenceEmbedding.support_subset q
  edgeSet_subset q := T.outsideIntervalGlobalReferenceEmbedding.edgeSet_subset q
  global_isWarp := ColouredSafeEndpointReference.isWarp
    T.outsideIntervalGlobalReferenceEmbedding.global_isWarp

/-- Every contact with the endpoint-pruned reference is outside the cut,
so the actual pointwise survivor-interval theorem applies. -/
theorem outsideEndpointReference_forwardContactConfined
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideFracturedWarp T.interval.ambientInterval R.closedSet)
    (A : CurrentSafeOccurrence F.holes.edgeWarp
      (outsideReference T.intervalReference R.closedSet) s)
    (hendpoints : endpoints s A.terminal? ⊆ R.closedSet)
    (hcap : A.vertexSet ∩ R.closedSet ⊆ endpoints s A.terminal?) :
    (T.outsideIntervalEndpointReferenceEmbedding s A.terminal? hendpoints).ForwardContactConfined
      A.forwardEdges := by
  intro x y hxy
  have hrow := F.occurrence_forwardEdges_subset_original A hxy
  have hends : x ∈ A.vertexSet ∧ y ∈ A.vertexSet := by
    cases A with
    | infinite Q => exact Q.forwardEdges_endpoints_mem_vertexSet hxy
    | finite t Q => exact Q.forwardEdges_endpoints_mem_vertexSet hxy
  have contact_local {w : V} (hwA : w ∈ A.vertexSet)
      (hwRef : w ∈ Gamma.vertexSet
        (ColouredSafeEndpointReference.reference C.ladder.limitWarp s A.terminal?))
      (hwRow : w ∈ Gamma.vertexSet T.interval.ambientInterval) :
      w ∈ Gamma.vertexSet (outsideReference T.intervalReference R.closedSet) := by
    have hwNotClosed : w ∉ R.closedSet := by
      intro hwX
      exact Set.disjoint_left.mp ColouredSafeEndpointReference.vertexSet_disjoint_endpoints
        hwRef (hcap ⟨hwA, hwX⟩)
    obtain ⟨p, hp, hwp⟩ := hwRef
    exact T.globalContact_mem_outsideIntervalReference hwNotClosed ⟨p, hp.1, hwp⟩ hwRow
  exact ⟨fun hx ↦ contact_local hends.1 hx (familyEdges_subset_vertexSet_prod _ hrow).1,
    fun hy ↦ contact_local hends.2 hy (familyEdges_subset_vertexSet_prod _ hrow).2⟩

/-- Promotion after excluding endpoint owners preserves the entire literal
word data. In particular no new finite terminal is selected. -/
theorem exists_endpointReferenceOccurrence
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideFracturedWarp T.interval.ambientInterval R.closedSet)
    (A : CurrentSafeOccurrence F.holes.edgeWarp
      (outsideReference T.intervalReference R.closedSet) s)
    (hendpoints : endpoints s A.terminal? ⊆ R.closedSet)
    (hcap : A.vertexSet ∩ R.closedSet ⊆ endpoints s A.terminal?) :
    ∃ B : CurrentSafeOccurrence T.interval.ambientInterval
        (ColouredSafeEndpointReference.reference C.ladder.limitWarp s A.terminal?) s,
      B.forwardEdges = A.forwardEdges ∧ B.backwardEdges = A.backwardEdges ∧
      B.vertexSet = A.vertexSet ∧ B.terminal? = A.terminal? := by
  let E := T.outsideIntervalEndpointReferenceEmbedding s A.terminal? hendpoints
  let hLocal : Gamma.IsWarp (outsideReference T.intervalReference R.closedSet) :=
    outsideReference_isWarp T.intervalReference_isLinkageBetween.isWarp
  let Q := A.retypeReferenceEmbedding E hLocal
    (T.outsideEndpointReference_forwardContactConfined F A hendpoints hcap)
  let B := Q.retypeForward (F.occurrence_forwardEdges_subset_original Q)
  exact ⟨B, by simp [B, Q], by cases A <;> rfl, by simp [B, Q], by simp [B, Q]⟩

/-- Every actual selected word admits endpoint-reference promotion, with
actual roof containment, endpoint exposure, and common-original-owner
semantics in its degenerate finite case. -/
theorem selected_endpointReferenceOccurrence
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (A : Assignment F.outside.holes (outsideReference T.intervalReference R.closedSet))
    (hgeometry : ∀ s, HasCutGeometry R.closedSet (A.assigned s))
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)) :
    ∃ B : CurrentSafeOccurrence T.interval.ambientInterval
        (ColouredSafeEndpointReference.reference C.ladder.limitWarp s.1
          (A.assigned s).terminal?) s.1,
      B.forwardEdges = (A.assigned s).forwardEdges ∧
      B.backwardEdges = (A.assigned s).backwardEdges ∧
      B.vertexSet = (A.assigned s).vertexSet ∧ B.terminal? = (A.assigned s).terminal? ∧
      B.vertexSet ⊆ Gamma.roof (C.ladder.frontier R.later.stage) ∧
      ∀ t, B.terminal? = some t → s.1 ≠ t → B.HasFiniteSwitchedPathTo t →
        ∃ p ∈ T.interval.ambientInterval, s.1 ∈ p.support ∧ t ∈ p.support := by
  have hEnd : endpoints s.1 (A.assigned s).terminal? ⊆ R.closedSet := by
    rintro w (hws | hwt)
    · exact hws ▸ T.uncovered_initials_subset_closedSet F.outside s.2
    · have ht := A.finite_terminal s hwt
      exact T.finite_terminal_mem_closedSet F.outside ht.1 ht.2
  have hcap : (A.assigned s).vertexSet ∩ R.closedSet ⊆
      endpoints s.1 (A.assigned s).terminal? := by
    cases ht : (A.assigned s).terminal? with
    | none => simpa only [endpoints_none] using (hgeometry s).infinite_cut ht
    | some t => simpa only [endpoints_some] using (hgeometry s).finite_cut t ht
  obtain ⟨B, hBF, hBB, hBV, hBT⟩ :=
    T.exists_endpointReferenceOccurrence F.outside (A.assigned s) hEnd hcap
  refine ⟨B, hBF, hBB, hBV, hBT, ?_, ?_⟩
  · rw [hBV]
    exact T.outsideOccurrence_vertices_subset_capturedRoof F s (A.assigned s)
  · intro t ht hne hdeg
    exact B.finiteDegenerate_endpoints_same_forward_owner
      T.interval.ambientInterval_linkage.isWarp
      (ColouredSafeEndpointReference.isWarp T.outsideIntervalGlobalReferenceEmbedding.global_isWarp)
      ht hne ColouredSafeEndpointReference.source_off
      (ColouredSafeEndpointReference.terminal_off (hBT.symm.trans ht)) hdeg

/-- A genuine simultaneous family retaining its original terminal-injective
assignment. Each promoted word explicitly records its own pruned reference. -/
structure EndpointReferenceAssignment
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet) where
  original : Assignment F.outside.holes (outsideReference T.intervalReference R.closedSet)
  geometry : ∀ s, HasCutGeometry R.closedSet (original.assigned s)
  word : ∀ s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet),
    CurrentSafeOccurrence T.interval.ambientInterval
      (ColouredSafeEndpointReference.reference C.ladder.limitWarp s.1
        (original.assigned s).terminal?) s.1
  forward_eq : ∀ s, (word s).forwardEdges = (original.assigned s).forwardEdges
  backward_eq : ∀ s, (word s).backwardEdges = (original.assigned s).backwardEdges
  vertices_eq : ∀ s, (word s).vertexSet = (original.assigned s).vertexSet
  terminal_eq : ∀ s, (word s).terminal? = (original.assigned s).terminal?

namespace EndpointReferenceAssignment

variable {T : StagePostClosureIntervalTransaction C alpha seed z R}
variable {F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
  (Gamma := Gamma) T.interval.ambientInterval R.closedSet}

theorem finite_terminals_injective (A : EndpointReferenceAssignment T F)
    {s r : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)}
    {t : V} (hs : (A.word s).terminal? = some t) (hr : (A.word r).terminal? = some t) :
    s = r :=
  A.original.finite_terminals_injective
    ((A.terminal_eq s).symm.trans hs) ((A.terminal_eq r).symm.trans hr)

theorem finiteEdges_eq (A : EndpointReferenceAssignment T F) :
    {p : V × V | ∃ s, (A.word s).terminal? = some p.2 ∧ s.1 = p.1} =
      A.original.toCompressed.finiteEdges := by
  ext p
  simp only [CompressedFracturedAssignment.finiteEdges, A.terminal_eq]
  rfl

theorem word_vertices_subset_capturedRoof (A : EndpointReferenceAssignment T F)
    (s : Source F.outside.holes (outsideReference T.intervalReference R.closedSet)) :
    (A.word s).vertexSet ⊆ Gamma.roof (C.ladder.frontier R.later.stage) := by
  rw [A.vertices_eq]
  exact T.outsideOccurrence_vertices_subset_capturedRoof F s (A.original.assigned s)

end EndpointReferenceAssignment

/-- All post-closure sources, including covered original-reference
endpoints, receive the unchanged selected word with endpoint owners removed.
No family of independently appended reference suffixes is used. -/
theorem exists_endpointReferenceAssignment
    (T : StagePostClosureIntervalTransaction C alpha seed z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet)
    (hsub : HasHereditarySubdivisionIncidence Gamma.graph) :
    Nonempty (EndpointReferenceAssignment T F) := by
  obtain ⟨A, hA, _hsource, _hterminal, _hcases⟩ := T.exists_fixedOutsideAssignment F hsub
  let word := fun s ↦ Classical.choose (T.selected_endpointReferenceOccurrence F A hA s)
  have hword := fun s ↦ Classical.choose_spec (T.selected_endpointReferenceOccurrence F A hA s)
  exact ⟨{
    original := A
    geometry := hA
    word := word
    forward_eq := fun s ↦ (hword s).1
    backward_eq := fun s ↦ (hword s).2.1
    vertices_eq := fun s ↦ (hword s).2.2.1
    terminal_eq := fun s ↦ (hword s).2.2.2.1 }⟩

end StagePostClosureIntervalTransaction

#print axioms StagePostClosureIntervalTransaction.outsideIntervalOwner_disjoint_closed
#print axioms StagePostClosureIntervalTransaction.exists_endpointReferenceOccurrence
#print axioms StagePostClosureIntervalTransaction.selected_endpointReferenceOccurrence
#print axioms StagePostClosureIntervalTransaction.exists_endpointReferenceAssignment
#print axioms StagePostClosureIntervalTransaction.EndpointReferenceAssignment.finiteEdges_eq

end Erdos599.Blueprint.LinkageBlueprint

