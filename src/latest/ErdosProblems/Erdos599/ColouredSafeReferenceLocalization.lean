/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceTransport
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Localizing native reference incidences and intervals

For a roof-captured occurrence, every removed global reference edge already
belongs to the selected stage. Local terminal purity then follows from
global contact removal: a new forward edge cannot leave a stage terminal,
since its global reference successor would have to be removed locally.
These are genuine reflection statements, not an assumption that the
limiting warp has finite character.
-/

noncomputable section

namespace Erdos599

open Cardinal Set DirectedPath Alternating Ladder Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace Blueprint.ReferenceSubpathEmbedding

private theorem support_subset_of_nonempty_edges_subset
    {p q : Gamma.DPath} (hnonempty : p.edgeSet.Nonempty)
    (hedges : p.edgeSet ⊆ q.edgeSet) : p.support ⊆ q.support := by
  cases p with
  | inl p =>
    have hne : p.start ≠ p.finish := by
      intro heq
      have hempty : ∀ {x y : V} (w : Walk Gamma.graph x y),
          w.IsPath → x = y → w.edgeSet = ∅ := by
        intro x y w hw hxy
        cases w with
        | nil => rfl
        | cons _ q =>
          exact False.elim ((List.nodup_cons.1 hw).1 (hxy ▸ q.end_mem_support))
      exact hnonempty.ne_empty (hempty p.walk p.isPath heq)
    intro x hx
    by_cases hxf : x = p.finish
    · obtain ⟨y, hyx⟩ := FinitePath.exists_edge_to_of_mem_of_ne_start p hx
        (fun hxs ↦ hne (hxs.symm.trans hxf))
      exact (q.edgeSet_subset_support_prod (hedges hyx)).2
    · obtain ⟨y, hxy⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish p hx hxf
      exact (q.edgeSet_subset_support_prod (hedges hxy)).1
  | inr r =>
    rintro x ⟨n, rfl⟩
    exact (q.edgeSet_subset_support_prod (hedges ⟨n, rfl⟩)).1

/-- A removed relation covered by the local members has interval convexity
locally whenever it has interval convexity on the global owners. -/
theorem edgeIntervals_local
    {Local Global : Set Gamma.DPath}
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {R : Set (V × V)} (hR : R ⊆ familyEdges Local)
    (hinterval : ∀ p ∈ Global, IsEdgeInterval (R ∩ p.edgeSet) p) :
    ∀ p ∈ Local, IsEdgeInterval (R ∩ p.edgeSet) p := by
  intro p hp
  by_cases hempty : R ∩ p.edgeSet = ∅
  · exact Or.inl hempty
  have heq := E.removed_inter_owner_eq hR (⟨p, hp⟩ : Local)
  have hglobal := hinterval (E.owner ⟨p, hp⟩).1 (E.owner ⟨p, hp⟩).2
  rcases hglobal with hnone | ⟨q, _hqGlobal, hq⟩
  · exact False.elim (hempty (heq.symm.trans hnone))
  · have hlocal : R ∩ p.edgeSet = q.edgeSet := heq.symm.trans hq
    have hnonempty : q.edgeSet.Nonempty := by
      rw [← hlocal]
      exact Set.nonempty_iff_ne_empty.mpr hempty
    have hedge : q.edgeSet ⊆ p.edgeSet := by
      rw [← hlocal]
      exact Set.inter_subset_right
    exact Or.inr ⟨q, ⟨support_subset_of_nonempty_edges_subset hnonempty hedge,
      hedge⟩, hlocal⟩

end Blueprint.ReferenceSubpathEmbedding

namespace ColouredSafeReferenceLocalization

open DWeb.KappaLadder.Deferred ColouredSafeReferenceTransport

variable {kappa : Cardinal.{u}} {L : Gamma.KappaLadder kappa} {a : Stage kappa}

theorem initialSet_stage_subset_limit (hL : HalfwayGeometry L) :
    Gamma.initialSet (L.warpAt a) ⊆ Gamma.initialSet L.limitWarp := by
  rintro x ⟨p, hp, hpx⟩
  refine ⟨hL.limitOwner a ⟨p, hp⟩, hL.limitOwner_mem a ⟨p, hp⟩, ?_⟩
  exact (Gamma.extends_initial (hL.extends_limitOwner a ⟨p, hp⟩)).symm.trans hpx

/-- Global endpoint purity and local ownership of every removed edge force
the required local endpoint purity. The terminal argument uses an actual
global successor, not a converse monotonicity of terminal sets. -/
theorem endpointPure_local_of_removed_edges_local
    (hL : HalfwayGeometry L) {F R : Set (V × V)}
    (hR : R ⊆ familyEdges (L.warpAt a))
    (hout : ∀ {x y z}, (x, y) ∈ F →
      (x, z) ∈ familyEdges L.limitWarp → (x, z) ∈ R)
    (hpure : ∀ {x y}, (x, y) ∈ F →
      y ∉ Gamma.initialSet L.limitWarp ∧ x ∉ Gamma.terminalFrontier L.limitWarp) :
    ∀ {x y}, (x, y) ∈ F →
      y ∉ Gamma.initialSet (L.warpAt a) ∧ x ∉ Gamma.terminalFrontier (L.warpAt a) := by
  intro x y hxy
  refine ⟨fun hy ↦ (hpure hxy).1 (initialSet_stage_subset_limit hL hy), ?_⟩
  intro hx
  have hlocal := hx
  have hstageWarp : Gamma.IsWarp (L.warpAt a) :=
    hL.warpStages (Stage.toExtended a)
  have hlimitWarp : Gamma.IsWarp L.limitWarp :=
    hL.warpStages (Ladder.finalStage kappa)
  rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
    hstageWarp] at hlocal
  have hxGlobal : x ∈ Gamma.vertexSet L.limitWarp := by
    obtain ⟨p, hp, hxp⟩ := hlocal.1
    exact ⟨(hL.stageReferenceEmbedding a).owner ⟨p, hp⟩,
      ((hL.stageReferenceEmbedding a).owner ⟨p, hp⟩).2,
      (hL.stageReferenceEmbedding a).support_subset ⟨p, hp⟩ hxp⟩
  have hglobalOut : HasOutgoing (familyEdges L.limitWarp) x := by
    by_contra hno
    apply (hpure hxy).2
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
      hlimitWarp]
    exact ⟨hxGlobal, hno⟩
  obtain ⟨z, hxz⟩ := hglobalOut
  exact hlocal.2 ⟨z, hR (hout hxy hxz)⟩

end ColouredSafeReferenceLocalization

open ColouredSafeReferenceTransport ColouredSafeReferenceLocalization

namespace Alternating.FiniteColouredOccurrenceWord

variable {W : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}

theorem backwardEdges_subset_stage_of_roof
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Q.backwardEdges ⊆ familyEdges (L.warpAt a) := by
  intro e he
  exact incoming_referenceEdge_reflect hL (Q.backwardEdges_subset_familyEdges he)
    (hRoof (Q.backwardEdges_endpoints_mem_vertexSet he).2)

/-- Literal restriction of a roof-captured finite occurrence to its stage
reference. Neither the word nor its forward-warp parameter is changed. -/
def retypeStageReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    FiniteColouredOccurrenceWord W (L.warpAt a) where
  length := Q.length
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i with
    | forward => simpa only [hd] using Q.actualEdge_spec i
    | backward =>
      apply incoming_referenceEdge_reflect hL
        (by simpa only [hd] using Q.actualEdge_spec i)
      exact hRoof ⟨i.castSucc, rfl⟩
  occurrence_injective := Q.occurrence_injective

@[simp] theorem retypeStageReference_forwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeStageReference hL hRoof).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeStageReference_backwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeStageReference hL hRoof).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeStageReference_vertexSet
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeStageReference hL hRoof).vertexSet = Q.vertexSet := rfl

theorem IsIntervalSafe.retypeStageReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : FiniteColouredOccurrenceWord W L.limitWarp} (hQ : Q.IsIntervalSafe)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeStageReference hL hRoof).IsIntervalSafe := by
  have hR := Q.backwardEdges_subset_stage_of_roof hL hRoof
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    exact hQ.incoming_removed hxy ((hL.stageReferenceEmbedding a).familyEdges_subset hby)
  · intro x y b hxy hxb
    exact hQ.outgoing_removed hxy ((hL.stageReferenceEmbedding a).familyEdges_subset hxb)
  · exact (hL.stageReferenceEmbedding a).edgeIntervals_local hR hQ.intervals
  · exact endpointPure_local_of_removed_edges_local hL hR
      hQ.outgoing_removed hQ.endpoint_pure

end Alternating.FiniteColouredOccurrenceWord

namespace Alternating.InfiniteColouredOccurrenceWord

variable {W : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}

theorem backwardEdges_endpoints_mem_vertexSet {Y : Set Gamma.DPath}
    (Q : InfiniteColouredOccurrenceWord W Y) {e : V × V}
    (he : e ∈ Q.backwardEdges) : e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  obtain ⟨i, rfl⟩ := he
  rw [Q.backwardEdge_eq]
  exact ⟨⟨i.1 + 1, rfl⟩, ⟨i.1, rfl⟩⟩

theorem backwardEdges_subset_stage_of_roof
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Q.backwardEdges ⊆ familyEdges (L.warpAt a) := by
  intro e he
  exact incoming_referenceEdge_reflect hL (Q.backwardEdges_subset_familyEdges he)
    (hRoof (Q.backwardEdges_endpoints_mem_vertexSet he).2)

/-- Infinite native localization also retains the complete occurrence
stream; it does not truncate to a finite prefix. -/
def retypeStageReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    InfiniteColouredOccurrenceWord W (L.warpAt a) where
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hd : Q.direction i with
    | forward => simpa only [hd] using Q.actualEdge_spec i
    | backward =>
      apply incoming_referenceEdge_reflect hL
        (by simpa only [hd] using Q.actualEdge_spec i)
      exact hRoof ⟨i, rfl⟩
  occurrence_injective := Q.occurrence_injective

@[simp] theorem retypeStageReference_forwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeStageReference hL hRoof).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeStageReference_backwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeStageReference hL hRoof).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeStageReference_vertexSet
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W L.limitWarp)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeStageReference hL hRoof).vertexSet = Q.vertexSet := rfl

theorem IsIntervalSafe.retypeStageReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : InfiniteColouredOccurrenceWord W L.limitWarp} (hQ : Q.IsIntervalSafe)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeStageReference hL hRoof).IsIntervalSafe := by
  have hR := Q.backwardEdges_subset_stage_of_roof hL hRoof
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    exact hQ.incoming_removed hxy ((hL.stageReferenceEmbedding a).familyEdges_subset hby)
  · intro x y b hxy hxb
    exact hQ.outgoing_removed hxy ((hL.stageReferenceEmbedding a).familyEdges_subset hxb)
  · exact (hL.stageReferenceEmbedding a).edgeIntervals_local hR hQ.intervals
  · exact endpointPure_local_of_removed_edges_local hL hR
      hQ.outgoing_removed hQ.endpoint_pure

end Alternating.InfiniteColouredOccurrenceWord

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

variable {current : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa} {s : V}

def retypeStageReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    CurrentSafeOccurrence current (L.warpAt a) s := by
  cases A with
  | infinite Q hsafe hfirst =>
    exact .infinite (Q.retypeStageReference hL hRoof)
      (hsafe.retypeStageReference hL hRoof) hfirst
  | finite t Q hsafe hfirst hlast =>
    exact .finite t (Q.retypeStageReference hL hRoof)
      (hsafe.retypeStageReference hL hRoof) hfirst hlast

@[simp] theorem retypeStageReference_forwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeStageReference hL hRoof).forwardEdges = A.forwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeStageReference_backwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeStageReference hL hRoof).backwardEdges = A.backwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeStageReference_vertexSet
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeStageReference hL hRoof).vertexSet = A.vertexSet := by
  cases A <;> rfl

@[simp] theorem retypeStageReference_terminal?
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current L.limitWarp s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeStageReference hL hRoof).terminal? = A.terminal? := by
  cases A <;> rfl

end ColouredSafeReverseReachability.CurrentSafeOccurrence

#print axioms Blueprint.ReferenceSubpathEmbedding.edgeIntervals_local
#print axioms ColouredSafeReferenceLocalization.endpointPure_local_of_removed_edges_local
#print axioms Alternating.FiniteColouredOccurrenceWord.IsIntervalSafe.retypeStageReference
#print axioms Alternating.InfiniteColouredOccurrenceWord.IsIntervalSafe.retypeStageReference
#print axioms ColouredSafeReverseReachability.CurrentSafeOccurrence.retypeStageReference

end Erdos599
