/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceRestriction
import ErdosProblems.Erdos599.ColouredSafeAmbientOccurrence
import ErdosProblems.Erdos599.DeferredStageReferenceEmbedding
import ErdosProblems.Erdos599.HalfwayDeferredReferenceRoofIncidence
import ErdosProblems.Erdos599.SafeLinkGround

/-!
# Native safe-occurrence transport to a limiting reference

A native coloured occurrence is indexed by a literal reference family.
This file retypes a word from a full deferred-ladder stage to the limiting
warp without changing its chronology, carrier, or colour relations.

The essential geometric hypothesis is that the word is contained in the
selected stage roof.  It reflects every limiting-reference contact to a
stage prefix.  Incoming incidence is supplied directly by no-late-entry;
outgoing incidence then follows from local endpoint purity and uniqueness in
the limiting warp.  The limiting warp may contain rays throughout.
-/

noncomputable section

namespace Erdos599

open Cardinal Order Set
open DirectedPath Alternating Ladder Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Blueprint.ReferenceSubpathEmbedding

variable {Local Global : Set Gamma.DPath}

/-- A literal removed relation sees the same edges on a local member and on
its global owner.  Unlike the older `AltPath` lemma, this only asks that the
removed relation be covered by the local family. -/
theorem removed_inter_owner_eq
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {R : Set (V × V)} (hR : R ⊆ familyEdges Local) (p : Local) :
    R ∩ (E.owner p).1.edgeSet = R ∩ p.1.edgeSet := by
  apply Set.Subset.antisymm
  · rintro e ⟨heR, heOwner⟩
    have heLocal := hR heR
    simp only [familyEdges, Set.mem_iUnion] at heLocal
    obtain ⟨q, hq, heq⟩ := heLocal
    let qs : Local := ⟨q, hq⟩
    have hqp : qs = p :=
      E.eq_of_owner_support_inter
        (E.support_subset qs (q.edgeSet_subset_support_prod heq).1)
        ((E.owner p).1.edgeSet_subset_support_prod heOwner).1
    refine ⟨heR, ?_⟩
    have hval : q = p.1 := congrArg Subtype.val hqp
    rwa [← hval]
  · rintro e ⟨heR, hep⟩
    exact ⟨heR, E.edgeSet_subset p hep⟩

/-- Local edge intervals of an arbitrary removed relation transport through
an injective subpath embedding.  No finiteness of the global owners is used. -/
theorem edgeIntervals_global
    (E : ReferenceSubpathEmbedding Gamma Local Global)
    {R : Set (V × V)} (hR : R ⊆ familyEdges Local)
    (hinterval : ∀ p ∈ Local, IsEdgeInterval (R ∩ p.edgeSet) p) :
    ∀ p ∈ Global, IsEdgeInterval (R ∩ p.edgeSet) p := by
  classical
  intro p hp
  by_cases hempty : R ∩ p.edgeSet = ∅
  · exact Or.inl hempty
  obtain ⟨e, heR, hep⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  have heLocal := hR heR
  simp only [familyEdges, Set.mem_iUnion] at heLocal
  obtain ⟨q, hq, heq⟩ := heLocal
  let qs : Local := ⟨q, hq⟩
  have howner : (E.owner qs).1 = p := by
    apply DWeb.IsWarp.eq_of_mem_support E.global_isWarp (E.owner qs).2 hp
    · exact E.support_subset qs (q.edgeSet_subset_support_prod heq).1
    · exact (p.edgeSet_subset_support_prod hep).1
  have hinter : R ∩ p.edgeSet = R ∩ q.edgeSet := by
    rw [← howner]
    exact E.removed_inter_owner_eq hR qs
  rw [hinter]
  rcases hinterval q hq with hnone | ⟨f, hfq, hfinterval⟩
  · exact Or.inl hnone
  · refine Or.inr ⟨f, ⟨?_, ?_⟩, hfinterval⟩
    · rw [← howner]
      exact hfq.1.trans (E.support_subset qs)
    · rw [← howner]
      exact hfq.2.trans (E.edgeSet_subset qs)

end Blueprint.ReferenceSubpathEmbedding

namespace ColouredSafeReferenceTransport

open DWeb.KappaLadder.Deferred

variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}

private theorem pathFamilyEdgeSet_eq_familyEdges
    (Gamma : DWeb V) (W : Set Gamma.DPath) :
    Gamma.pathFamilyEdgeSet W = familyEdges W := by
  ext e
  simp only [DWeb.pathFamilyEdgeSet, familyEdges, Set.mem_ofPred_eq,
    Set.mem_iUnion]
  constructor <;> rintro ⟨p, hp, he⟩ <;> exact ⟨p, hp, he⟩

/-- Every limiting-reference point still inside the selected roof belongs
to a full member of the selected stage. -/
theorem limitWarp_inter_roof_subset_warpAt
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.vertexSet L.limitWarp ∩ Gamma.roof (L.frontier a) ⊆
      Gamma.vertexSet (L.warpAt a) := by
  intro x hx
  rcases vertexSet_limitWarp_inter_roof_subset_essential_or_inessential
      hL a hx with hxEssential | hxInessential
  · obtain ⟨p, hp, hxp⟩ := hxEssential
    exact ⟨p, hp.1, hxp⟩
  · obtain ⟨p, hp, hxp⟩ := hxInessential
    exact ⟨p, hp.1, hxp⟩

/-- Carrier confinement follows pointwise from roof containment. -/
theorem contactConfined_of_vertexSet_subset_roof
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {X : Set V} (hX : X ⊆ Gamma.roof (L.frontier a)) :
    X ∩ Gamma.vertexSet L.limitWarp ⊆ Gamma.vertexSet (L.warpAt a) := by
  rintro x ⟨hxX, hxLimit⟩
  exact limitWarp_inter_roof_subset_warpAt hL ⟨hxLimit, hX hxX⟩

/-- A limiting incoming edge at a roofed point is already a stage edge. -/
theorem incoming_referenceEdge_reflect
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x y : V} (hxy : (x, y) ∈ familyEdges L.limitWarp)
    (hyRoof : y ∈ Gamma.roof (L.frontier a)) :
    (x, y) ∈ familyEdges (L.warpAt a) := by
  rw [← pathFamilyEdgeSet_eq_familyEdges] at hxy ⊢
  exact pathFamilyEdgeSet_of_head_mem_roof_frontier hL a
    kappa.ord le_rfl a.2.le hxy hyRoof

private theorem exists_outgoing_familyEdge_of_mem_not_terminal
    {W : Set Gamma.DPath} {x : V} (hx : x ∈ Gamma.vertexSet W)
    (hterminal : x ∉ Gamma.terminalFrontier W) :
    ∃ y, (x, y) ∈ familyEdges W := by
  obtain ⟨p, hpW, hxp⟩ := hx
  have hpterminal : Gamma.terminal? p ≠ some x := by
    intro hp
    exact hterminal ⟨p, hpW, hp⟩
  rcases p with p | r
  · have hxfinish : x ≠ p.finish := by
      intro hx
      apply hpterminal
      simp [hx]
    obtain ⟨y, hxy⟩ :=
      FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        p hxp hxfinish
    exact ⟨y, Set.mem_iUnion.2 ⟨Sum.inl p,
      Set.mem_iUnion.2 ⟨hpW, hxy⟩⟩⟩
  · obtain ⟨n, rfl⟩ := hxp
    refine ⟨r (n + 1), Set.mem_iUnion.2 ⟨Sum.inr r,
      Set.mem_iUnion.2 ⟨hpW, ?_⟩⟩⟩
    exact ⟨n, rfl⟩

/-- Local endpoint purity reflects a limiting outgoing edge at a roofed
forward contact. -/
theorem outgoing_referenceEdge_reflect
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {F : Set (V × V)}
    (hlocalPure : ∀ {x y}, (x, y) ∈ F →
      x ∉ Gamma.terminalFrontier (L.warpAt a))
    {x y z : V} (hxyF : (x, y) ∈ F)
    (hxRoof : x ∈ Gamma.roof (L.frontier a))
    (hxzLimit : (x, z) ∈ familyEdges L.limitWarp) :
    (x, z) ∈ familyEdges (L.warpAt a) := by
  have hxLimit : x ∈ Gamma.vertexSet L.limitWarp :=
    familyEdges_subset_vertexSet_prod L.limitWarp hxzLimit |>.1
  have hxStage : x ∈ Gamma.vertexSet (L.warpAt a) :=
    limitWarp_inter_roof_subset_warpAt hL ⟨hxLimit, hxRoof⟩
  obtain ⟨w, hxwStage⟩ :=
    exists_outgoing_familyEdge_of_mem_not_terminal hxStage
      (hlocalPure hxyF)
  have hxwLimit := (hL.stageReferenceEmbedding a).familyEdges_subset hxwStage
  have hwz : w = z :=
    (IsWarp.familyEdges_biUnique
      (hL.warpStages (Ladder.finalStage kappa))).2 hxwLimit hxzLimit
  simpa only [hwz] using hxwStage

/-- Limiting initials which lie in the selected roof are stage initials. -/
theorem initialSet_reflect_of_mem_roof
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x : V} (hx : x ∈ Gamma.initialSet L.limitWarp)
    (hxRoof : x ∈ Gamma.roof (L.frontier a)) :
    x ∈ Gamma.initialSet (L.warpAt a) := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hpRoof : p.initial ∈ Gamma.roof (L.frontier a) := by
    rwa [hpx]
  obtain ⟨q, hq, hqp⟩ :=
    exists_warpAt_prefix_of_limitComponent_initial_mem_roof hL a hp hpRoof
  refine ⟨q, hq, ?_⟩
  exact (Gamma.extends_initial hqp).trans hpx

/-- Limiting finite terminals which lie in the selected roof are already
terminals of their stage prefixes. -/
theorem terminalFrontier_reflect_of_mem_roof
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {x : V} (hx : x ∈ Gamma.terminalFrontier L.limitWarp)
    (hxRoof : x ∈ Gamma.roof (L.frontier a)) :
    x ∈ Gamma.terminalFrontier (L.warpAt a) := by
  obtain ⟨p, hp, hpx⟩ := hx
  have hpInitialRoof : p.initial ∈ Gamma.roof (L.frontier a) :=
    limitComponent_initial_mem_roof_of_support_mem hL a hp
      (Gamma.terminal_mem_support hpx) hxRoof
  obtain ⟨q, hq, hqp⟩ :=
    exists_warpAt_prefix_of_limitComponent_initial_mem_roof
      hL a hp hpInitialRoof
  have hxq : x ∈ q.support :=
    limitComponent_support_inter_roof_subset_prefix hL a hp hq hqp
      ⟨Gamma.terminal_mem_support hpx, hxRoof⟩
  refine ⟨q, hq, ?_⟩
  rcases p with p | r
  · have hfinish : p.finish = x := Option.some.inj hpx
    have hpfinishq : p.finish ∈ q.support := by
      rw [hfinish]
      exact hxq
    have hterminal :=
      SafeLinkGround.DirectedPath.FinitePath.terminal_eq_of_extends_of_mem_finish
        hqp hpfinishq
    simpa only [hfinish] using hterminal
  · simp at hpx

end ColouredSafeReferenceTransport

open ColouredSafeReferenceTransport

namespace Alternating.FiniteColouredOccurrenceWord

variable {W : Set Gamma.DPath} {L : Gamma.KappaLadder kappa}
variable {a : Stage kappa}

/-- Retype a finite occurrence from a full stage reference to the limiting
reference.  All chronological data and literal colour relations are
definitionally unchanged. -/
def retypeLimitReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W (L.warpAt a)) :
    FiniteColouredOccurrenceWord W L.limitWarp :=
  Q.retypeEdges Set.Subset.rfl (hL.stageReferenceEmbedding a).familyEdges_subset

@[simp] theorem retypeLimitReference_forwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W (L.warpAt a)) :
    (Q.retypeLimitReference hL).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeLimitReference_backwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W (L.warpAt a)) :
    (Q.retypeLimitReference hL).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeLimitReference_vertexSet
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W (L.warpAt a)) :
    (Q.retypeLimitReference hL).vertexSet = Q.vertexSet := rfl

@[simp] theorem retypeLimitReference_vertex
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : FiniteColouredOccurrenceWord W (L.warpAt a))
    (i : Fin (Q.length + 1)) :
    (Q.retypeLimitReference hL).vertex i = Q.vertex i := rfl

/-- Roof-contained finite native safeness transports to the possibly
ray-containing limiting reference. -/
theorem IsIntervalSafe.retypeLimitReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : FiniteColouredOccurrenceWord W (L.warpAt a)}
    (hQ : Q.IsIntervalSafe)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeLimitReference hL).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    change (x, y) ∈ Q.forwardEdges at hxy
    change (b, y) ∈ Q.backwardEdges
    apply hQ.incoming_removed hxy
    apply incoming_referenceEdge_reflect hL hby
    exact hRoof (Q.forwardEdges_endpoints_mem_vertexSet hxy).2
  · intro x y b hxy hxb
    change (x, y) ∈ Q.forwardEdges at hxy
    change (x, b) ∈ Q.backwardEdges
    apply hQ.outgoing_removed hxy
    apply outgoing_referenceEdge_reflect hL
      (fun {_x _y} h ↦ (hQ.endpoint_pure h).2) hxy
      (hRoof (Q.forwardEdges_endpoints_mem_vertexSet hxy).1) hxb
  · intro p hp
    change IsEdgeInterval (Q.backwardEdges ∩ p.edgeSet) p
    exact (hL.stageReferenceEmbedding a).edgeIntervals_global
      Q.backwardEdges_subset_familyEdges hQ.intervals p hp
  · intro x y hxy
    change (x, y) ∈ Q.forwardEdges at hxy
    have hlocal := hQ.endpoint_pure hxy
    have hends := Q.forwardEdges_endpoints_mem_vertexSet hxy
    constructor
    · intro hy
      exact hlocal.1
        (initialSet_reflect_of_mem_roof hL hy (hRoof hends.2))
    · intro hx
      exact hlocal.2
        (terminalFrontier_reflect_of_mem_roof hL hx (hRoof hends.1))

end Alternating.FiniteColouredOccurrenceWord

namespace Alternating.InfiniteColouredOccurrenceWord

variable {W : Set Gamma.DPath} {L : Gamma.KappaLadder kappa}
variable {a : Stage kappa}

/-- Infinite reference retyping, again without changing the word. -/
def retypeLimitReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W (L.warpAt a)) :
    InfiniteColouredOccurrenceWord W L.limitWarp where
  vertex := Q.vertex
  direction := Q.direction
  actualEdge_spec := by
    intro i
    cases hdir : Q.direction i with
    | forward => simpa only [hdir] using Q.actualEdge_spec i
    | backward =>
        apply (hL.stageReferenceEmbedding a).familyEdges_subset
        simpa only [hdir] using Q.actualEdge_spec i
  occurrence_injective := Q.occurrence_injective

@[simp] theorem retypeLimitReference_forwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W (L.warpAt a)) :
    (Q.retypeLimitReference hL).forwardEdges = Q.forwardEdges := rfl

@[simp] theorem retypeLimitReference_backwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W (L.warpAt a)) :
    (Q.retypeLimitReference hL).backwardEdges = Q.backwardEdges := rfl

@[simp] theorem retypeLimitReference_vertexSet
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W (L.warpAt a)) :
    (Q.retypeLimitReference hL).vertexSet = Q.vertexSet := rfl

@[simp] theorem retypeLimitReference_vertex
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (Q : InfiniteColouredOccurrenceWord W (L.warpAt a)) (i : Nat) :
    (Q.retypeLimitReference hL).vertex i = Q.vertex i := rfl

theorem forwardEdges_endpoints_mem_vertexSet
    {Y : Set Gamma.DPath} (Q : InfiniteColouredOccurrenceWord W Y)
    {e : V × V} (he : e ∈ Q.forwardEdges) :
    e.1 ∈ Q.vertexSet ∧ e.2 ∈ Q.vertexSet := by
  obtain ⟨i, rfl⟩ := he
  rw [Q.forwardEdge_eq]
  exact ⟨⟨i.1, rfl⟩, ⟨i.1 + 1, rfl⟩⟩

/-- Roof-contained infinite native safeness transports to the limiting
reference.  In particular, no finite-character assumption is made on it. -/
theorem IsIntervalSafe.retypeLimitReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : InfiniteColouredOccurrenceWord W (L.warpAt a)}
    (hQ : Q.IsIntervalSafe)
    (hRoof : Q.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (Q.retypeLimitReference hL).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x b y hxy hby
    change (x, y) ∈ Q.forwardEdges at hxy
    change (b, y) ∈ Q.backwardEdges
    apply hQ.incoming_removed hxy
    apply incoming_referenceEdge_reflect hL hby
    exact hRoof (Q.forwardEdges_endpoints_mem_vertexSet hxy).2
  · intro x y b hxy hxb
    change (x, y) ∈ Q.forwardEdges at hxy
    change (x, b) ∈ Q.backwardEdges
    apply hQ.outgoing_removed hxy
    apply outgoing_referenceEdge_reflect hL
      (fun {_x _y} h ↦ (hQ.endpoint_pure h).2) hxy
      (hRoof (Q.forwardEdges_endpoints_mem_vertexSet hxy).1) hxb
  · intro p hp
    change IsEdgeInterval (Q.backwardEdges ∩ p.edgeSet) p
    exact (hL.stageReferenceEmbedding a).edgeIntervals_global
      Q.backwardEdges_subset_familyEdges hQ.intervals p hp
  · intro x y hxy
    change (x, y) ∈ Q.forwardEdges at hxy
    have hlocal := hQ.endpoint_pure hxy
    have hends := Q.forwardEdges_endpoints_mem_vertexSet hxy
    constructor
    · intro hy
      exact hlocal.1
        (initialSet_reflect_of_mem_roof hL hy (hRoof hends.2))
    · intro hx
      exact hlocal.2
        (terminalFrontier_reflect_of_mem_roof hL hx (hRoof hends.1))

end Alternating.InfiniteColouredOccurrenceWord

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

open ColouredSafeReferenceTransport

variable {current : Set Gamma.DPath} {L : Gamma.KappaLadder kappa}
variable {a : Stage kappa} {s : V}

/-- Retype either branch of a roof-contained current occurrence to the
limiting reference.  The occurrence source and finite endpoint are retained. -/
def retypeLimitReference
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    CurrentSafeOccurrence current L.limitWarp s := by
  cases A with
  | infinite Q hsafe hfirst =>
      exact .infinite (Q.retypeLimitReference hL)
        (hsafe.retypeLimitReference hL hRoof) hfirst
  | finite t Q hsafe hfirst hlast =>
      exact .finite t (Q.retypeLimitReference hL)
        (hsafe.retypeLimitReference hL hRoof) hfirst hlast

@[simp] theorem retypeLimitReference_forwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeLimitReference hL hRoof).forwardEdges = A.forwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeLimitReference_backwardEdges
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeLimitReference hL hRoof).backwardEdges = A.backwardEdges := by
  cases A <;> rfl

@[simp] theorem retypeLimitReference_vertexSet
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeLimitReference hL hRoof).vertexSet = A.vertexSet := by
  cases A <;> rfl

@[simp] theorem retypeLimitReference_terminal?
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    (A.retypeLimitReference hL hRoof).terminal? = A.terminal? := by
  cases A <;> rfl

end ColouredSafeReverseReachability.CurrentSafeOccurrence

#print axioms Blueprint.ReferenceSubpathEmbedding.edgeIntervals_global
#print axioms ColouredSafeReferenceTransport.limitWarp_inter_roof_subset_warpAt
#print axioms Alternating.FiniteColouredOccurrenceWord.IsIntervalSafe.retypeLimitReference
#print axioms Alternating.InfiniteColouredOccurrenceWord.IsIntervalSafe.retypeLimitReference
#print axioms ColouredSafeReverseReachability.CurrentSafeOccurrence.retypeLimitReference

end Erdos599
