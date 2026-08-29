/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceTransport

/-!
# Semantic invariance of native occurrences under limiting-reference transport

Inside a selected stage roof, retyping a native coloured occurrence from the
stage reference to the limiting reference does not change finite switched
reachability.  The nontrivial direction first proves that a limiting switched
path whose terminal is roofed is entirely roofed, and then reflects every
retained limiting-reference edge back to the selected stage.

The second part records that reference retyping is injective on the subtype of
roof-supported ambient occurrences.  This is literal-data injectivity: the
vertices, directions, and finite endpoint are unchanged by retyping.  It is
the cardinality interface needed when transporting native hammocks.
-/

noncomputable section

open Set

namespace Erdos599

open DirectedPath Alternating Ladder Blueprint

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}

namespace Alternating.FiniteColouredOccurrenceWord

variable {W : Set Gamma.DPath}

/-- Reference retyping is injective because it leaves every literal field of
the finite occurrence word unchanged. -/
theorem retypeLimitReference_injective
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Function.Injective
      (retypeLimitReference (W := W) (a := a) hL) := by
  intro Q P h
  rcases Q with ⟨n, v, d, hs, hi⟩
  rcases P with ⟨m, w, e, ht, hj⟩
  simp only [retypeLimitReference, retypeEdges] at h
  cases h
  rfl

end Alternating.FiniteColouredOccurrenceWord

namespace Alternating.InfiniteColouredOccurrenceWord

variable {W : Set Gamma.DPath}

/-- Reference retyping is injective on infinite literal occurrence words. -/
theorem retypeLimitReference_injective
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Function.Injective
      (retypeLimitReference (W := W) (a := a) hL) := by
  intro Q P h
  rcases Q with ⟨v, d, hs, hi⟩
  rcases P with ⟨w, e, ht, hj⟩
  simp only [retypeLimitReference] at h
  cases h
  rfl

end Alternating.InfiniteColouredOccurrenceWord

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

open ColouredSafeReferenceTransport
open DWeb.KappaLadder.Deferred

variable {current : Set Gamma.DPath} {s : V}

private theorem pathFamilyEdgeSet_eq_familyEdges
    (Gamma : DWeb V) (W : Set Gamma.DPath) :
    Gamma.pathFamilyEdgeSet W = familyEdges W := by
  ext e
  simp only [DWeb.pathFamilyEdgeSet, familyEdges, Set.mem_ofPred_eq,
    Set.mem_iUnion]
  constructor <;> rintro ⟨p, hp, he⟩ <;> exact ⟨p, hp, he⟩

/-- Both endpoints of an inserted forward edge occur in the native word. -/
theorem forwardEdges_endpoints_mem_vertexSet
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    {e : V × V} (he : e ∈ A.forwardEdges) :
    e.1 ∈ A.vertexSet ∧ e.2 ∈ A.vertexSet := by
  cases A with
  | infinite Q =>
      exact Q.forwardEdges_endpoints_mem_vertexSet he
  | finite t Q =>
      exact Q.forwardEdges_endpoints_mem_vertexSet he

/-- The stage switched relation is contained in the limiting switched
relation.  Removed and inserted relations are literally unchanged. -/
theorem switchedEdges_subset_retypeLimitReference
    (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    A.switchedEdges ⊆ (A.retypeLimitReference hL hRoof).switchedEdges := by
  intro e he
  rcases he with hreference | hforward
  · exact Or.inl ⟨
      (hL.stageReferenceEmbedding a).familyEdges_subset hreference.1,
      by simpa using hreference.2⟩
  · exact Or.inr (by simpa using hforward)

/-- A limiting switched edge whose head lies in the selected roof is already
a stage switched edge. -/
theorem mem_switchedEdges_of_retype_of_head_mem_roof
    (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    {e : V × V}
    (he : e ∈ (A.retypeLimitReference hL hRoof).switchedEdges)
    (hheadRoof : e.2 ∈ Gamma.roof (L.frontier a)) :
    e ∈ A.switchedEdges := by
  rcases he with hreference | hforward
  · exact Or.inl ⟨
      incoming_referenceEdge_reflect hL hreference.1 hheadRoof,
      by simpa using hreference.2⟩
  · exact Or.inr (by simpa using hforward)

/-- A finite path in the limiting switched relation which ends in the
selected roof cannot have entered that roof late.  Reference edges reflect by
the ladder no-late-entry theorem, while inserted edges have roofed tails
because the occurrence carrier is roofed. -/
theorem finitePath_support_subset_roof_of_retypeLimitReference
    (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    {p : FinitePath Gamma.graph}
    (hpEdges : p.edgeSet ⊆
      (A.retypeLimitReference hL hRoof).switchedEdges)
    (hfinishRoof : p.finish ∈ Gamma.roof (L.frontier a)) :
    p.support ⊆ Gamma.roof (L.frontier a) := by
  have hback : ∀ {x y : V}, (x, y) ∈ p.edgeSet →
      y ∈ Gamma.roof (L.frontier a) →
      x ∈ Gamma.roof (L.frontier a) := by
    intro x y hxy hyRoof
    rcases hpEdges hxy with hreference | hforward
    · have hstage : (x, y) ∈ familyEdges (L.warpAt a) :=
        incoming_referenceEdge_reflect hL hreference.1 hyRoof
      rw [← pathFamilyEdgeSet_eq_familyEdges] at hstage
      have hxRaw := edge_tail_mem_strictRoof_of_mem_warpAt hL a hstage
      rw [L.frontier_eq_essential_terminalFrontier
        hL.roofsSourceAtStages, Gamma.roof_essential]
      exact hxRaw.1
    · have hforward' : (x, y) ∈ A.forwardEdges := by simpa using hforward
      exact hRoof (A.forwardEdges_endpoints_mem_vertexSet hforward').1
  intro x hxp
  let q := p.suffixFrom x hxp
  have hq :=
    _root_.Erdos599.DWeb.KappaLadder.Walk.start_mem_of_meets_of_backwardClosed
      (w := q.walk) (R := Gamma.roof (L.frontier a))
      (fun {_y _z} hyz hzRoof ↦
        hback (p.suffixFrom_edgeSet_subset x hxp hyz) hzRoof)
      ⟨p.finish, q.finish_mem_support, by simpa [q] using hfinishRoof⟩
  simpa [q] using hq

/-- Finite switched reachability to a displayed roofed terminal is invariant
under passage from the selected stage reference to the limiting reference. -/
theorem hasFiniteSwitchedPathTo_retypeLimitReference_iff
    (hL : HalfwayGeometry L)
    (A : CurrentSafeOccurrence current (L.warpAt a) s)
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    {t : V} (htRoof : t ∈ Gamma.roof (L.frontier a)) :
    (A.retypeLimitReference hL hRoof).HasFiniteSwitchedPathTo t ↔
      A.HasFiniteSwitchedPathTo t := by
  constructor
  · rintro ⟨p, hpStart, hpFinish, hpEdges⟩
    have hpRoof : p.support ⊆ Gamma.roof (L.frontier a) :=
      finitePath_support_subset_roof_of_retypeLimitReference
        hL A hRoof hpEdges (hpFinish.symm ▸ htRoof)
    refine ⟨p, hpStart, hpFinish, ?_⟩
    intro e he
    exact mem_switchedEdges_of_retype_of_head_mem_roof hL A hRoof
      (hpEdges he) (hpRoof (p.edgeSet_subset_support_prod he).2)
  · rintro ⟨p, hpStart, hpFinish, hpEdges⟩
    exact ⟨p, hpStart, hpFinish,
      hpEdges.trans (switchedEdges_subset_retypeLimitReference hL A hRoof)⟩

/-- Retyping is injective on roof-supported current occurrences.  The subtype
is important only because it supplies the safeness transport proof; equality
of outputs recovers the unchanged finite or infinite literal word. -/
theorem retypeLimitReference_injective
    (hL : HalfwayGeometry L) :
    Function.Injective
      (fun A : {A : CurrentSafeOccurrence current (L.warpAt a) s //
          A.vertexSet ⊆ Gamma.roof (L.frontier a)} ↦
        A.1.retypeLimitReference hL A.2) := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ h
  apply Subtype.ext
  dsimp at h ⊢
  cases A with
  | infinite Q hQ hfirst =>
      cases B with
      | infinite P hP hpfirst =>
          injection h with hQP
          have hraw : Q = P :=
            Alternating.InfiniteColouredOccurrenceWord.retypeLimitReference_injective
              hL hQP
          subst P
          rfl
      | finite t P hP hpfirst hplast => cases h
  | finite t Q hQ hfirst hlast =>
      cases B with
      | infinite P hP hpfirst => cases h
      | finite u P hP hpfirst hplast =>
          injection h with htu hQP
          have hraw : Q = P :=
            Alternating.FiniteColouredOccurrenceWord.retypeLimitReference_injective
              hL hQP
          subst P
          subst u
          rfl

end ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace ColouredSafeAmbientOccurrence

open ColouredSafeReverseReachability
open DWeb.KappaLadder.Deferred

variable {s : V}

/-- Ambient native occurrences at a selected stage whose complete literal
carrier is contained in the selected roof. -/
abbrev RoofSupportedAt
    (L : Gamma.KappaLadder kappa) (a : Stage kappa) (s : V) :=
  {A : Occurrence (L.warpAt a) s //
    A.vertexSet ⊆ Gamma.roof (L.frontier a)}

/-- Retype a roof-supported ambient occurrence to the limiting reference. -/
def retypeLimitReference
    (hL : HalfwayGeometry L) (A : RoofSupportedAt L a s) :
    Occurrence L.limitWarp s :=
  A.1.retypeLimitReference hL A.2

@[simp] theorem retypeLimitReference_vertexSet
    (hL : HalfwayGeometry L) (A : RoofSupportedAt L a s) :
    (retypeLimitReference hL A).vertexSet = A.1.vertexSet := by
  exact ColouredSafeReverseReachability.CurrentSafeOccurrence.retypeLimitReference_vertexSet
    hL A.1 A.2

@[simp] theorem retypeLimitReference_terminal?
    (hL : HalfwayGeometry L) (A : RoofSupportedAt L a s) :
    (retypeLimitReference hL A).terminal? = A.1.terminal? := by
  exact ColouredSafeReverseReachability.CurrentSafeOccurrence.retypeLimitReference_terminal?
    hL A.1 A.2

/-- The ambient roof-supported transport is injective, hence it preserves
cardinality of every native hammock family by image/injection arguments. -/
theorem retypeLimitReference_injective
    (hL : HalfwayGeometry L) :
    Function.Injective
      (retypeLimitReference (L := L) (a := a) (s := s) hL) :=
  ColouredSafeReverseReachability.CurrentSafeOccurrence.retypeLimitReference_injective
    hL

end ColouredSafeAmbientOccurrence

#print axioms ColouredSafeReverseReachability.CurrentSafeOccurrence.hasFiniteSwitchedPathTo_retypeLimitReference_iff
#print axioms ColouredSafeAmbientOccurrence.retypeLimitReference_injective

end Erdos599
