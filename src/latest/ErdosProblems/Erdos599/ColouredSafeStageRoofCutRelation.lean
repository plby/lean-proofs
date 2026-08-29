/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeAmbientOccurrence
import ErdosProblems.Erdos599.ColouredSafeReferenceLocalization
import ErdosProblems.Erdos599.ColouredSafeTouchedReferenceSwitch
import ErdosProblems.Erdos599.GroundingSuccessorTransport
import ErdosProblems.Erdos599.HalfwayLadderReference
import ErdosProblems.Erdos599.SafeSwitchingRelationalBalance

/-!
# Cutting a noncausal safe occurrence at one stage roof

A globally safe occurrence need not stay in one stage roof.  This file does
not retype that occurrence as a stage occurrence.  Instead it keeps exactly
the forward incidences whose tails lie in the strict roof, and removes only
the occurrence's backward incidences which belong to the chosen stage
reference subwarp.  The resulting literal relation has the incidence,
interval, and endpoint-purity properties required by relational switch
realization.

The construction deliberately makes no claim about the initial or terminal
sets after realization.  In particular, later pruning may lose reentry
roots; source accounting is a separate step.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath Alternating Ladder Blueprint
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open Alternating.SwitchingCore
open Alternating.SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}} {L : Gamma.KappaLadder kappa}
variable {a : Stage kappa} {s : V}

namespace ColouredSafeStageRoofCutRelation

/-- Inserted occurrence edges whose tails lie strictly behind `T`.  Their
heads are proved to lie in the full roof when `T` is essential. -/
def forwardEdges
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (T : Set V) : Set (V × V) :=
  {e | e ∈ A.forwardEdges ∧ e.1 ∈ Gamma.strictRoof T}

/-- Removed incidences are cropped to the actual local reference. -/
def backwardEdges
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (Y : Set Gamma.DPath) : Set (V × V) :=
  A.backwardEdges ∩ familyEdges Y

/-- The exact stage-roof-cut switched relation. -/
def edges
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (Y : Set Gamma.DPath) (T : Set V) : Set (V × V) :=
  (familyEdges Y \ backwardEdges A Y) ∪ forwardEdges A T

/-- The negative endpoint contribution of a finite occurrence; infinite
occurrences have no such defect. -/
def terminalDefect
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) (x : V) : Int :=
  match A.terminal? with
  | none => 0
  | some t => propInt (x = t)

private theorem familyEdges_mono {X Y : Set Gamma.DPath} (hXY : X ⊆ Y) :
    familyEdges X ⊆ familyEdges Y := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨p, hp, hep⟩ := he
  exact ⟨p, hXY hp, hep⟩

/-- The exact signed balance of the erased occurrence. -/
theorem edgeBalance_forward_sub_backward
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (hlimit : Gamma.IsWarp L.limitWarp) (x : V) :
    edgeBalance A.forwardEdges x - edgeBalance A.backwardEdges x =
      propInt (x = s) - terminalDefect A x := by
  obtain ⟨W, hW, _hWfinite, hforward⟩ := hA
  let B := A.retypeForward hforward
  cases A with
  | infinite Q hQ hfirst =>
      have hbalance :=
        (Q.retypeForward hforward).edgeBalance_forward_sub_backward hW hlimit x
      change edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
        propInt (x = Q.vertex 0) at hbalance
      simpa only [CurrentSafeOccurrence.forwardEdges,
        CurrentSafeOccurrence.backwardEdges, terminalDefect,
        CurrentSafeOccurrence.terminal?, hfirst, sub_zero] using hbalance
  | finite t Q hQ hfirst hlast =>
      have hbalance :=
        (Q.retypeForward hforward).edgeBalance_forward_sub_backward hW hlimit x
      change edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
        propInt (x = Q.vertex 0) -
          propInt (x = Q.vertex (Fin.last Q.length)) at hbalance
      simpa only [CurrentSafeOccurrence.forwardEdges,
        CurrentSafeOccurrence.backwardEdges, terminalDefect,
        CurrentSafeOccurrence.terminal?, hfirst, hlast] using hbalance

theorem forwardEdges_subset
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) (T : Set V) :
    forwardEdges A T ⊆ A.forwardEdges := fun _ he ↦ he.1

theorem backwardEdges_subset
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (Y : Set Gamma.DPath) :
    backwardEdges A Y ⊆ familyEdges Y := fun _ he ↦ he.2

private theorem forward_head_not_initial_limit
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    {e : V × V} (he : e ∈ A.forwardEdges) :
    e.2 ∉ Gamma.initialSet L.limitWarp := by
  cases A with
  | infinite Q hQ => exact (hQ.endpoint_pure he).1
  | finite t Q hQ => exact (hQ.endpoint_pure he).1

private theorem incoming_removed_global
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    {x b y : V} (hxy : (x, y) ∈ A.forwardEdges)
    (hby : (b, y) ∈ familyEdges L.limitWarp) :
    (b, y) ∈ A.backwardEdges := by
  cases A with
  | infinite Q hQ => exact hQ.incoming_removed hxy hby
  | finite t Q hQ => exact hQ.incoming_removed hxy hby

private theorem outgoing_removed_global
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    {x y b : V} (hxy : (x, y) ∈ A.forwardEdges)
    (hxb : (x, b) ∈ familyEdges L.limitWarp) :
    (x, b) ∈ A.backwardEdges := by
  cases A with
  | infinite Q hQ => exact hQ.outgoing_removed hxy hxb
  | finite t Q hQ => exact hQ.outgoing_removed hxy hxb

/-- The cropped forward relation stays in the full stage roof.  This is the
only place where essentiality of the cutting frontier is used. -/
theorem forwardEdges_endpoints_mem_roof
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (T : Set V) (hessential : Gamma.essential T = T)
    {e : V × V} (he : e ∈ forwardEdges A T) :
    e.1 ∈ Gamma.roof T ∧ e.2 ∈ Gamma.roof T := by
  refine ⟨he.2.1, ?_⟩
  obtain ⟨W, _hW, _hWfinite, hforward⟩ := hA
  exact Gamma.adj_mem_roof_of_mem_strictRoof_of_essential hessential
    (familyEdges_subset_adj W (hforward he.1)) he.2

private theorem occurrence_forward_endpoints_mem_vertexSet
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    {e : V × V} (he : e ∈ A.forwardEdges) :
    e.1 ∈ A.vertexSet ∧ e.2 ∈ A.vertexSet := by
  cases A with
  | infinite Q => exact Q.forwardEdges_endpoints_mem_vertexSet he
  | finite t Q => exact Q.forwardEdges_endpoints_mem_vertexSet he

/-- Every endpoint used by the cropped relation comes from either the local
reference carrier or the literal occurrence carrier. -/
theorem edges_endpoints_mem_carrier_union
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (Y : Set Gamma.DPath) (T : Set V)
    {e : V × V} (he : e ∈ edges A Y T) :
    e.1 ∈ Gamma.vertexSet Y ∪ A.vertexSet ∧
      e.2 ∈ Gamma.vertexSet Y ∪ A.vertexSet := by
  rcases he with he | he
  · have hends := familyEdges_subset_vertexSet_prod Y he.1
    exact ⟨Or.inl hends.1, Or.inl hends.2⟩
  · have hends := occurrence_forward_endpoints_mem_vertexSet A he.1
    exact ⟨Or.inr hends.1, Or.inr hends.2⟩

/-- If the selected local reference is roofed, then every endpoint of the
literal cropped relation is roofed as well. -/
theorem edges_endpoints_mem_roof
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (Y : Set Gamma.DPath) (T : Set V)
    (hessential : Gamma.essential T = T)
    (hYroof : Gamma.vertexSet Y ⊆ Gamma.roof T)
    {e : V × V} (he : e ∈ edges A Y T) :
    e.1 ∈ Gamma.roof T ∧ e.2 ∈ Gamma.roof T := by
  rcases he with he | he
  · have hends := familyEdges_subset_vertexSet_prod Y he.1
    exact ⟨hYroof hends.1, hYroof hends.2⟩
  · exact forwardEdges_endpoints_mem_roof A hA T hessential he

/-- Every local reference incidence entering an inserted head is deleted. -/
theorem incoming_removed
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (Y : Set Gamma.DPath) (hY : Y ⊆ L.warpAt a) (T : Set V)
    {x b y : V} (hxy : (x, y) ∈ forwardEdges A T)
    (hby : (b, y) ∈ familyEdges Y) :
    (b, y) ∈ backwardEdges A Y := by
  refine ⟨incoming_removed_global A hxy.1 ?_, hby⟩
  exact (hL.stageReferenceEmbedding a).familyEdges_subset
    (familyEdges_mono hY hby)

/-- Every local reference incidence leaving an inserted tail is deleted. -/
theorem outgoing_removed
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (Y : Set Gamma.DPath) (hY : Y ⊆ L.warpAt a) (T : Set V)
    {x y b : V} (hxy : (x, y) ∈ forwardEdges A T)
    (hxb : (x, b) ∈ familyEdges Y) :
    (x, b) ∈ backwardEdges A Y := by
  refine ⟨outgoing_removed_global A hxy.1 ?_, hxb⟩
  exact (hL.stageReferenceEmbedding a).familyEdges_subset
    (familyEdges_mono hY hxb)

/-- The local crop retains the endpoint-purity needed by relational
realization.  Initial purity comes from the original occurrence.  Terminal
purity comes from stopping strictly behind the essential frontier. -/
theorem endpoint_pure
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (Y : Set Gamma.DPath) (hY : Y ⊆ L.warpAt a)
    (T : Set V) (hessential : Gamma.essential T = T)
    (hterminal : Gamma.terminalFrontier Y ⊆ T)
    {x y : V} (hxy : (x, y) ∈ forwardEdges A T) :
    y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y := by
  constructor
  · rintro ⟨p, hpY, hpy⟩
    apply forward_head_not_initial_limit A hxy.1
    apply ColouredSafeReferenceLocalization.initialSet_stage_subset_limit hL
    exact ⟨p, hY hpY, hpy⟩
  · intro hx
    exact hxy.2.2 (hessential.symm ▸ hterminal hx)

/-- Incidence deletion alone makes the cropped relation biunique. -/
theorem edges_biUnique
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (Y : Set Gamma.DPath) (hYWarp : Gamma.IsWarp Y)
    (hY : Y ⊆ L.warpAt a) (T : Set V) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ edges A Y T) := by
  obtain ⟨W, hW, _hWfinite, hforward⟩ := hA
  exact biUnique_of_incident_reference_edges_removed hW hYWarp
    (forwardEdges_subset A T |>.trans hforward)
    (incoming_removed hL A Y hY T) (outgoing_removed hL A Y hY T)

private theorem global_noForwardSandwich
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) :
    SwitchingCore.NoForwardSandwich (D := Gamma.graph)
      (familyEdges L.limitWarp \ A.backwardEdges) A.forwardEdges := by
  have hlimit : Gamma.IsWarp L.limitWarp :=
    hL.warpStages (Ladder.finalStage kappa)
  cases A with
  | infinite Q hQ =>
      exact noForwardSandwich_of_incidence_intervalConvex hlimit
        hQ.incoming_removed hQ.outgoing_removed hQ.intervals hQ.endpoint_pure
  | finite t Q hQ =>
      exact noForwardSandwich_of_incidence_intervalConvex hlimit
        hQ.incoming_removed hQ.outgoing_removed hQ.intervals hQ.endpoint_pure

/-- The no-sandwich certificate of the full occurrence survives the roof
crop.  This is stronger than the owner-interval fact needed by the usual
realization interface and avoids retyping a noncausal occurrence as a stage
word. -/
theorem noForwardSandwich
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (Y : Set Gamma.DPath) (hY : Y ⊆ L.warpAt a) (T : Set V) :
    SwitchingCore.NoForwardSandwich (D := Gamma.graph)
      (familyEdges Y \ backwardEdges A Y) (forwardEdges A T) := by
  intro p hpne hpB x y hxp hyp
  apply global_noForwardSandwich hL A p hpne
    (fun e he ↦ by
      have heLocal := hpB he
      exact ⟨(hL.stageReferenceEmbedding a).familyEdges_subset
        (familyEdges_mono hY heLocal.1),
        fun heBackward ↦ heLocal.2 ⟨heBackward, heLocal.1⟩⟩)
    x y (forwardEdges_subset A T hxp) (forwardEdges_subset A T hyp)

/-- The cropped relation has an exact finite-character realization.  This
uses the inherited no-sandwich certificate directly; it neither assumes nor
concludes any source or boundary accounting. -/
theorem exists_finiteWarp
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (Y : Set Gamma.DPath) (hYWarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hY : Y ⊆ L.warpAt a) (T : Set V)
    (hessential : Gamma.essential T = T)
    (hterminal : Gamma.terminalFrontier Y ⊆ T) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = edges A Y T ∧
      isolatedVertices U = isolatedVertices Y := by
  let R := backwardEdges A Y
  let F := forwardEdges A T
  let E := edges A Y T
  obtain ⟨W, hW, hWfinite, hforward⟩ := hA
  have hF : F ⊆ familyEdges W :=
    (forwardEdges_subset A T).trans hforward
  have hin : ∀ {x b y : V}, (x, y) ∈ F →
      (b, y) ∈ familyEdges Y → (b, y) ∈ R :=
    incoming_removed hL A Y hY T
  have hout : ∀ {x y b : V}, (x, y) ∈ F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R :=
    outgoing_removed hL A Y hY T
  have hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) :=
    biUnique_of_incident_reference_edges_removed hW hYWarp hF hin hout
  have hEeq : E = (familyEdges Y \ R) ∪ F := rfl
  have hgraph : (familyEdges Y \ R) ∪ F ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
    rintro e (he | he)
    · exact familyEdges_subset_adj Y he.1
    · exact familyEdges_subset_adj W (hF he)
  have hdisj : Disjoint (familyEdges Y \ R) F :=
    retained_disjoint_inserted_of_incidence hin
  have hno : SwitchingCore.NoForwardSandwich (D := Gamma.graph)
      (familyEdges Y \ R) F := noForwardSandwich hL A Y hY T
  have hBcycle : ¬ContainsDirectedCycle (familyEdges Y \ R) := by
    rintro ⟨C, hC⟩
    exact SwitchingCore.familyEdges_not_containsDirectedCycle hYWarp hYfinite
      ⟨C, hC.trans Set.sdiff_subset⟩
  have hBray : ¬ContainsDirectedRay (familyEdges Y \ R) := by
    rintro ⟨r, hr⟩
    exact SwitchingCore.familyEdges_not_containsDirectedRay hYWarp hYfinite
      ⟨r, hr.trans Set.sdiff_subset⟩
  have hBreverse : ¬ContainsReverseDirectedRay (familyEdges Y \ R) := by
    rintro ⟨r, hr⟩
    exact SwitchingCore.familyEdges_not_containsReverseDirectedRay hYWarp hYfinite
      ⟨r, fun n ↦ (hr n).1⟩
  have hFcycle : ¬ContainsDirectedCycle F := by
    rintro ⟨C, hC⟩
    exact SwitchingCore.familyEdges_not_containsDirectedCycle hW hWfinite
      ⟨C, hC.trans hF⟩
  have hFray : ¬ContainsDirectedRay F := by
    rintro ⟨r, hr⟩
    exact SwitchingCore.familyEdges_not_containsDirectedRay hW hWfinite
      ⟨r, hr.trans hF⟩
  have hFreverse : ¬ContainsReverseDirectedRay F := by
    rintro ⟨r, hr⟩
    exact SwitchingCore.familyEdges_not_containsReverseDirectedRay hW hWfinite
      ⟨r, fun n ↦ hF (hr n)⟩
  have hcycle : ¬ContainsDirectedCycle E := by
    rw [hEeq]
    exact SwitchingCore.union_not_containsDirectedCycle (familyEdges Y \ R) F
      hgraph hdisj hno hBcycle hFcycle
  have hray : ¬ContainsDirectedRay E := by
    rw [hEeq]
    exact SwitchingCore.union_not_containsDirectedRay (familyEdges Y \ R) F
      hgraph hno hBray hFray
  have hreverse : ¬ContainsReverseDirectedRay E := by
    rw [hEeq]
    exact SwitchingCore.union_not_containsReverseDirectedRay (familyEdges Y \ R) F
      hgraph hno hBreverse hFreverse
  have hI : ∀ x ∈ isolatedVertices Y, ∀ y,
      (x, y) ∉ E ∧ (y, x) ∉ E := by
    intro x hx y
    have hxInitial : x ∈ Gamma.initialSet Y :=
      ⟨Gamma.trivialPath x, hx, by simp⟩
    have hxTerminal : x ∈ Gamma.terminalFrontier Y :=
      ⟨Gamma.trivialPath x, hx, by simp⟩
    constructor
    · rintro (he | he)
      · exact not_isolated_of_hasOutgoing hYWarp ⟨y, he.1⟩ hx
      · exact (endpoint_pure hL A Y hY T hessential hterminal he).2 hxTerminal
    · rintro (he | he)
      · exact not_isolated_of_hasIncoming hYWarp ⟨y, he.1⟩ hx
      · exact (endpoint_pure hL A Y hY T hessential hterminal he).1 hxInitial
  obtain ⟨U, hU, hUE, hUI, hUfinite⟩ :=
    RelationDecomposition.DWeb.exists_finiteWarp_realizing_biUnique
      Gamma E (isolatedVertices Y) (hEeq.symm ▸ hgraph)
      hbi hcycle hray hreverse hI
  exact ⟨U, hU, hUfinite, hUE, hUI⟩

/-- The exact realization can be chosen with no new carrier outside the
local reference and the literal occurrence.  Under a roofed local reference
it is entirely contained in the cutting roof. -/
theorem exists_finiteWarp_roofed
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (Y : Set Gamma.DPath) (hYWarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hY : Y ⊆ L.warpAt a) (T : Set V)
    (hessential : Gamma.essential T = T)
    (hterminal : Gamma.terminalFrontier Y ⊆ T)
    (hYroof : Gamma.vertexSet Y ⊆ Gamma.roof T) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = edges A Y T ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.vertexSet U ⊆ Gamma.roof T ∧
      Gamma.vertexSet U ⊆ Gamma.vertexSet Y ∪ A.vertexSet := by
  obtain ⟨U, hU, hUfinite, hUE, hUI⟩ :=
    exists_finiteWarp hL A hA Y hYWarp hYfinite hY T hessential hterminal
  have hroof : Gamma.vertexSet U ⊆ Gamma.roof T := by
    rw [TerminalContactSwitch.vertexSet_eq_isolated_union_incident_anyWarp hU]
    rintro x (hx | hx)
    · exact hYroof (isolatedVertices_subset_vertexSet Y (hUI ▸ hx))
    · rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact (edges_endpoints_mem_roof A hA Y T hessential hYroof
          (hUE ▸ hy)).2
      · exact (edges_endpoints_mem_roof A hA Y T hessential hYroof
          (hUE ▸ hy)).1
  have hcarrier : Gamma.vertexSet U ⊆ Gamma.vertexSet Y ∪ A.vertexSet := by
    rw [TerminalContactSwitch.vertexSet_eq_isolated_union_incident_anyWarp hU]
    rintro x (hx | hx)
    · exact Or.inl (isolatedVertices_subset_vertexSet Y (hUI ▸ hx))
    · rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact (edges_endpoints_mem_carrier_union A Y T (hUE ▸ hy)).2
      · exact (edges_endpoints_mem_carrier_union A Y T (hUE ▸ hy)).1
  exact ⟨U, hU, hUfinite, hUE, hUI, hroof, hcarrier⟩

theorem exists_finiteWarp_roofed_countable
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A)
    (Y : Set Gamma.DPath) (hYWarp : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hYcountable : (Gamma.vertexSet Y).Countable)
    (hY : Y ⊆ L.warpAt a) (T : Set V)
    (hessential : Gamma.essential T = T)
    (hterminal : Gamma.terminalFrontier Y ⊆ T)
    (hYroof : Gamma.vertexSet Y ⊆ Gamma.roof T) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = edges A Y T ∧
      isolatedVertices U = isolatedVertices Y ∧
      Gamma.vertexSet U ⊆ Gamma.roof T ∧
      (Gamma.vertexSet U).Countable := by
  obtain ⟨U, hU, hUfinite, hUE, hUI, hroof, hcarrier⟩ :=
    exists_finiteWarp_roofed hL A hA Y hYWarp hYfinite hY T
      hessential hterminal hYroof
  exact ⟨U, hU, hUfinite, hUE, hUI, hroof,
    (hYcountable.union A.vertexSet_countable).mono hcarrier⟩

/-- The finite essential stage-reference owners touched by the literal
occurrence.  This is selected after the stage is fixed. -/
def stageTouchedReference
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) :
    Set Gamma.DPath :=
  {p | p ∈ LinkageBlueprint.ladderReference L a ∧
    (p.support ∩ A.vertexSet).Nonempty}

theorem stageTouchedReference_subset :
    ∀ (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s),
    stageTouchedReference (L := L) (a := a) (s := s) A ⊆
      LinkageBlueprint.ladderReference L a := fun _ _ hp ↦ hp.1

theorem stageTouchedReference_isWarp
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) :
    Gamma.IsWarp (stageTouchedReference (L := L) (a := a) (s := s) A) := by
  intro p hp q hq hpq
  exact LinkageBlueprint.ladderReference.isWarp hL hp.1 hq.1 hpq

theorem stageTouchedReference_finiteCharacter
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) :
    Gamma.HasFiniteCharacter
      (stageTouchedReference (L := L) (a := a) (s := s) A) :=
  fun hp ↦ LinkageBlueprint.ladderReference.finiteCharacter hp.1

theorem vertexSet_stageTouchedReference
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) :
    Gamma.vertexSet
        (stageTouchedReference (L := L) (a := a) (s := s) A) =
      meetingVertices Gamma (LinkageBlueprint.ladderReference L a) A.vertexSet := by
  ext x
  constructor
  · rintro ⟨p, hp, hxp⟩
    exact Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxp⟩
  · intro hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    exact ⟨p.1, p.2, hxp⟩

theorem vertexSet_stageTouchedReference_countable
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) :
    (Gamma.vertexSet
      (stageTouchedReference (L := L) (a := a) (s := s) A)).Countable := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [vertexSet_stageTouchedReference]
  exact mk_meetingVertices_le Gamma (LinkageBlueprint.ladderReference L a)
    A.vertexSet (LinkageBlueprint.ladderReference.isWarp hL) le_rfl
    A.vertexSet_countable.le_aleph0

theorem stageTouchedReference_terminal_subset
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) :
    Gamma.terminalFrontier
        (stageTouchedReference (L := L) (a := a) (s := s) A) ⊆
      L.frontier a := by
  rintro x ⟨p, hp, hpx⟩
  rw [← LinkageBlueprint.ladderReference.terminalFrontier_eq hL]
  exact ⟨p, hp.1, hpx⟩

theorem stageTouchedReference_vertexSet_subset_roof
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s) :
    Gamma.vertexSet
      (stageTouchedReference (L := L) (a := a) (s := s) A) ⊆
      Gamma.roof (L.frontier a) := by
  intro x hx
  apply LinkageBlueprint.ladderReference.vertexSet_subset_roof hL
    (DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
      hL a)
  obtain ⟨p, hp, hxp⟩ := hx
  exact ⟨p, hp.1, hxp⟩

/-- Canonical fixed-stage roof cut.  The full occurrence may make noncausal
excursions outside this roof; only its literal strict-roof forward edges and
the touched essential stage reference enter the realized relation. -/
theorem exists_stageTouched_finiteWarp
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (A : ColouredSafeAmbientOccurrence.Occurrence L.limitWarp s)
    (hA : ColouredSafeAmbientOccurrence.Valid A) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = edges A
        (stageTouchedReference (L := L) (a := a) (s := s) A) (L.frontier a) ∧
      isolatedVertices U = isolatedVertices
        (stageTouchedReference (L := L) (a := a) (s := s) A) ∧
      Gamma.vertexSet U ⊆ Gamma.roof (L.frontier a) ∧
      (Gamma.vertexSet U).Countable := by
  apply exists_finiteWarp_roofed_countable hL A hA
    (stageTouchedReference (L := L) (a := a) (s := s) A)
    (stageTouchedReference_isWarp hL A)
    (stageTouchedReference_finiteCharacter A)
    (vertexSet_stageTouchedReference_countable hL A)
  · intro p hp
    exact hp.1.1
  · exact L.frontiersAreEssential_of_roofsSourceAtStages
      hL.roofsSourceAtStages a
  · exact stageTouchedReference_terminal_subset hL A
  · exact stageTouchedReference_vertexSet_subset_roof hL A

end ColouredSafeStageRoofCutRelation

end Erdos599
