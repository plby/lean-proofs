/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStageRoofCutRelation

/-!
# Roof cutting relative to an arbitrary inherited reference

Keep forward edges with strictly roofed tails and crop removed edges to a
finite local reference. Only edge and initial inclusion into the original
reference are needed. The full occurrence need not be roofed, and the
original reference need not have finite character. The exact realization
does not by itself assert a rooted boundary or source coverage.
-/

noncomputable section

namespace Erdos599.ColouredSafeReferenceRoofCut

open Set DirectedPath Alternating
open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence
open Alternating.SwitchingCore Alternating.SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {G : Set Gamma.DPath} {s : V}

def forwardEdges (A : Occurrence G s) (T : Set V) : Set (V × V) :=
  {e | e ∈ A.forwardEdges ∧ e.1 ∈ Gamma.strictRoof T}

def backwardEdges (A : Occurrence G s) (K : Set Gamma.DPath) : Set (V × V) :=
  A.backwardEdges ∩ familyEdges K

def edges (A : Occurrence G s) (K : Set Gamma.DPath) (T : Set V) : Set (V × V) :=
  (familyEdges K \ backwardEdges A K) ∪ forwardEdges A T

theorem incoming_removed (A : Occurrence G s) {K : Set Gamma.DPath}
    (hKE : familyEdges K ⊆ familyEdges G) {T : Set V} {x b y : V}
    (hxy : (x, y) ∈ forwardEdges A T) (hby : (b, y) ∈ familyEdges K) :
    (b, y) ∈ backwardEdges A K := by
  refine ⟨?_, hby⟩
  cases A with
  | infinite Q hQ => exact hQ.incoming_removed hxy.1 (hKE hby)
  | finite t Q hQ => exact hQ.incoming_removed hxy.1 (hKE hby)

theorem outgoing_removed (A : Occurrence G s) {K : Set Gamma.DPath}
    (hKE : familyEdges K ⊆ familyEdges G) {T : Set V} {x y b : V}
    (hxy : (x, y) ∈ forwardEdges A T) (hxb : (x, b) ∈ familyEdges K) :
    (x, b) ∈ backwardEdges A K := by
  refine ⟨?_, hxb⟩
  cases A with
  | infinite Q hQ => exact hQ.outgoing_removed hxy.1 (hKE hxb)
  | finite t Q hQ => exact hQ.outgoing_removed hxy.1 (hKE hxb)

theorem noForwardSandwich (hG : Gamma.IsWarp G) (A : Occurrence G s)
    {K : Set Gamma.DPath} (hKE : familyEdges K ⊆ familyEdges G) (T : Set V) :
    SwitchingCore.NoForwardSandwich (D := Gamma.graph)
      (familyEdges K \ backwardEdges A K) (forwardEdges A T) := by
  have hglobal : SwitchingCore.NoForwardSandwich (D := Gamma.graph)
      (familyEdges G \ A.backwardEdges) A.forwardEdges := by
    cases A with
    | infinite Q hQ =>
      exact noForwardSandwich_of_incidence_intervalConvex hG
        hQ.incoming_removed hQ.outgoing_removed hQ.intervals hQ.endpoint_pure
    | finite t Q hQ =>
      exact noForwardSandwich_of_incidence_intervalConvex hG
        hQ.incoming_removed hQ.outgoing_removed hQ.intervals hQ.endpoint_pure
  intro p hpne hpB x y hxp hyp
  apply hglobal p hpne (fun e he ↦ ?_) x y hxp.1 hyp.1
  have heLocal := hpB he
  exact ⟨hKE heLocal.1, fun hback ↦ heLocal.2 ⟨hback, heLocal.1⟩⟩

theorem endpoint_pure (A : Occurrence G s) {K : Set Gamma.DPath}
    (hKI : Gamma.initialSet K ⊆ Gamma.initialSet G) {T : Set V}
    (hessential : Gamma.essential T = T) (hKT : Gamma.terminalFrontier K ⊆ T)
    {x y : V} (hxy : (x, y) ∈ forwardEdges A T) :
    y ∉ Gamma.initialSet K ∧ x ∉ Gamma.terminalFrontier K := by
  constructor
  · intro hy
    have hyG := hKI hy
    cases A with
    | infinite Q hQ => exact (hQ.endpoint_pure hxy.1).1 hyG
    | finite t Q hQ => exact (hQ.endpoint_pure hxy.1).1 hyG
  · exact fun hx ↦ hxy.2.2 (hessential.symm ▸ hKT hx)

theorem edges_subset_switchedEdges (A : Occurrence G s) {K : Set Gamma.DPath}
    (hKE : familyEdges K ⊆ familyEdges G) (T : Set V) :
    edges A K T ⊆ A.switchedEdges := by
  rintro e (he | he)
  · exact Or.inl ⟨hKE he.1, fun hback ↦ he.2 ⟨hback, he.1⟩⟩
  · exact Or.inr he.1

theorem exists_finiteWarp_roofed (hG : Gamma.IsWarp G) (A : Occurrence G s)
    (hA : Valid A) (K : Set Gamma.DPath) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K) (hKE : familyEdges K ⊆ familyEdges G)
    (hKI : Gamma.initialSet K ⊆ Gamma.initialSet G)
    (T : Set V) (hessential : Gamma.essential T = T)
    (hKT : Gamma.terminalFrontier K ⊆ T) (hKRoof : Gamma.vertexSet K ⊆ Gamma.roof T) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      familyEdges U = edges A K T ∧ isolatedVertices U = isolatedVertices K ∧
      Gamma.vertexSet U ⊆ Gamma.roof T ∧
      Gamma.vertexSet U ⊆ Gamma.vertexSet K ∪ A.vertexSet := by
  obtain ⟨W, hW, hWfinite, hforward⟩ := hA
  have hF : forwardEdges A T ⊆ familyEdges W := fun _ he ↦ hforward he.1
  have hbi : Relator.BiUnique (fun x y ↦ (x, y) ∈ edges A K T) :=
    biUnique_of_incident_reference_edges_removed hW hK hF
      (incoming_removed A hKE) (outgoing_removed A hKE)
  have hI : ∀ x ∈ isolatedVertices K, ∀ y,
      (x, y) ∉ edges A K T ∧ (y, x) ∉ edges A K T := by
    intro x hx y
    have hxI : x ∈ Gamma.initialSet K := ⟨Gamma.trivialPath x, hx, by simp⟩
    have hxT : x ∈ Gamma.terminalFrontier K := ⟨Gamma.trivialPath x, hx, by simp⟩
    constructor
    · rintro (he | he)
      · exact not_isolated_of_hasOutgoing hK ⟨y, he.1⟩ hx
      · exact (endpoint_pure A hKI hessential hKT he).2 hxT
    · rintro (he | he)
      · exact not_isolated_of_hasIncoming hK ⟨y, he.1⟩ hx
      · exact (endpoint_pure A hKI hessential hKT he).1 hxI
  obtain ⟨U, hU, hUE, hUI, hUfinite⟩ :=
    exists_finiteWarp_realizing_incidence_noForwardSandwich hW hK hWfinite hKfinite
      hF (incoming_removed A hKE) rfl hbi (noForwardSandwich hG A hKE T)
      (isolatedVertices K) hI
  change familyEdges U = edges A K T at hUE
  have hforwardCarrier : ∀ e ∈ A.forwardEdges,
      e.1 ∈ A.vertexSet ∧ e.2 ∈ A.vertexSet := by
    intro e he
    cases A with
    | infinite Q => exact Q.forwardEdges_endpoints_mem_vertexSet he
    | finite t Q => exact Q.forwardEdges_endpoints_mem_vertexSet he
  have hends : ∀ e ∈ edges A K T,
      (e.1 ∈ Gamma.roof T ∧ e.2 ∈ Gamma.roof T) ∧
      (e.1 ∈ Gamma.vertexSet K ∪ A.vertexSet ∧
        e.2 ∈ Gamma.vertexSet K ∪ A.vertexSet) := by
    rintro e (he | he)
    · have hv := familyEdges_subset_vertexSet_prod K he.1
      exact ⟨⟨hKRoof hv.1, hKRoof hv.2⟩, ⟨Or.inl hv.1, Or.inl hv.2⟩⟩
    · have hv := hforwardCarrier e he.1
      exact ⟨⟨he.2.1, Gamma.adj_mem_roof_of_mem_strictRoof_of_essential hessential
        (familyEdges_subset_adj W (hforward he.1)) he.2⟩, ⟨Or.inr hv.1, Or.inr hv.2⟩⟩
  have hcarrier : ∀ x ∈ Gamma.vertexSet U,
      x ∈ Gamma.roof T ∧ x ∈ Gamma.vertexSet K ∪ A.vertexSet := by
    rw [TerminalContactSwitch.vertexSet_eq_isolated_union_incident_anyWarp hU]
    rintro x (hx | hx)
    · have hxK := isolatedVertices_subset_vertexSet K (hUI ▸ hx)
      exact ⟨hKRoof hxK, Or.inl hxK⟩
    · rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
      · have h := hends (y, x) (hUE ▸ hy)
        exact ⟨h.1.2, h.2.2⟩
      · have h := hends (x, y) (hUE ▸ hy)
        exact ⟨h.1.1, h.2.1⟩
  exact ⟨U, hU, hUfinite, hUE, hUI,
    fun x hx ↦ (hcarrier x hx).1, fun x hx ↦ (hcarrier x hx).2⟩

#print axioms exists_finiteWarp_roofed

end Erdos599.ColouredSafeReferenceRoofCut
