/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause

/-!
# The exact-frontier half-way clause

The terminal blueprint construction proves more than the public half-way
clause records: the terminal frontier of the completed family is exactly the
constructed stop-over.  This file retains that equality in the induction
interface.  Literal quotient iteration can consequently use the produced
family without choosing a different altitude-minimizing stop-over.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

open Blueprint.LinkageBlueprint

universe u

variable {V : Type u}

/-- A bounded half-way linkage together with the particular stop-over whose
frontier it realizes exactly. -/
def ExactFrontierHalfwayLinkageOfAltitude (Gamma : DWeb V)
    (A0 : Set V) (kappa : Cardinal.{u}) (W : Set Gamma.DPath) : Prop :=
  ∃ C : Set V, IsHalfwayStopover Gamma W C ∧
    Gamma.terminalFrontier W = C ∧ LinksToTarget Gamma W A0 ∧
    HeightAtMost Gamma C kappa

namespace ExactFrontierHalfwayLinkageOfAltitude

/-- Forgetting the retained frontier equality gives the ordinary qualified
half-way linkage used by Theorem 9.2. -/
theorem toHalfwayLinkageOfAltitude
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    {W : Set Gamma.DPath}
    (h : ExactFrontierHalfwayLinkageOfAltitude Gamma A0 kappa W) :
    IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  obtain ⟨C, hC, -, hlinks, hheight⟩ := h
  exact halfwayLinkageOfAltitude_of_stopover hC hlinks hheight

end ExactFrontierHalfwayLinkageOfAltitude

/-- The source half-way clause with the exact terminal frontier retained. -/
def ExactFrontierHalfwayClauseAt (Gamma : DWeb V)
    (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    ∃ W : Set Gamma.DPath,
      ExactFrontierHalfwayLinkageOfAltitude Gamma A0 kappa W

/-- The exact-frontier clause strengthens the ordinary half-way clause. -/
theorem ExactFrontierHalfwayClauseAt.toHalfwayClauseAt
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (h : ExactFrontierHalfwayClauseAt Gamma kappa) :
    HalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  obtain ⟨W, hW⟩ := h A0 hA0 hcard
  exact ⟨W, hW.toHalfwayLinkageOfAltitude⟩

/-- A globally resolved blueprint certificate produces the literal completed
family and retains its exact frontier, rather than erasing that equality in
the ordinary half-way package. -/
theorem GloballyResolvedBlueprintCertificate.exists_exactFrontierHalfwayLinkage
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (C : GloballyResolvedBlueprintCertificate Gamma A0 kappa) :
    ∃ W : Set Gamma.DPath,
      ExactFrontierHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  let R : Set Gamma.DPath := C.blueprint.referenceRemainder C.slice
  let W : Set Gamma.DPath := C.blueprint.completedFamily C.edge_real R
  have hwarp : Gamma.IsWarp W :=
    C.blueprint.isWarp_completedFamily C.edge_real
      (C.blueprint.isWarp_referenceRemainder C.slice C.reference_isWarp)
      (C.blueprint.disjoint_referenceRemainder C.slice)
  have hUfinite : ∀ p ∈ C.blueprint.paths,
      ∃ q : DirectedPath.FinitePath
        (Blueprint.imaginaryGraph Gamma C.reference kappa), p = .inl q := by
    intro p hp
    obtain ⟨q, hpq, -⟩ := C.blueprint_endpointPure p hp
    exact ⟨q, hpq⟩
  have hRfinite : Gamma.HasFiniteCharacter R := by
    intro p hp
    obtain ⟨q, hpq, -⟩ := C.reference_endpointPure p hp
    exact ⟨q, hpq⟩
  have hfinite : Gamma.HasFiniteCharacter W :=
    C.blueprint.finiteCharacter_completedFamily C.edge_real
      hUfinite hRfinite
  have hinitial : Gamma.initialSet W = Gamma.source := by
    rw [C.blueprint.initialSet_completedFamily C.edge_real R]
    exact C.source_cover
  have hterminal : Gamma.terminalFrontier W = C.stopover := by
    rw [C.blueprint.terminalFrontier_completedFamily C.edge_real R]
    exact C.terminal_frontier
  have hpure : ∀ p ∈ W,
      IsPathBetween Gamma Gamma.source C.stopover p :=
    C.blueprint.endpointPure_completedFamily C.edge_real
      C.blueprint_endpointPure C.reference_endpointPure
  have hlinkage : IsLinkageBetween Gamma Gamma.source C.stopover W :=
    ⟨hwarp, hfinite, hinitial, hterminal.le, hpure⟩
  have hgraph : C.blueprint.familyGraph = C.blueprint.realPart := by
    change Blueprint.FamilyGraph.mk C.blueprint.familyGraph.vertices
        C.blueprint.familyGraph.edges =
      Blueprint.FamilyGraph.mk C.blueprint.realPart.vertices
        C.blueprint.realPart.edges
    apply congrArg₂ (fun vertices edges ↦
      Blueprint.FamilyGraph.mk vertices edges)
    · rfl
    · change C.blueprint.familyGraph.edges =
        C.blueprint.familyGraph.edges ∩ {e | Gamma.graph.Adj e.1 e.2}
      apply Set.Subset.antisymm
      · intro e he
        exact ⟨he, C.edge_real he⟩
      · exact Set.inter_subset_left
  have hterminalTarget : C.blueprint.terminalSet ⊆ Gamma.target := by
    intro x hx
    have hxterm := C.blueprint.terminalSet_subset_familyGraph_terminals
      C.blueprint_endpointPure hx
    rw [hgraph] at hxterm
    exact C.real_terminals_target hxterm
  have hblueprintLinks : C.blueprint.BlueprintLinksToTarget A0 :=
    C.blueprint.blueprintLinksToTarget_of_initial_terminal
      C.designated_source C.designated_initial C.blueprint_endpointPure
      hterminalTarget
  have hlinks : LinksToTarget Gamma W A0 :=
    C.blueprint.linksToTarget_completedFamily C.edge_real R hblueprintLinks
  have hheight : HeightAtMost Gamma C.stopover kappa :=
    ⟨C.heightDelete,
      ⟨C.heightDelete_nonSource, C.heightWave, C.heightWave_isWave,
        C.stopover_roofed⟩,
      C.heightDelete_card⟩
  exact ⟨W, C.stopover,
    ⟨hlinkage, C.stopover_trimmed, C.quotient_unhindered⟩,
    hterminal, hlinks, hheight⟩

/-- Construction certificates for every designated source set prove the
strong exact-frontier half-way clause. -/
theorem exactFrontierHalfwayClauseAt_of_globallyResolvedBlueprintCertificates
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcert : ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
      Nonempty (GloballyResolvedBlueprintCertificate Gamma A0 kappa)) :
    ExactFrontierHalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  exact (hcert A0 hA0 hcard).some.exists_exactFrontierHalfwayLinkage

end CardinalInduction
end Erdos599
