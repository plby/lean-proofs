/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayTerminalBoundarySubset
import ErdosProblems.Erdos599.HalfwaySourceRootPruningTerminal

/-!
# Sound separating final certificate with a containing stopover

The chosen separating stopover may contain vertices which are not terminals
of the selected linkage.  The mathematically sound certificate therefore
records terminal-frontier inclusion, exactly as `IsLinkageBetween` does.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

open Blueprint LinkageBlueprint

universe u

variable {V : Type u}

/-- A globally resolved blueprint with the sound containing-stopover
boundary.  Every field is construction data; no half-way conclusion is an
input. -/
structure SeparatingSubsetGloballyResolvedBlueprintCertificate
    (Gamma : DWeb V) (A0 : Set V) (kappa : Cardinal.{u}) where
  reference : Set Gamma.DPath
  blueprint : Blueprint.LinkageBlueprint Gamma reference kappa
  slice : Set V
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  reference_isWarp : Gamma.IsWarp reference
  edge_real : blueprint.IsEdgeReal
  real_terminals_target : blueprint.realPart.terminals ⊆ Gamma.target
  designated_source : A0 ⊆ Gamma.source
  designated_initial : A0 ⊆ blueprint.initialSet
  source_cover : blueprint.initialSet ∪
    Gamma.initialSet (blueprint.referenceRemainder slice) = Gamma.source
  terminal_boundary : blueprint.terminalSet ∪
    Gamma.terminalFrontier (blueprint.referenceRemainder slice) ⊆ stopover
  blueprint_endpointPure : ∀ p ∈ blueprint.paths,
    blueprint.IsPathBetween Gamma.source stopover p
  reference_endpointPure : ∀ p ∈ blueprint.referenceRemainder slice,
    IsPathBetween Gamma Gamma.source stopover p
  stopover_separator : IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave : (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

namespace SeparatingSubsetGloballyResolvedBlueprintCertificate

/-- Compile the corrected certificate to the separating half-way data. -/
theorem exists_separatingHalfwayLinkage
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (C : SeparatingSubsetGloballyResolvedBlueprintCertificate
      Gamma A0 kappa) :
    ∃ W : Set Gamma.DPath,
      IsSeparatingHalfwayStopover Gamma W C.stopover ∧
      LinksToTarget Gamma W A0 ∧
      HeightAtMost Gamma C.stopover kappa := by
  have hterminalTarget : C.blueprint.terminalSet ⊆ Gamma.target := by
    rw [← C.blueprint.realPart_terminals_eq_terminalSet_of_isEdgeReal
      C.edge_real]
    exact C.real_terminals_target
  have hlinks : C.blueprint.BlueprintLinksToTarget A0 :=
    C.blueprint.blueprintLinksToTarget_of_initial_terminal
      C.designated_source C.designated_initial C.blueprint_endpointPure
      hterminalTarget
  exact exists_separatingHalfwayStopover_of_terminalBlueprint_withReference_subset
    C.blueprint C.edge_real
    (C.blueprint.referenceRemainder C.slice)
    (C.blueprint.isWarp_referenceRemainder C.slice C.reference_isWarp)
    (C.blueprint.disjoint_referenceRemainder C.slice)
    C.source_cover C.terminal_boundary C.blueprint_endpointPure
    C.reference_endpointPure C.stopover_trimmed C.quotient_unhindered
    C.stopover_separator hlinks C.heightDelete_nonSource C.heightWave
    C.heightWave_isWave C.stopover_roofed C.heightDelete_card

/-- Forget the retained separator and recover the ordinary public half-way
linkage conclusion. -/
theorem exists_halfwayLinkage
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (C : SeparatingSubsetGloballyResolvedBlueprintCertificate
      Gamma A0 kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W := by
  obtain ⟨W, hstop, hlinks, hheight⟩ :=
    C.exists_separatingHalfwayLinkage
  exact ⟨W, halfwayLinkageOfAltitude_of_stopover
    hstop.stopover hlinks hheight⟩

end SeparatingSubsetGloballyResolvedBlueprintCertificate

/-- Construction interface for the corrected separating certificate. -/
def SeparatingSubsetGloballyResolvedBlueprintCompiler
    (Gamma : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    Nonempty (SeparatingSubsetGloballyResolvedBlueprintCertificate
      Gamma A0 kappa)

/-- The corrected compiler directly proves the ordinary source half-way
clause, without passing through an exact-frontier strengthening. -/
theorem halfwayClauseAt_of_separatingSubsetGloballyResolvedBlueprintCompiler
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : SeparatingSubsetGloballyResolvedBlueprintCompiler
      Gamma kappa) :
    HalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  exact (hcompile A0 hA0 hcard).some.exists_halfwayLinkage

end CardinalInduction
end Erdos599
