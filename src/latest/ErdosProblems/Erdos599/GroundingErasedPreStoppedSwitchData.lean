/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedForwardConflict
import ErdosProblems.Erdos599.CyclowarpDecomposition

/-!
# Exact switch data before grounding-boundary stopping

The source construction for Assertion 8.22 applies all selected exchanges
before pruning components at their first `BB` contact.  The older
`erasedSelectedSwitchData` packages `erasedSelectedSwitchedEdges`, whose
definition already deletes every departure from `BB`; it therefore cannot
serve as the realization data for the pre-stopped construction.

This file packages the actual empty-frontier relation
`erasedSelectedSwitchedEdgesAt U S K ∅`.  Besides the original isolated
ladder components, a caller may nominate a boundary set `B`; points of `B`
which are not incident with the relation are represented as singleton
components.  This is exactly the convention needed by the later BB-coverage
argument without prematurely stopping the relation at `B`.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedPreStoppedSwitchData

open Alternating GroundingErasedDecode GroundingErasedForwardConflict

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Boundary points and original singleton ladder components which are not
incident with the exact empty-frontier simultaneous relation. -/
def preStoppedIsolated
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (B : Set V) : Set V :=
  (B ∪ Alternating.isolatedVertices L.ladder.paths) \
    Alternating.RelationDecomposition.IncidentVertices
      (erasedSelectedSwitchedEdgesAt U S K ∅)

theorem preStoppedIsolated_nonincident
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (B : Set V) :
    ∀ x ∈ preStoppedIsolated U S K B, ∀ y,
      (x, y) ∉ erasedSelectedSwitchedEdgesAt U S K ∅ ∧
        (y, x) ∉ erasedSelectedSwitchedEdgesAt U S K ∅ := by
  intro x hx y
  refine ⟨?_, ?_⟩
  · intro hxy
    exact hx.2 ⟨y, Or.inl hxy⟩
  · intro hyx
    exact hx.2 ⟨y, Or.inr hyx⟩

/-- Exact graph-level data of the selected simultaneous switch before any
grounding-boundary stopping. -/
def preStoppedSwitchData
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (B : Set V) :
    Alternating.SwitchData Gamma where
  edges := erasedSelectedSwitchedEdgesAt U S K ∅
  edges_in_graph := erasedSelectedSwitchedEdgesAt_subset_adj U S K ∅
  isolated := preStoppedIsolated U S K B

@[simp] theorem preStoppedSwitchData_edges
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (B : Set V) :
    (preStoppedSwitchData U S K B).edges =
      erasedSelectedSwitchedEdgesAt U S K ∅ :=
  rfl

@[simp] theorem preStoppedSwitchData_isolated
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (B : Set V) :
    (preStoppedSwitchData U S K B).isolated =
      preStoppedIsolated U S K B :=
  rfl

/-- The two global relation obstructions not supplied by the generic local
bi-uniqueness theorem.  Every field refers to the literal empty-frontier
relation. -/
structure Compatible
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) : Prop where
  noDirectedCycle :
    ¬ Alternating.ContainsDirectedCycle
      (erasedSelectedSwitchedEdgesAt U S K ∅)
  noReverseDirectedRay :
    ¬ Alternating.ContainsReverseDirectedRay
      (erasedSelectedSwitchedEdgesAt U S K ∅)

/-- An exact realization of the pre-stopped relation.  Local bi-uniqueness
is already available for every control package; compatibility therefore
contains only the two honest global conditions. -/
theorem Compatible.exists_realization
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    (hfaith : GroundingSimultaneousDecode.ProxyPathsFaithful L)
    (B : Set V) (h : Compatible U S K) :
    ∃ W : Set Gamma.DPath,
      Alternating.SwitchData.RealizedBy
        (preStoppedSwitchData U S K B) W := by
  obtain ⟨W, hW, hE, hI⟩ :=
    Alternating.RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
      Gamma (erasedSelectedSwitchedEdgesAt U S K ∅)
      (preStoppedIsolated U S K B)
      (erasedSelectedSwitchedEdgesAt_subset_adj U S K ∅)
      (erasedSelectedSwitchedEdgesAt_biUnique U S K ∅ hfaith)
      h.noDirectedCycle h.noReverseDirectedRay
      (preStoppedIsolated_nonincident U S K B)
  exact ⟨W, hW, hE, hI⟩

end GroundingErasedPreStoppedSwitchData
end Erdos599

#print axioms Erdos599.GroundingErasedPreStoppedSwitchData.Compatible.exists_realization
