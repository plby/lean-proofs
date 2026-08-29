/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedPreStoppedSwitchData
import ErdosProblems.Erdos599.GroundingProtectedPruning
import ErdosProblems.Erdos599.GroundingPreStoppedRealization

/-!
# Boundary geometry of an exact pre-stopped realization

The pre-stopped switch data explicitly retains every nonincident nominated
boundary point as a singleton.  Hence boundary coverage is automatic for an
exact realization, while the one-hit property remains precisely the genuine
reachability-antichain obligation of the source construction.

This module also composes that exact realization geometry with the
source-faithful unused-component pruning endpoint.  No stopped-relation
replacement or root-away-from-the-unused-source premise is introduced.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingErasedPreStoppedBoundaryGeometry

open Alternating GroundingErasedDecode
open GroundingErasedPreStoppedSwitchData

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Every nominated boundary point belongs to every exact realization of
the pre-stopped switch data.  Incident points are covered by relation edges;
all remaining points were retained explicitly as singleton components. -/
theorem boundary_subset_vertexSet
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    {B : Set V} {W : Set Gamma.DPath}
    (hR : (preStoppedSwitchData U S K B).RealizedBy W) :
    B ⊆ Gamma.vertexSet W := by
  apply GroundingBBGeometry.subset_vertexSet_of_realized_isolated_or_incident
    hR
  intro b hb
  by_cases hincident : b ∈
      RelationDecomposition.IncidentVertices
        (erasedSelectedSwitchedEdgesAt U S K ∅)
  · exact Or.inr hincident
  · exact Or.inl ⟨Or.inl hb, hincident⟩

/-- A reachability antichain meets every component of an exact pre-stopped
realization at most once. -/
theorem component_inter_boundary_subsingleton
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    {S : Popular.PopularSeparator U}
    {K : GroundingSelection.Controls S}
    {B : Set V} {W : Set Gamma.DPath}
    (hR : (preStoppedSwitchData U S K B).RealizedBy W)
    (hanti : GroundingRootedReachabilityWarp.IsReachabilityAntichain
      (erasedSelectedSwitchedEdgesAt U S K ∅) B) :
    ∀ p : Gamma.DPath, p ∈ W → (p.support ∩ B).Subsingleton := by
  intro p hp
  exact
    GroundingPreStoppedRealization.component_inter_subsingleton_of_realized_reachabilityAntichain
      hR hanti hp

/-- Exact realization-to-Assertion-8.22 compositor for the source's
unused-component branch.  Coverage is discharged by the switch-data
definition itself; the remaining inputs are the genuine global source,
one-hit, and unused-component invariants. -/
theorem assertion822Output_of_realized_unusedComponent
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    {K : GroundingSelection.Controls S}
    {W : Set Gamma.DPath}
    (hR : (preStoppedSwitchData U S K
      (GroundingCut.BB L S.cut)).RealizedBy W)
    (hinitial : Gamma.initialSet W ⊆ Gamma.source)
    (hone : ∀ p : Gamma.DPath, p ∈ W →
      (p.support ∩ GroundingCut.BB L S.cut).Subsingleton)
    (hseparator : Popular.IsSeparator Gamma (GroundingCut.BB L S.cut))
    (p : Gamma.DPath) (hpW : p ∈ W)
    (hpAvoids : Disjoint p.support (GroundingCut.BB L S.cut)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output L S.cut) := by
  refine
    GroundingProtectedPruning.assertion822Output_of_unusedComponent_avoids_BB
      L S.cut W hR.1 ?_ (boundary_subset_vertexSet hR) hone hseparator
        p.initial ?_ p hpW rfl hpAvoids
  · intro q hqW _hqMeets
    apply hinitial
    exact ⟨q, hqW, rfl⟩
  · apply hinitial
    exact ⟨p, hpW, rfl⟩

/-- Antichain-specialized form of the preceding compositor. -/
theorem assertion822Output_of_realized_unusedComponent_of_antichain
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    {K : GroundingSelection.Controls S}
    {W : Set Gamma.DPath}
    (hR : (preStoppedSwitchData U S K
      (GroundingCut.BB L S.cut)).RealizedBy W)
    (hinitial : Gamma.initialSet W ⊆ Gamma.source)
    (hanti : GroundingRootedReachabilityWarp.IsReachabilityAntichain
      (erasedSelectedSwitchedEdgesAt U S K ∅)
      (GroundingCut.BB L S.cut))
    (hseparator : Popular.IsSeparator Gamma (GroundingCut.BB L S.cut))
    (p : Gamma.DPath) (hpW : p ∈ W)
    (hpAvoids : Disjoint p.support (GroundingCut.BB L S.cut)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output L S.cut) := by
  apply assertion822Output_of_realized_unusedComponent S hR hinitial
  · exact component_inter_boundary_subsingleton hR hanti
  · exact hseparator
  · exact hpW
  · exact hpAvoids

end GroundingErasedPreStoppedBoundaryGeometry
end Erdos599

#print axioms Erdos599.GroundingErasedPreStoppedBoundaryGeometry.boundary_subset_vertexSet
#print axioms Erdos599.GroundingErasedPreStoppedBoundaryGeometry.assertion822Output_of_realized_unusedComponent
