/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingReservedRecordControls
import ErdosProblems.Erdos599.GroundingAssertion822Output

/-!
# Assertion 8.22 geometry with a reserved grounded record

This is the concrete output interface for the source-faithful selector.
The selected local fan paths avoid the reserved grounded record off their
own apex, while the switched relation stops at the globally chosen frontier
`T`.  Adjacency, local bi-uniqueness, and the terminal antichain are all
unconditional; only source-rooted reachability remains as an input.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode
open GroundingErasedForwardConflict GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The `T`-stopped simultaneous relation selected while reserving `R`. -/
abbrev assertion822ReservedSwitchedEdgesAt
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) (T : Set V) : Set (V × V) :=
  erasedSelectedSwitchedEdgesAt (L.popularAuxiliaryIndexed hL) S
    (L.reservedGroundedControls hL S R) T

theorem assertion822ReservedSwitchedEdgesAt_subset_adj
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) (T : Set V) :
    L.assertion822ReservedSwitchedEdgesAt hL S R T ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  exact erasedSelectedSwitchedEdgesAt_subset_adj
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) T

theorem assertion822ReservedSwitchedEdgesAt_biUnique
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) (T : Set V) :
    Relator.BiUnique (fun x y ↦
      (x, y) ∈ L.assertion822ReservedSwitchedEdgesAt hL S R T) := by
  exact erasedSelectedSwitchedEdgesAt_biUnique
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) T
        (L.popularAuxiliary_proxyPathsFaithful hL)

theorem assertion822ReservedSwitchedEdgesAt_noOutgoing
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    {t : V} (ht : t ∈ T) :
    ¬ HasOutgoing (L.assertion822ReservedSwitchedEdgesAt hL S R T) t := by
  exact boundary_noOutgoing_switchedAt
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) T ht

theorem assertion822ReservedSwitchedEdgesAt_reachabilityAntichain
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) (T : Set V) :
    IsReachabilityAntichain
      (L.assertion822ReservedSwitchedEdgesAt hL S R T) T := by
  intro b hb c _hc hbc
  exact GroundingBlockingReachability.eq_of_reflTransGen_of_noOutgoing
    (L.assertion822ReservedSwitchedEdgesAt_noOutgoing hL S R T hb) hbc

/-- Exact reserved-selector Assertion 8.22 compiler. -/
theorem assertion822Output_of_reservedFrontierGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S) (T : Set V)
    (hTsubset : T ⊆
      GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut)
    (hTseparator : Popular.IsSeparator Gamma T)
    (hroot : ∀ t ∈ T,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedSwitchedEdgesAt hL S R T) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  apply GroundingAssertion822Output.exists_of_rootedReachability
    (L.popularAuxiliaryInput hL.legal) S.cut
    (L.assertion822ReservedSwitchedEdgesAt hL S R T)
    (Gamma.source \ {R.record.initial}) T
    (L.assertion822ReservedSwitchedEdgesAt_subset_adj hL S R T)
    (L.assertion822ReservedSwitchedEdgesAt_biUnique hL S R T)
    Set.sdiff_subset hTsubset hTseparator
    (L.assertion822ReservedSwitchedEdgesAt_reachabilityAntichain hL S R T)
    hroot R.record.initial R.record_initial_mem_source
  simp

end DWeb.KappaLadder
end Erdos599

