/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedDecode
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# Reachability rigidity at the grounding boundary

The final grounding switch is stopped on both sides at its first contact with
`BB`: residual ladder departures are deleted by `boundaryOutgoingCutEdges`,
and decoded forward links retain only their source-side prefix.  Consequently
every point of `BB` is a sink, so no two distinct boundary points are
comparable by switched reachability.

This packages the exact unconditional antichain input used by the final
Assertion 8.22 realization.  The blocking-point corollary is stated from the
literal `BL` membership witness and is therefore independent of the concrete
presentation of the retained fragment family.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingBlockingReachability

open Alternating PopularGroundingBridge
open GroundingErasedDecode GroundingRootedReachabilityWarp

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- A directed reachability chain starting at a vertex with no outgoing edge
is necessarily reflexive. -/
theorem eq_of_reflTransGen_of_noOutgoing
    {E : Set (V × V)} {b c : V} (hno : ¬ HasOutgoing E b)
    (hbc : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) b c) :
    b = c := by
  rcases hbc.cases_head with hbc | ⟨d, hbd, _hdc⟩
  · exact hbc
  · exact False.elim (hno ⟨d, hbd⟩)

/-- The complete final grounding boundary is an unconditional reachability
antichain for the repaired switched relation. -/
theorem erasedSelectedSwitchedEdges_reachabilityAntichain
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    IsReachabilityAntichain
      (erasedSelectedSwitchedEdges U S K)
      (GroundingCut.BB L S.cut) := by
  intro b hb c _hc hbc
  exact eq_of_reflTransGen_of_noOutgoing
    (boundary_noOutgoing_switched U S K hb) hbc

/-- Exact blocking-point specialization.  Literal membership of the blocking
point in `BL` is the only fragment-side fact needed after boundary stopping. -/
theorem blockingPoint_reachability_rigid_of_mem_BL
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (P : L.Fragment)
    (hb : GroundingCut.blockingPoint L S.cut P ∈
      GroundingCut.BL L S.cut) :
    ∀ c ∈ GroundingCut.BB L S.cut,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdges U S K)
        (GroundingCut.blockingPoint L S.cut P) c →
      GroundingCut.blockingPoint L S.cut P = c := by
  intro c hc hbc
  exact erasedSelectedSwitchedEdges_reachabilityAntichain U S K
    (GroundingCut.BL_subset_BB L S.cut hb) hc hbc

end GroundingBlockingReachability
end Erdos599
