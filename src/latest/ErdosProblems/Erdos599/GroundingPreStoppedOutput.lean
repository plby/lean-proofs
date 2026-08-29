/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingWarpPruning
import ErdosProblems.Erdos599.GroundingAssertion818Decoder
import ErdosProblems.Erdos599.GroundingAssertion822UnusedRecord

/-!
# Pre-stopped component compiler for Assertion 8.22

The simultaneous switch is performed before stopping its components at the
bookkeeping boundary `BB`.  This is important: stopping the entire relation
at every point of `BB` can strand a later boundary point in a component which
meets `BB` twice.  The source proof instead establishes that the relevant
pre-stopped components already form a warp, cover `BB`, and meet `BB` at most
once.  Only then are those components pruned at their unique first `BB` hit.

This file isolates that final, purely path-theoretic compilation.  Its
hypotheses are exactly the remaining geometric obligations for the decoded
simultaneous switch; separatorhood itself is discharged by Assertion 8.18.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Compile a pre-stopped component warp into the exact output of Assertion
8.22.  Roots are required to avoid the reserved grounded source only for
components which meet `BB`, since all other components are discarded by the
final first-hit pruning. -/
theorem assertion822Output_of_preStoppedWarpGeometry
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (W : Set Gamma.DPath)
    (hW : Gamma.IsWarp W)
    (hroot : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support,
        x ∈ GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut) →
      p.initial ∈ Gamma.source \ {R.record.initial})
    (hcover : GroundingCut.BB
        (L.popularAuxiliaryInput hL.legal) S.cut ⊆ Gamma.vertexSet W)
    (hone : ∀ (p : Gamma.DPath), p ∈ W →
      (p.support ∩ GroundingCut.BB
        (L.popularAuxiliaryInput hL.legal) S.cut).Subsingleton) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  classical
  let B : Set V :=
    GroundingCut.BB (L.popularAuxiliaryInput hL.legal) S.cut
  have hsource : ∀ (p : Gamma.DPath), p ∈ W →
      (∃ x ∈ p.support, x ∈ B) → p.initial ∈ Gamma.source := by
    intro p hpW hpB
    exact (hroot p hpW hpB).1
  have hinitial : Gamma.initialSet
      (GroundingWarpPruning.prunedFamily W B hsource hW) ⊆
        Gamma.source \ {R.record.initial} := by
    exact GroundingWarpPruning.prunedFamily_initialSet_subset_of
      W B (Gamma.source \ {R.record.initial}) hsource hW hroot
  refine ⟨GroundingWarpPruning.assertion822OutputOfPruning
    (L.popularAuxiliaryInput hL.legal) S.cut W hW hsource hcover hone
    (GroundingAssertion818Decoder.assertion8_18
      L hL.legal S.cut S.separates)
    R.record.initial R.record_initial_mem_source ?_⟩
  intro hreserved
  obtain ⟨p, hpEssential, hpInitial⟩ := hreserved
  have hpPruned : p ∈ GroundingWarpPruning.prunedFamily W B hsource hW :=
    hpEssential.1
  have hallowed : R.record.initial ∈
      Gamma.source \ {R.record.initial} :=
    hinitial ⟨p, hpPruned, hpInitial⟩
  exact hallowed.2 (Set.mem_singleton R.record.initial)

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_of_preStoppedWarpGeometry
