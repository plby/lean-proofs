/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary
import ErdosProblems.Erdos599.GroundingAssertion818Decoder
import ErdosProblems.Erdos599.GroundingAssertion822Output

/-!
# Minimal-frontier integration for Assertion 8.22

The full set `BB` is retained for the finite-descent separator proof.  A
globally minimal separating subset `T ⊆ BB` is then chosen, and the
boundary-parametric simultaneous relation is stopped exactly at `T`.

This module packages every already unconditional part of that reduction.
The sole remaining premise is the private-path/component exchange statement
which roots each point of `T` away from the stationary unused source.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingMinimalSeparatingBoundary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The literal Assertion 8.18 boundary contains a globally minimal
separating frontier. -/
theorem exists_assertion822MinimalFrontier
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    ∃ T : Set V,
      T ⊆ GroundingCut.BB
        (L.popularAuxiliaryInput hL.legal) S.cut ∧
      Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T := by
  apply exists_minimalSeparatingSubset
  exact GroundingAssertion818Decoder.assertion8_18
    L hL.legal S.cut S.separates

/-- Exact final reduction of the separator branch.  All construction and
bookkeeping inputs—Assertion 8.18, the minimal frontier, the unused grounded
record, adjacency, local bi-uniqueness, and terminal antichain—are discharged
internally.  Only source-rootedness away from that unused record remains. -/
theorem assertion822Output_of_minimalFrontierRooting
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (hroot : ∀
      (R : L.UnusedGroundedRecord hL S) (T : Set V),
      T ⊆ GroundingCut.BB
          (L.popularAuxiliaryInput hL.legal) S.cut →
      Popular.IsSeparator Gamma T →
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T →
      ∀ t ∈ T,
        ∃ a ∈ Gamma.source \ {R.record.initial},
          Relation.ReflTransGen
            (fun x y ↦ (x, y) ∈
              L.assertion822SwitchedEdgesAt hL S T) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (L.popularAuxiliaryInput hL.legal) S.cut) := by
  obtain ⟨R⟩ := L.exists_unusedGroundedRecord hL S
  obtain ⟨T, hTsub, hTsep, hTmin⟩ :=
    L.exists_assertion822MinimalFrontier hL S
  exact L.assertion822Output_of_frontierGeometry hL S R T hTsub hTsep
    (hroot R T hTsub hTsep hTmin)

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_assertion822MinimalFrontier
#print axioms Erdos599.DWeb.KappaLadder.assertion822Output_of_minimalFrontierRooting
