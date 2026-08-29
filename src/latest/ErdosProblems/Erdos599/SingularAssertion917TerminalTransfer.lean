/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMergedReentry

/-!
# Designated terminal transport for Assertion 9.17

For a current half-way row `W` with stop-over `D`, the source set passed to
the lower half-way clause in `G / D` is not the next ambient request `B`
itself.  It is the set of terminals of the `W`-components starting in `B`,
namely `requestedFrontier G W B`.  This set lies in the quotient source and
has exactly the same cardinality as `B`.

The lower half-way linkage on those terminal images can then be appended to
`W` by `SingularContinuation.continuation`.  The final theorem packages the
cardinal change of coordinates and the `LinksToTarget` transport in the
form used by one column of Assertion 9.17.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularAssertion917TerminalTransfer

open SingularBoundarySplit SingularContinuation SingularMergedReentry
  SingularQuotientReentry SingularTargetLinkTransfer
  SingularTargetRowMachine

universe u

variable {V : Type u}

/-- Apply the lower half-way clause to the exact terminal image of the next
ambient request set, and pull all of its target links back through the
current half-way row.

The continued row is the unrestricted target row.  No terminal-clean claim
at the new quotient stop-over is made here; that is the separate
completed/pending re-entry output. -/
theorem exists_lowerHalfwayContinuation_to_designatedSources
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrhoKappa : rho < kappa)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D B : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    (hB : B ⊆ G.source)
    (hrho : aleph0 ≤ rho) (hBcard : #B = rho) :
    let A := requestedFrontier G W B
    #A = rho ∧ A ⊆ (G.quotient D).source ∧
      ∃ (U : Set (G.quotient D).DPath) (E : Set V),
        ∃ hE : IsHalfwayStopover (G.quotient D) U E,
        IsHalfwayLinkageOfAltitude (G.quotient D) A rho U ∧
        let W' := continuation G hD.linkage hD.separator
          hD.stopover.minimal hclean U hE.linkage.initialSet_eq
        G.IsWarp W' ∧ G.HasFiniteCharacter W' ∧
          G.ForwardExtension W W' ∧
          G.initialSet W' = G.source ∧ LinksToTarget G W' B := by
  let A := requestedFrontier G W B
  have hAcard : #A = rho := by
    dsimp only [A]
    rw [mk_requestedFrontier_eq hD.linkage hB, hBcard]
  have hAsub : A ⊆ (G.quotient D).source :=
    requestedFrontier_subset_quotientSource hD
  have hlowerRho := hlower rho hrhoKappa
    (G.quotient D) hD.quotient_unhindered
  obtain ⟨U, hU⟩ := hlowerRho.halfway hrho A hAsub hAcard
  obtain ⟨E, hE⟩ := hU.1
  let W' := continuation G hD.linkage hD.separator
    hD.stopover.minimal hclean U hE.linkage.initialSet_eq
  have hW'warp : G.IsWarp W' :=
    continuation_isWarp G hD.linkage hD.separator
      hD.stopover.minimal hclean hE.linkage.isWarp
        hE.linkage.initialSet_eq
  have hW'finite : G.HasFiniteCharacter W' :=
    continuation_finiteCharacter G hD.linkage hD.separator
      hD.stopover.minimal hclean hE.linkage.finiteCharacter
        hE.linkage.initialSet_eq
  have hW'forward : G.ForwardExtension W W' :=
    forwardExtension_continuation G hD.linkage hD.separator
      hD.stopover.minimal hclean U hE.linkage.initialSet_eq
  have hW'initial : G.initialSet W' = G.source :=
    initialSet_continuation G hD.linkage hD.separator
      hD.stopover.minimal hclean U hE.linkage.initialSet_eq
  have hroute : RoutesTerminals G W B A := by
    exact routesTerminals_requestedFrontier
      hD.linkage.finiteCharacter hD.linkage.initialSet_eq hB
  have hW'links : LinksToTarget G W' B :=
    linksToTarget_continuation hNorm hD hclean
      hE.linkage.isWarp hE.linkage.finiteCharacter
      hE.linkage.initialSet_eq hAsub hB hroute hU.2.1
  exact ⟨hAcard, hAsub, U, E, hE, hU, hW'warp, hW'finite,
    hW'forward, hW'initial, hW'links⟩

#print axioms exists_lowerHalfwayContinuation_to_designatedSources

end SingularAssertion917TerminalTransfer
end CardinalInduction
end Erdos599
