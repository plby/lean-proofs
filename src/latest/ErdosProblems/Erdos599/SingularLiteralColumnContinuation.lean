/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularBoundarySplit
import ErdosProblems.Erdos599.SingularContinuation
import ErdosProblems.Erdos599.SingularQuotientReentry
import ErdosProblems.Erdos599.SingularTargetLinkTransfer

/-!
# The literal quotient continuation in one singular column

The successor sentence in Assertion 9.17 changes coordinates before it
applies the lower-cardinal half-way clause.  If `B` is the next set of
*original* sources, the request made in the quotient is not `B` itself: it
is the set of terminals of the current components rooted in `B`.  A
full-source linkage identifies these two sets bijectively.  The lower
half-way linkage in the quotient can consequently be source-starred onto
the current row, giving a literal forward extension which links `B` to the
ambient target.

This file packages exactly that construction.  In particular, `paths_eq`
records that the new row is `SingularContinuation.continuation`, rather
than an unrelated row selected after the quotient witness.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularLiteralColumnContinuation

open SingularBoundarySplit SingularContinuation SingularQuotientReentry
  SingularTargetLinkTransfer

universe u

variable {V : Type u}

/-- The current row maps an original request set bijectively to the
terminal-coordinate request used in its quotient. -/
theorem terminalRequest_card
    {G : DWeb V} {W : Set G.DPath} {D B : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hB : B ⊆ G.source) :
    #(requestedFrontier G W B) = #B :=
  mk_requestedFrontier_eq hD.linkage hB

/-- Every requested original source is carried by its current component to
one of the terminal-coordinate requests. -/
theorem routes_terminalRequest
    {G : DWeb V} {W : Set G.DPath} {D B : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hB : B ⊆ G.source) :
    RoutesTerminals G W B (requestedFrontier G W B) := by
  intro b hb
  obtain ⟨p, hp, hpInitial, t, hpTerminal⟩ :=
    exists_path_to_requestedFrontier hD.linkage hB hb
  obtain ⟨f, rfl⟩ := hD.linkage.finiteCharacter hp.1
  refine ⟨f, hp.1, hpInitial, ?_⟩
  have hfinish : f.finish = t.1 := Option.some.inj hpTerminal
  exact hfinish ▸ t.2

/-- One literal column successor.  The quotient witness is retained, as is
the equation identifying the ambient output with source-star continuation.
-/
structure ColumnContinuation
    (G : DWeb V) {W : Set G.DPath} {D B : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    (rho : Cardinal.{u}) where
  quotientPaths : Set (G.quotient D).DPath
  quotientHalfway : IsHalfwayLinkageOfAltitude
    (G.quotient D) (requestedFrontier G W B) rho quotientPaths
  quotientBoundary : Set V
  quotientStopover : IsHalfwayStopover
    (G.quotient D) quotientPaths quotientBoundary
  paths : Set G.DPath
  paths_eq : paths = continuation G hD.linkage hD.separator
    hD.stopover.minimal hclean quotientPaths
      quotientStopover.linkage.initialSet_eq
  isWarp : G.IsWarp paths
  finiteCharacter : G.HasFiniteCharacter paths
  initialSet : G.initialSet paths = G.source
  forward : G.ForwardExtension W paths
  links : LinksToTarget G paths B

/-- The lower-cardinal half-way clause, applied after the terminal
coordinate change, constructs the literal successor in one column.
-/
theorem exists_columnContinuation
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : aleph0 ≤ rho) (hrhoKappa : rho < kappa)
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {D B : Set V}
    (hD : IsSeparatingHalfwayStopover G W D)
    (hclean : TerminalCleanAt G W D)
    (hB : B ⊆ G.source) (hBcard : #B = rho) :
    Nonempty (ColumnContinuation G (B := B) hD hclean rho) := by
  let A : Set V := requestedFrontier G W B
  have hAsource : A ⊆ (G.quotient D).source := by
    rw [hD.quotient_source_eq]
    rintro x ⟨p, hp, hpx⟩
    exact hD.linkage.terminalFrontier_subset ⟨p, hp.1, hpx⟩
  have hAcard : #A = rho := by
    dsimp only [A]
    rw [terminalRequest_card hD hB, hBcard]
  have hLower := hlower rho hrhoKappa
    (G.quotient D) hD.quotient_unhindered
  obtain ⟨U, hU⟩ := hLower.2 hrho A hAsource hAcard
  obtain ⟨E, hE⟩ := hU.1
  let P : Set G.DPath :=
    continuation G hD.linkage hD.separator hD.stopover.minimal
      hclean U hE.linkage.initialSet_eq
  have hPwarp : G.IsWarp P :=
    continuation_isWarp G hD.linkage hD.separator hD.stopover.minimal
      hclean hE.linkage.isWarp hE.linkage.initialSet_eq
  have hPfinite : G.HasFiniteCharacter P :=
    continuation_finiteCharacter G hD.linkage hD.separator
      hD.stopover.minimal hclean hE.linkage.finiteCharacter
        hE.linkage.initialSet_eq
  have hPinitial : G.initialSet P = G.source :=
    initialSet_continuation G hD.linkage hD.separator
      hD.stopover.minimal hclean U hE.linkage.initialSet_eq
  have hPforward : G.ForwardExtension W P :=
    forwardExtension_continuation G hD.linkage hD.separator
      hD.stopover.minimal hclean U hE.linkage.initialSet_eq
  have hPlinks : LinksToTarget G P B :=
    linksToTarget_continuation hNorm hD hclean
      hE.linkage.isWarp hE.linkage.finiteCharacter
      hE.linkage.initialSet_eq hAsource hB
      (routes_terminalRequest hD hB) hU.2.1
  exact ⟨{
    quotientPaths := U
    quotientHalfway := hU
    quotientBoundary := E
    quotientStopover := hE
    paths := P
    paths_eq := rfl
    isWarp := hPwarp
    finiteCharacter := hPfinite
    initialSet := hPinitial
    forward := hPforward
    links := hPlinks
  }⟩

#print axioms terminalRequest_card
#print axioms routes_terminalRequest
#print axioms exists_columnContinuation

end SingularLiteralColumnContinuation
end CardinalInduction
end Erdos599
