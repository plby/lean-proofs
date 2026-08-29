/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMergedReentry

/-!
# The literal quotient-continuation successor in the singular construction

For a terminal-clean whole-source half-way row, the next requested ambient
sources are first transported to the terminals of their current components.
Those terminals are legal sources of the quotient by the current stop-over,
and have exactly the same cardinality.  The lower half-way clause therefore
produces a quotient row.  Source-star with that row is an honest forward
extension and transports all requested quotient target links back to the
requested ambient sources.

This is the literal successor used in Assertion 9.17.  It makes no safe
deletion or future-avoidance assumption.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularLiteralQuotientSuccessor

open SingularBoundarySplit SingularContinuation SingularExtension
  SingularMatrix SingularMergedReentry SingularQuotientReentry
  SingularTargetLinkTransfer SingularTargetRowMachine

universe u

variable {V : Type u}

/-- One column of the literal quotient successor.  The lower half-way
witness is retained in the conclusion together with the continued ambient
row. -/
theorem exists_literalQuotientContinuationForNext
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hNorm : G.IsNormalized) {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (S : TargetRowStage G (Index kappa))
    (hsource : ∀ i,
      S.sources i ⊆ G.source ∧
        #(S.sources i) = scale kappa hkappa hsingular i)
    (D : Index kappa → Set V)
    (hD : ∀ i, IsSeparatingHalfwayStopover G (S.paths i) (D i))
    (hclean : ∀ i, TerminalCleanAt G (S.paths i) (D i))
    (i : Index kappa) :
    let B := nextTargetSources G fixed S i
    let A := requestedFrontier G (S.paths i) B
    ∃ U : Set (G.quotient (D i)).DPath, ∃ T : Set G.DPath,
      IsHalfwayLinkageOfAltitude (G.quotient (D i)) A
        (scale kappa hkappa hsingular i) U ∧
      G.IsWarp T ∧
      G.HasFiniteCharacter T ∧
      G.ForwardExtension (S.paths i) T ∧
      G.initialSet T = G.source ∧
      LinksToTarget G T B := by
  dsimp only
  let B := nextTargetSources G fixed S i
  let A := requestedFrontier G (S.paths i) B
  obtain ⟨U, hU⟩ := exists_quotientHalfwayForNext
    hlower hkappa hsingular hfixedWarp hfixedInitial S hsource D hD i
  obtain ⟨C, hC⟩ := hU.1
  let T : Set G.DPath :=
    continuation G (hD i).linkage (hD i).separator
      (hD i).stopover.minimal (hclean i) U hC.linkage.initialSet_eq
  have hBsource : B ⊆ G.source := by
    exact nextTargetSources_subset_source hfixedInitial S
      (fun j ↦ (hsource j).1) i
  have hAsource : A ⊆ (G.quotient (D i)).source := by
    exact requestedFrontier_subset_quotientSource (A := B) (hD i)
  have hroute : RoutesTerminals G (S.paths i) B A := by
    exact routesTerminals_requestedFrontier
      (S.finiteCharacter i) (S.initialSet i) hBsource
  have hTwarp : G.IsWarp T := by
    exact continuation_isWarp G (hD i).linkage (hD i).separator
      (hD i).stopover.minimal (hclean i) hC.linkage.isWarp
        hC.linkage.initialSet_eq
  have hTfinite : G.HasFiniteCharacter T := by
    exact continuation_finiteCharacter G (hD i).linkage
      (hD i).separator (hD i).stopover.minimal (hclean i)
        hC.linkage.finiteCharacter hC.linkage.initialSet_eq
  have hTforward : G.ForwardExtension (S.paths i) T := by
    exact forwardExtension_continuation G (hD i).linkage
      (hD i).separator (hD i).stopover.minimal (hclean i)
        U hC.linkage.initialSet_eq
  have hTinitial : G.initialSet T = G.source := by
    exact initialSet_continuation G (hD i).linkage
      (hD i).separator (hD i).stopover.minimal (hclean i)
        U hC.linkage.initialSet_eq
  have hTlinks : LinksToTarget G T B := by
    exact linksToTarget_continuation hNorm (hD i) (hclean i)
      hC.linkage.isWarp hC.linkage.finiteCharacter
      hC.linkage.initialSet_eq hAsource hBsource hroute hU.2.1
  exact ⟨U, T, hU, hTwarp, hTfinite, hTforward, hTinitial, hTlinks⟩

/-- Simultaneous target-row form of the literal quotient successor.  Choice
is only used to select the already-constructed successor independently in
each column. -/
theorem exists_literalQuotientTargetRowStage
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hkappa : aleph0 < kappa) (hsingular : kappa.IsSingular)
    {G : DWeb V} (hNorm : G.IsNormalized) {fixed : Set G.DPath}
    (hfixedWarp : G.IsWarp fixed)
    (hfixedInitial : G.initialSet fixed ⊆ G.source)
    (S : TargetRowStage G (Index kappa))
    (hsource : ∀ i,
      S.sources i ⊆ G.source ∧
        #(S.sources i) = scale kappa hkappa hsingular i)
    (D : Index kappa → Set V)
    (hD : ∀ i, IsSeparatingHalfwayStopover G (S.paths i) (D i))
    (hclean : ∀ i, TerminalCleanAt G (S.paths i) (D i)) :
    ∃ T : TargetRowStage G (Index kappa),
      T.sources = nextTargetSources G fixed S ∧
      ∀ i, G.ForwardExtension (S.paths i) (T.paths i) := by
  have hex : ∀ i, ∃ W : Set G.DPath,
      G.IsWarp W ∧ G.HasFiniteCharacter W ∧
      G.ForwardExtension (S.paths i) W ∧
      G.initialSet W = G.source ∧
      LinksToTarget G W (nextTargetSources G fixed S i) := by
    intro i
    obtain ⟨_U, W, _hU, hWwarp, hWfinite, hWforward,
        hWinitial, hWlinks⟩ :=
      exists_literalQuotientContinuationForNext
        hlower hkappa hsingular hNorm hfixedWarp hfixedInitial
          S hsource D hD hclean i
    exact ⟨W, hWwarp, hWfinite, hWforward, hWinitial, hWlinks⟩
  let paths : Index kappa → Set G.DPath :=
    fun i ↦ Classical.choose (hex i)
  let T : TargetRowStage G (Index kappa) :=
    { sources := nextTargetSources G fixed S
      paths := paths
      isWarp := fun i ↦ (Classical.choose_spec (hex i)).1
      finiteCharacter := fun i ↦ (Classical.choose_spec (hex i)).2.1
      initialSet := fun i ↦ (Classical.choose_spec (hex i)).2.2.2.1
      links := fun i ↦ (Classical.choose_spec (hex i)).2.2.2.2 }
  refine ⟨T, rfl, ?_⟩
  intro i
  exact (Classical.choose_spec (hex i)).2.2.1

#print axioms exists_literalQuotientContinuationForNext
#print axioms exists_literalQuotientTargetRowStage

end SingularLiteralQuotientSuccessor
end CardinalInduction
end Erdos599
