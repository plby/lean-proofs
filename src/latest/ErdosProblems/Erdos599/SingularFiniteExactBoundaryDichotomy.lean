/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteExactBoundaryGlobalExchange
import ErdosProblems.Erdos599.SingularFiniteBadComponentExchange

/-!
# The exact finite marked-exchange dichotomy

The whole-component colour repair has two genuinely different outcomes.
When the fresh augmentation component is outside the exceptional set, the
local repair globalizes to an exact-boundary target-linkage update and its
complement is a residual one-point augmentation avoiding the new carrier.
When the fresh component is exceptional, finite endpoint balance supplies
an opposite-coloured new path ending at the old designated frontier.

This file joins those two already-realized branches.  It deliberately makes
no wave claim about the residual augmentation: old carrier vertices freed by
the target-linkage update still require the separate finite roof correction.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteExactBoundaryDichotomy

open DWeb Alternating
open SliceCandidate SliceSpliceSource
open SingularComponentMixedAugmentation
open SingularFiniteBadComponentExchange
open SingularFiniteEndpointColorRepair
open SingularFiniteExactBoundaryGlobalExchange
open SingularMarkedResidualFiniteFactor
open SingularMarkedResidualSimultaneousColourRepair
open SingularMarkedResidualTargetColourRepair
open SingularMarkedResidualTouchedPaths
open SingularResidualWaveExchange

universe u

variable {V : Type u}

/-- The complete fixed-window output of the finite two-colour repair.

The first alternative is the successful global exact-boundary exchange.  In
the second alternative the fresh component is retained on the old side, and
the displayed `Qplus` member crosses from residual initial colour to the old
designated terminal colour. -/
theorem globalExactBoundaryExchange_or_badComponent
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U)
    {l : List (OneHoleResidualState V)} {Qplus : Set G.DPath}
    (hQfinite : Qplus.Finite)
    (hlocal :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      K.IsOnePointAugmentation
        (touchedDesignatedPaths K (P ∪ L) l) Qplus)
    (hRTQ :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      Disjoint
        (K.vertexSet (untouchedDesignatedPaths K (P ∪ L) l))
        (K.vertexSet Qplus))
    (hglobal :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      K.IsOnePointAugmentation (P ∪ L)
        (untouchedDesignatedPaths K (P ∪ L) l ∪ Qplus)) :
    let L := G.liftDeleteFamily (G.vertexSet P) U
    let K := G.retarget
      (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
    let TT := touchedDesignatedPaths K (P ∪ L) l
    let TP := touchedDesignatedPaths K P l
    let AP := K.initialSet TP
    let BT := K.terminalFrontier TP
    let YA := initialRestriction K Qplus AP
    let E := badTerminalColour K YA BT
    let D := exceptionalComponentVertices K TT Qplus E
    let Z := componentMixedFamily K TT Qplus E
    IsLinkageBetween K AP BT (initialRestriction K Z AP) ∧
      ((∃ Pplus Jplus Rplus : Set K.DPath,
          IsLinkageBetween G A G.target Pplus ∧
          (G.vertexSet P \ G.vertexSet Pplus).Finite ∧
          K.initialSet Pplus = K.initialSet P ∧
          K.terminalFrontier Pplus = K.terminalFrontier P ∧
          Pplus ⊆ Jplus ∧
          K.IsOnePointAugmentation (P ∪ L) Jplus ∧
          Rplus = Jplus \ Pplus ∧
          K.IsOnePointAugmentation L Rplus ∧
          Disjoint (K.vertexSet Pplus) (K.vertexSet Rplus)) ∨
        ∃ a b : V,
          a ∈ K.source \ K.initialSet TT ∧
          b ∈ K.target \ K.terminalFrontier TT ∧
          b ∈ AlternatingComponents.component TT Qplus a ∧
          K.initialSet Qplus = insert a (K.initialSet TT) ∧
          K.terminalFrontier Qplus = insert b (K.terminalFrontier TT) ∧
          a ∈ D ∧ b ∈ D ∧
          K.IsWarp Z ∧ K.HasFiniteCharacter Z ∧
          K.initialSet Z = K.initialSet TT ∧
          K.terminalFrontier Z = K.terminalFrontier TT ∧
          ∃ p ∈ Qplus, p.initial ∉ AP ∧
            p.initial ∈ AlternatingComponents.component TT Qplus a ∧
            ∃ q : DirectedPath.FinitePath K.graph,
              p = .inl q ∧ q.finish ∈ BT) := by
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TT := touchedDesignatedPaths K (P ∪ L) l
  let TP := touchedDesignatedPaths K P l
  let AP := K.initialSet TP
  let BT := K.terminalFrontier TP
  let YA := initialRestriction K Qplus AP
  let E := badTerminalColour K YA BT
  let D := exceptionalComponentVertices K TT Qplus E
  let Z := componentMixedFamily K TT Qplus E
  obtain ⟨hrepair, a, b, ha, hb, hab, hinit, hterm, hbranch⟩ :=
    markedResidual_wholeComponentMix_dichotomy_with_oppositeCross
      hNorm hA hP hU hUfin hQfinite hlocal hglobal
  refine ⟨hrepair, ?_⟩
  rcases hbranch with houtside | hinside
  · left
    obtain ⟨haD, hbD, _hlocalZ⟩ := houtside
    obtain ⟨_a, _ha, _b, _hb, hQwarp, hQcharacter, _, _⟩ := hlocal
    exact exists_globalExactBoundaryExchange_of_marked_outside
      hNorm hA hP hU hUfin ha hb hQwarp hQcharacter hinit hterm
        hRTQ hglobal haD hbD
  · right
    obtain ⟨haD, hbD, hZwarp, hZcharacter, hZinit, hZterm,
      p, hpQ, hpNotAP, hpComponent, q, hpq, hqBT⟩ := hinside
    exact ⟨a, b, ha, hb, hab, hinit, hterm, haD, hbD, hZwarp, hZcharacter,
      hZinit, hZterm, p, hpQ, hpNotAP, hpComponent, q, hpq, hqBT⟩

#print axioms globalExactBoundaryExchange_or_badComponent

end SingularFiniteExactBoundaryDichotomy
end CardinalInduction
end Erdos599
