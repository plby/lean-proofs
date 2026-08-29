/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteExactBoundaryDichotomy
import ErdosProblems.Erdos599.SingularFiniteFreedCarrierCorrection
import ErdosProblems.Erdos599.SingularMaximalWaveTotalFiniteExchange
import ErdosProblems.Erdos599.SingularResidualAugmentationFreedCarrierCorrection

/-!
# The unconditional finite repair trichotomy

This module assembles the finite marked exchange through the exact
two-colour repair and the freed-carrier correction.  Starting from a
hindered provisional target linkage, one obtains exactly one of three
constructive outcomes:

* a replacement linkage whose residual maximal-wave profile is strictly
  larger;
* a replacement linkage and an explicit target path escaping from a freed
  carrier vertex while avoiding the proposed residual frontier;
* the finite exceptional component together with its opposite-colour
  crossing path.

No wave-continuity or arbitrary-row safety assertion is used.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteRepairTrichotomy

open DWeb Alternating
open SliceCandidate SliceSpliceSource
open SingularComponentMixedAugmentation
open SingularFiniteBadComponentExchange
open SingularFiniteEndpointColorRepair
open SingularFiniteExactBoundaryDichotomy
open SingularFiniteFreedCarrierCorrection
open SingularMarkedResidualFiniteFactor
open SingularMarkedResidualSimultaneousColourRepair
open SingularMarkedResidualTouchedPaths
open SingularMaximalWaveTotalFiniteExchange
open SingularResidualAugmentationFreedCarrierCorrection

universe u

variable {V : Type u}

/-- A finite repair has succeeded at the maximal-wave profile level. -/
def HasStrictResidualProfileUpdate
    (G : DWeb V) (A : Set V) (P : Set G.DPath)
    (U : Set ((G.delete (G.vertexSet P)).DPath)) : Prop :=
  ∃ P' : Set G.DPath,
    IsLinkageBetween G A G.target P' ∧
      ∃ M' : (G.delete (G.vertexSet P')).Wave, IsMax M' ∧
        (G.delete (G.vertexSet P)).initialSet U ⊂
          (G.delete (G.vertexSet P')).initialSet M'.1

/-- The exact unresolved outside-branch datum: a path starts at a freed old
carrier vertex and avoids the whole proposed residual frontier. -/
def HasEscapingFreedCarrierUpdate
    (G : DWeb V) (A : Set V) (P : Set G.DPath)
    (U : Set ((G.delete (G.vertexSet P)).DPath)) : Prop :=
  ∃ P' Rplus : Set G.DPath,
    ∃ hAvoid : Disjoint (G.vertexSet P') (G.vertexSet Rplus),
    IsLinkageBetween G A G.target P' ∧
    (G.vertexSet P \ G.vertexSet P').Finite ∧
    Disjoint G.source (G.vertexSet P \ G.vertexSet P') ∧
    (G.retarget
      (G.target ∪
        (G.delete (G.vertexSet P)).terminalFrontier U)).IsOnePointAugmentation
      (G.liftDeleteFamily (G.vertexSet P) U) Rplus ∧
    ∃ x : V, x ∈ G.vertexSet P \ G.vertexSet P' ∧ x ∉ G.source ∧
      ∃ p : DirectedPath.FinitePath (G.delete (G.vertexSet P')).graph,
        (G.delete (G.vertexSet P')).IsTargetPathFrom x p ∧
          Disjoint p.support
            ((G.delete (G.vertexSet P')).terminalFrontier
              (G.restrictDeleteFamily
                (G.vertexSet P') Rplus hAvoid.symm))

/-- The exact exceptional finite-component datum retained by the inside
branch.  The local/global augmentations are included so a subsequent
selective switch can reuse the same marked window. -/
def HasExceptionalColourBlock
    (G : DWeb V) (P : Set G.DPath)
    (U : Set ((G.delete (G.vertexSet P)).DPath)) : Prop :=
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  ∃ l : List (OneHoleResidualState V), ∃ Qplus : Set K.DPath,
    Qplus.Finite ∧
    K.IsOnePointAugmentation
      (touchedDesignatedPaths K (P ∪ L) l) Qplus ∧
    Disjoint
      (K.vertexSet (untouchedDesignatedPaths K (P ∪ L) l))
      (K.vertexSet Qplus) ∧
    K.IsOnePointAugmentation (P ∪ L)
      (untouchedDesignatedPaths K (P ∪ L) l ∪ Qplus) ∧
    let TT := touchedDesignatedPaths K (P ∪ L) l
    let TP := touchedDesignatedPaths K P l
    let AP := K.initialSet TP
    let BT := K.terminalFrontier TP
    let YA := initialRestriction K Qplus AP
    let E := badTerminalColour K YA BT
    let D := exceptionalComponentVertices K TT Qplus E
    let Z := componentMixedFamily K TT Qplus E
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
          p = .inl q ∧ q.finish ∈ BT

/-- A hindered provisional target linkage admits a finite repair which
either strictly enlarges the residual maximal-wave profile or isolates the
finite exceptional colour block.  The former freed-carrier escape branch is
absorbed by `exists_wave_initialSet_superset_of_finite_roof_defect`. -/
theorem exists_strictProfile_or_exceptionalBlock
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧ (G.delete (G.vertexSet P)).IsHindrance M.1 ∧
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      (G.delete (G.vertexSet P)).HasFiniteCharacter U ∧
      (HasStrictResidualProfileUpdate G A P U ∨
        HasExceptionalColourBlock G P U) := by
  obtain ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP,
      hl, hcontact, hwindow, hTfinite, hTPnonempty, Qplus,
      hQfinite, hlocal, hcarrierFinite, hRTQ, hglobal,
      hinit, hterminal⟩ :=
    exists_totalFiniteWindowExchangeExact_of_residual_hindered
      hNorm hG hA hP hresidual
  let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
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
  obtain ⟨hrepair, hbranch⟩ :=
    globalExactBoundaryExchange_or_badComponent
      hNorm hA hP hUh hUfin hQfinite hlocal hRTQ hglobal
  refine ⟨M, hMmax, hMh, hUh, hUfin, ?_⟩
  rcases hbranch with houtside | hinside
  · obtain ⟨Pplus, Jplus, Rplus, hPplus, hFreedFinite, hPplusInitial,
      hPplusTerminal, hPplusJplus, hJplus, hRplusEq,
      hRplus, hRplusAvoid⟩ := houtside
    have hprogress :=
      exists_maximalWave_strictly_extending_exactResidualAugmentation_of_finite
        hNorm hA hP hPplus hUh.1 hRplus hRplusAvoid hFreedFinite
    exact Or.inl ⟨Pplus, hPplus, hprogress⟩
  · right
    obtain ⟨a', b', ha', hb', hab', hinit', hterm', haD, hbD, hZwarp,
      hZcharacter, hZinitial, hZterminal, p, hpQplus,
      hpNotAP, hpComponent, q, hpq, hqBT⟩ := hinside
    exact ⟨l, Qplus, hQfinite, hlocal, hRTQ, hglobal,
      a', b', ha', hb', hab', hinit', hterm', haD, hbD, hZwarp,
      hZcharacter, hZinitial, hZterminal, p, hpQplus,
      hpNotAP, hpComponent, q, hpq, hqBT⟩

/-- Backward-compatible three-way statement.  Its middle alternative is no
longer needed: every finite outside exchange is absorbed into strict profile
progress. -/
theorem exists_strictProfile_or_escapingFreedCarrier_or_exceptionalBlock
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧ (G.delete (G.vertexSet P)).IsHindrance M.1 ∧
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      (G.delete (G.vertexSet P)).HasFiniteCharacter U ∧
      (HasStrictResidualProfileUpdate G A P U ∨
        HasEscapingFreedCarrierUpdate G A P U ∨
        HasExceptionalColourBlock G P U) := by
  obtain ⟨M, hMmax, hMh, hUh, hUfin, hprogress | hexceptional⟩ :=
    exists_strictProfile_or_exceptionalBlock
      hNorm hG hA hP hresidual
  · exact ⟨M, hMmax, hMh, hUh, hUfin, Or.inl hprogress⟩
  · exact ⟨M, hMmax, hMh, hUh, hUfin,
      Or.inr (Or.inr hexceptional)⟩

#print axioms exists_strictProfile_or_exceptionalBlock
#print axioms exists_strictProfile_or_escapingFreedCarrier_or_exceptionalBlock

end SingularFiniteRepairTrichotomy
end CardinalInduction
end Erdos599
