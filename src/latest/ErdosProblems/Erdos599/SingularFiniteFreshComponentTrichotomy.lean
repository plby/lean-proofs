/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteFreshComponentGlobalExchange
import ErdosProblems.Erdos599.SingularFiniteRepairTrichotomy
import ErdosProblems.Erdos599.SingularToggleCarrierProvenance
import ErdosProblems.Erdos599.SingularExactBoundaryFreedCarrier

/-!
# Finite repair trichotomy with fresh-component provenance

The ordinary finite trichotomy records an escaping freed carrier vertex but
forgets where that vertex came from.  By using the fresh-component exchange,
the escaping vertex lies in the unique alternating component containing the
fresh source and terminal of the marked augmentation.  This file retains the
original reduced marked route and the exact finite augmentation as well.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteFreshComponentTrichotomy

open DWeb Alternating
open SliceCandidate SliceSpliceSource
open SingularFiniteBadComponentExchange
open SingularFiniteEndpointColorRepair
open SingularFiniteFreshComponentGlobalExchange
open SingularFiniteFreedCarrierCorrection
open SingularFiniteRepairTrichotomy
open SingularExactBoundaryFreedCarrier
open SingularMarkedResidualFiniteFactor
open SingularMarkedResidualSimultaneousColourRepair
open SingularMarkedResidualTouchedPaths
open SingularMaximalWaveTotalFiniteExchange
open SingularResidualAugmentationFreedCarrierCorrection
open SingularResidualWaveExchange
open SingularToggleCarrierProvenance

universe u

variable {V : Type u}

/-- The escaping roof defect with complete finite marked provenance.  In
particular, the freed vertex is in the same alternating component as the
fresh missing residual source. -/
def HasFreshComponentEscapingUpdate
    (G : DWeb V) (A : Set V) (P : Set G.DPath)
    (U : Set ((G.delete (G.vertexSet P)).DPath)) : Prop :=
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  ∃ a b : V, ∃ l : List (OneHoleResidualState V),
    IsReducedMarkedRoute K (P ∪ L) a b l ∧
    a ∈ K.source \ K.initialSet
      (touchedDesignatedPaths K (P ∪ L) l) ∧
    b ∈ K.target \ K.terminalFrontier
      (touchedDesignatedPaths K (P ∪ L) l) ∧
    ¬ Disjoint (oneHoleRouteBackwardEdges K (P ∪ L) l)
      (familyEdges P) ∧
    ∃ Qplus : Set K.DPath,
      Qplus.Finite ∧
      K.IsOnePointAugmentation
        (touchedDesignatedPaths K (P ∪ L) l) Qplus ∧
      K.initialSet Qplus = insert a
        (K.initialSet (touchedDesignatedPaths K (P ∪ L) l)) ∧
      K.terminalFrontier Qplus = insert b
        (K.terminalFrontier (touchedDesignatedPaths K (P ∪ L) l)) ∧
      ∃ C : Cyclowarp K,
        Qplus = C.pathPart ∧
        C.edges = oneHoleRouteToggledEdges K
          (touchedDesignatedPaths K (P ∪ L) l) l ∧
        C.isolated = isolatedVertices
          (touchedDesignatedPaths K (P ∪ L) l) ∧
      ∃ P' Rplus : Set K.DPath,
        ∃ hAvoid : Disjoint (K.vertexSet P') (K.vertexSet Rplus),
        IsLinkageBetween G A G.target P' ∧
        (G.vertexSet P \ G.vertexSet P').Finite ∧
        Disjoint G.source (G.vertexSet P \ G.vertexSet P') ∧
        Disjoint G.target (G.vertexSet P \ G.vertexSet P') ∧
        G.vertexSet P \ G.vertexSet P' ⊆
          SingularEndpointCarrierSplit.internalCarrier G P ∧
        G.vertexSet P \ G.vertexSet P' ⊆
          AlternatingComponents.component
            (touchedDesignatedPaths K (P ∪ L) l) Qplus a ∧
        K.IsOnePointAugmentation L Rplus ∧
        ∃ x : V,
          x ∈ G.vertexSet P \ G.vertexSet P' ∧
          x ∈ AlternatingComponents.component
            (touchedDesignatedPaths K (P ∪ L) l) Qplus a ∧
          x ∉ G.source ∧
          (x ∈ K.vertexSet Qplus ∨
            x ∈ routeVertexSet l ∨
              ∃ c ∈ C.cycles, x ∈ c.support) ∧
          ∃ p : DirectedPath.FinitePath (G.delete (G.vertexSet P')).graph,
            (G.delete (G.vertexSet P')).IsTargetPathFrom x p ∧
            Disjoint p.support
              ((G.delete (G.vertexSet P')).terminalFrontier
                (G.restrictDeleteFamily
                  (G.vertexSet P') Rplus hAvoid.symm))

/-- The unconditional finite repair trichotomy, sharpened so the escaping
branch retains its unique fresh alternating component and marked route. -/
theorem exists_strictProfile_or_freshComponentEscape_or_exceptionalBlock
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
        HasFreshComponentEscapingUpdate G A P U ∨
        HasExceptionalColourBlock G P U) := by
  obtain ⟨M, hMmax, hMh, hUh, hUfin, a, b, l, ha, hb, hbP,
      hl, hcontact, hwindow, hTfinite, hTPnonempty, Qplus,
      hQfinite, hlocal, hcarrierFinite, hRTQ, hglobal,
      hinit, hterminal, C, hCpath, hCedges, hCisolated⟩ :=
    exists_totalFiniteWindowExchangeExactRelation_of_residual_hindered
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
  obtain ⟨hrepair, a', b', ha', hb', hab', hinit', hterm', hbranch⟩ :=
    markedResidual_wholeComponentMix_dichotomy_with_oppositeCross
      hNorm hA hP hUh hUfin hQfinite hlocal hglobal
  have haa : a' = a := by
    have haMem : a' ∈ insert a (K.initialSet TT) := by
      rw [← hinit]
      rw [hinit']
      exact Set.mem_insert a' _
    rcases haMem with haEq | haOld
    · exact haEq
    · exact False.elim (ha'.2 haOld)
  have hbb : b' = b := by
    have hbMem : b' ∈ insert b (K.terminalFrontier TT) := by
      rw [← hterminal]
      rw [hterm']
      exact Set.mem_insert b' _
    rcases hbMem with hbEq | hbOld
    · exact hbEq
    · exact False.elim (hb'.2 hbOld)
  subst a'
  subst b'
  refine ⟨M, hMmax, hMh, hUh, hUfin, ?_⟩
  rcases hbranch with houtside | hinside
  · obtain ⟨haD, hbD, hZplus⟩ := houtside
    obtain ⟨Pplus, Jplus, Rplus, hPplus, hFreedFinite,
        hFreedFresh, hPplusInitial, hPplusTerminal,
        hPplusJplus, hJplus, hRplusEq, hRplus, hRplusAvoid⟩ :=
      exists_globalFreshComponentExchange_of_marked_outside
        hNorm hA hP hUh hUfin hQfinite hlocal ha' hb' hinit' hterm'
          hRTQ hglobal haD
    rcases strictMaximalProfile_or_escapingFreedCarrierPath
        hNorm hA hP hPplus hUh.1 hRplus hRplusAvoid with
      hprogress | hescape
    · exact Or.inl ⟨Pplus, hPplus, hprogress⟩
    · obtain ⟨x, hxFreed, p, hpTarget, hpAvoid⟩ := hescape
      have hFreedDisjoint :
          Disjoint G.source (G.vertexSet P \ G.vertexSet Pplus) :=
        disjoint_source_freedCarrier_of_targetLinkage_update
          hNorm hA hP hPplus
      have hxNotSource : x ∉ G.source := by
        intro hxSource
        exact Set.disjoint_left.1 hFreedDisjoint hxSource hxFreed
      have hFreedTarget :
          Disjoint G.target (G.vertexSet P \ G.vertexSet Pplus) :=
        disjoint_target_freedCarrier_of_terminalFrontier_eq
          hNorm hP hPplus hPplusTerminal
      have hFreedInternal :
          G.vertexSet P \ G.vertexSet Pplus ⊆
            SingularEndpointCarrierSplit.internalCarrier G P :=
        freedCarrier_subset_internalCarrier_of_exact_boundary
          hNorm hA hP hPplus hPplusTerminal
      have hxFresh := hFreedFresh hxFreed
      have hJclean : K.IsCleanFiniteWarp (P ∪ L) :=
        combinedWarp_isCleanFiniteWarp hNorm hA hP hUh hUfin
      have hTTclean : K.IsCleanFiniteWarp TT :=
        cleanFiniteWarp_mono hJclean
          (touchedDesignatedPaths_subset K (P ∪ L) l)
      have hrouteLocal : IsReducedMarkedRoute K TT a b l := by
        have hl' : IsReducedMarkedRoute K
            ((P ∪ L) ∪ (∅ : Set K.DPath)) a b l := by
          simpa only [Set.union_empty] using hl
        have hlocalized :=
          reducedRoute_localize_designated
            (G := K) (P := P ∪ L) (L := (∅ : Set K.DPath)) hl'
        simpa only [Set.union_empty] using hlocalized
      have hxa : x ≠ a := by
        intro hxa
        apply hxNotSource
        change x ∈ K.source
        rw [hxa]
        exact ha'.1
      have hxCarrier : x ∈ K.vertexSet TT ∪ K.vertexSet Qplus :=
        mem_vertexSet_union_of_mem_component_of_ne hxFresh hxa
      have hxProvenance :
          x ∈ K.vertexSet Qplus ∨
            x ∈ routeVertexSet l ∨
              ∃ c ∈ C.cycles, x ∈ c.support := by
        by_cases hxQ : x ∈ K.vertexSet Qplus
        · exact Or.inl hxQ
        · right
          have hxTT : x ∈ K.vertexSet TT :=
            hxCarrier.resolve_right hxQ
          have hxNotC : x ∉ K.vertexSet C.pathPart := by
            rw [← hCpath]
            exact hxQ
          exact mem_routeVertexSet_or_discardedCycle
            hTTclean hrouteLocal C hCedges hCisolated hxTT hxNotC
      exact Or.inr <| Or.inl ⟨a, b, l, hl, ha', hb', hcontact, Qplus,
        hQfinite, hlocal, hinit, hterminal,
        C, hCpath, hCedges, hCisolated, Pplus, Rplus,
        hRplusAvoid, hPplus, hFreedFinite, hFreedDisjoint,
        hFreedTarget, hFreedInternal,
        hFreedFresh, hRplus, x, hxFreed, hxFresh, hxNotSource,
        hxProvenance, p, hpTarget, hpAvoid⟩
  · right
    right
    obtain ⟨haD, hbD, hZwarp, hZcharacter, hZinitial, hZterminal,
      p, hpQplus, hpNotAP, hpComponent, q, hpq, hqBT⟩ := hinside
    exact ⟨l, Qplus, hQfinite, hlocal, hRTQ, hglobal,
      a, b, ha', hb', hab', hinit', hterm', haD, hbD, hZwarp,
      hZcharacter, hZinitial, hZterminal, p, hpQplus,
      hpNotAP, hpComponent, q, hpq, hqBT⟩

#print axioms exists_strictProfile_or_freshComponentEscape_or_exceptionalBlock

end SingularFiniteFreshComponentTrichotomy
end CardinalInduction
end Erdos599
