/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteFreshComponentRepair

/-!
# Global exchange localized to the fresh alternating component

This is the global form of `SingularFiniteFreshComponentRepair`.  In the
successful endpoint-colour branch it switches only the alternating component
containing the two fresh endpoints, splices the untouched block back, and
extracts the complementary residual augmentation.  In addition to the usual
exact boundary data, it proves that every freed old designated-carrier vertex
lies in that one fresh component.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteFreshComponentGlobalExchange

open DWeb Alternating
open SliceCandidate SliceSpliceSource
open SingularCombinedWaveResidualExtraction
open SingularComponentMixedAugmentation
open SingularFiniteEndpointColorRepair
open SingularFiniteExactBoundaryGlobalExchange
open SingularFiniteExactBoundaryRepair
open SingularFiniteFreshComponentRepair
open SingularFiniteTargetLinkageUpdate
open SingularMarkedResidualFiniteFactor
open SingularMarkedResidualSimultaneousColourRepair
open SingularMarkedResidualTargetColourRepair
open SingularMarkedResidualTouchedPaths
open SingularResidualWaveExchange

universe u

variable {V : Type u}

/-- Successful marked repair using the new family only on its fresh
alternating component.  The final inclusion is the new localization datum:
the entire freed old carrier is contained in that component. -/
theorem exists_globalFreshComponentExchange_of_marked_outside
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U)
    {a b : V} {l : List (OneHoleResidualState V)}
    {Qplus : Set G.DPath} (hQfinite : Qplus.Finite)
    (hlocal :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      K.IsOnePointAugmentation
        (touchedDesignatedPaths K (P ∪ L) l) Qplus)
    (ha :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      a ∈ K.source \ K.initialSet
        (touchedDesignatedPaths K (P ∪ L) l))
    (hb :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      b ∈ K.target \ K.terminalFrontier
        (touchedDesignatedPaths K (P ∪ L) l))
    (hinit :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      K.initialSet Qplus = insert a
        (K.initialSet (touchedDesignatedPaths K (P ∪ L) l)))
    (hterm :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      K.terminalFrontier Qplus = insert b
        (K.terminalFrontier (touchedDesignatedPaths K (P ∪ L) l)))
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
        (untouchedDesignatedPaths K (P ∪ L) l ∪ Qplus))
    (haD :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      let TT := touchedDesignatedPaths K (P ∪ L) l
      let TP := touchedDesignatedPaths K P l
      let AP := K.initialSet TP
      let BT := K.terminalFrontier TP
      let YA := initialRestriction K Qplus AP
      let E := badTerminalColour K YA BT
      a ∉ exceptionalComponentVertices K TT Qplus E) :
    let L := G.liftDeleteFamily (G.vertexSet P) U
    let K := G.retarget
      (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
    let TT := touchedDesignatedPaths K (P ∪ L) l
    ∃ Pplus Jplus Rplus : Set K.DPath,
      IsLinkageBetween G A G.target Pplus ∧
      (G.vertexSet P \ G.vertexSet Pplus).Finite ∧
      G.vertexSet P \ G.vertexSet Pplus ⊆
        AlternatingComponents.component TT Qplus a ∧
      K.initialSet Pplus = K.initialSet P ∧
      K.terminalFrontier Pplus = K.terminalFrontier P ∧
      Pplus ⊆ Jplus ∧
      K.IsOnePointAugmentation (P ∪ L) Jplus ∧
      Rplus = Jplus \ Pplus ∧
      K.IsOnePointAugmentation L Rplus ∧
      Disjoint (K.vertexSet Pplus) (K.vertexSet Rplus) := by
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TT := touchedDesignatedPaths K (P ∪ L) l
  let RT := untouchedDesignatedPaths K (P ∪ L) l
  let TP := touchedDesignatedPaths K P l
  let RP := untouchedDesignatedPaths K P l
  let AP := K.initialSet TP
  let BT := K.terminalFrontier TP
  let Cfresh := AlternatingComponents.component TT Qplus a
  let E := Cfreshᶜ
  let Z := componentMixedFamily K TT Qplus E
  let ZA := initialRestriction K Z AP
  let Jplus := RT ∪ Z
  let Pplus := RP ∪ ZA
  let Rplus := Jplus \ Pplus
  have hJclean : K.IsCleanFiniteWarp (P ∪ L) :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin
  have hTTclean : K.IsCleanFiniteWarp TT :=
    cleanFiniteWarp_mono hJclean
      (touchedDesignatedPaths_subset K (P ∪ L) l)
  have hTTlink : IsLinkageBetween K (K.initialSet TT) K.target TT :=
    isLinkageBetween_of_cleanFiniteWarp hTTclean
  have hQclean : K.IsCleanFiniteWarp Qplus :=
    localReplacement_clean hNorm hA hP hU hUfin hglobal
  have hQlink : IsLinkageBetween K (K.initialSet Qplus) K.target Qplus :=
    isLinkageBetween_of_cleanFiniteWarp hQclean
  have hP_K : IsLinkageBetween K A G.target P := by
    change IsLinkageBetween G A G.target P
    exact hP
  have hTP : IsLinkageBetween K AP G.target TP :=
    isLinkageBetween_subfamily hP_K
      (touchedDesignatedPaths_subset K P l)
  have hTPexact : IsLinkageBetween K AP BT TP :=
    linkageBetween_own_terminalFrontier K hTP
  have hAPTT : AP ⊆ K.initialSet TT :=
    initialSet_touched_designated_subset_total K P L l
  obtain ⟨_a, _ha, _b, _hb, hQwarp, hQcharacter,
      _hinit, _hterm⟩ := hlocal
  have hAPQ : AP ⊆ K.initialSet Qplus := by
    intro x hx
    rw [hinit]
    exact Or.inr (hAPTT hx)
  have hBTK : BT ⊆ K.target := by
    intro x hx
    exact Set.subset_union_left (hTP.terminalFrontier_subset hx)
  have hPL : Disjoint (K.vertexSet P) (K.vertexSet L) := by
    change Disjoint (G.vertexSet P)
      (G.vertexSet (G.liftDeleteFamily (G.vertexSet P) U))
    exact (G.vertexSet_liftDeleteFamily_disjoint hU.1.2.1).symm
  have hOldRestriction : initialRestriction K TT AP = TP :=
    initialRestriction_touched_union_eq_left K hPL l
  have hOld : IsLinkageBetween K AP BT
      (initialRestriction K TT AP) := by
    rw [hOldRestriction]
    exact hTPexact
  have hZA : IsLinkageBetween K AP BT ZA := by
    exact initialRestriction_freshComponentMix_repairs_terminalColour
      K hTTlink hQlink hAPTT hAPQ hBTK hOld haD
  have hTPfinite : TP.Finite := touchedDesignatedPaths_finite hP.isWarp l
  have hTTfinite : TT.Finite :=
    touchedDesignatedPaths_finite hJclean.isWarp l
  have hab : b ∈ Cfresh := by
    exact SingularFiniteAugmentationEndpointComponent.freshEndpoints_mem_same_component
      hTTclean.isWarp hQwarp hTTclean.hasFiniteCharacter hQcharacter
        hTTfinite hQfinite ha.2 hb.2 hinit hterm
  have haNotE : a ∉ exceptionalComponentVertices K TT Qplus E := by
    have heq : exceptionalComponentVertices K TT
        (show Set K.DPath from Qplus) E = Cfreshᶜ := by
      dsimp only [E, Cfresh]
      exact exceptionalComponentVertices_compl_component K TT
        (show Set K.DPath from Qplus) a
    rw [heq]
    simpa only [Set.mem_compl_iff, not_not] using
      (AlternatingComponents.mem_component_self TT Qplus a)
  have hbNotE : b ∉ exceptionalComponentVertices K TT Qplus E := by
    have heq : exceptionalComponentVertices K TT
        (show Set K.DPath from Qplus) E = Cfreshᶜ := by
      dsimp only [E, Cfresh]
      exact exceptionalComponentVertices_compl_component K TT
        (show Set K.DPath from Qplus) a
    rw [heq]
    simpa only [Set.mem_compl_iff, not_not] using hab
  have hZAterminal : K.terminalFrontier ZA = K.terminalFrontier TP :=
    terminalFrontier_eq_of_finite_linkages_same_initial
      hTPfinite hTPexact hZA hZA.terminalFrontier_subset
  have hZAinitial : K.initialSet ZA = K.initialSet TP := by
    rw [hZA.initialSet_eq, hTP.initialSet_eq]
  have hZwarp : K.IsWarp Z :=
    componentMixedFamily_isWarp K E hTTclean.isWarp hQwarp
      hTTclean.hasFiniteCharacter hQcharacter
  have hZcharacter : K.HasFiniteCharacter Z :=
    componentMixedFamily_hasFiniteCharacter K E
      hTTclean.hasFiniteCharacter hQcharacter
  have hRTwarp : K.IsWarp RT := fun p hp q hq hpq ↦
    hJclean.1
      (untouchedDesignatedPaths_subset K (P ∪ L) l hp)
      (untouchedDesignatedPaths_subset K (P ∪ L) l hq) hpq
  have hRTcharacter : K.HasFiniteCharacter RT := fun {_p} hp ↦
    hJclean.2.1
      (untouchedDesignatedPaths_subset K (P ∪ L) l hp)
  have hTTRT : Disjoint (K.vertexSet TT) (K.vertexSet RT) :=
    disjoint_vertexSet_touched_untouched hJclean.isWarp l
  have hglobal' : K.IsOnePointAugmentation (RT ∪ TT) (RT ∪ Qplus) := by
    rw [untouched_union_touched]
    exact hglobal
  have hJplusData := onePointAugmentation_union_componentMixedFamily
    K E hRTwarp hRTcharacter hTTclean.isWarp hTTclean.hasFiniteCharacter
      ha hb hQwarp hQcharacter hinit hterm haNotE hbNotE
      hTTRT.symm hRTQ hglobal'
  have hJplus : K.IsOnePointAugmentation (P ∪ L) Jplus := by
    rw [← untouched_union_touched K (P ∪ L) l]
    exact hJplusData.1
  have hRTZ : Disjoint (K.vertexSet RT) (K.vertexSet Z) :=
    vertexSet_disjoint_componentMixedFamily K E hTTRT.symm hRTQ
  have hRP : IsLinkageBetween K (K.initialSet RP) G.target RP :=
    isLinkageBetween_subfamily hP_K
      (untouchedDesignatedPaths_subset K P l)
  have hZA_target : IsLinkageBetween K AP G.target ZA := by
    refine ⟨hZA.isWarp, hZA.finiteCharacter, hZA.initialSet_eq,
      hZA.terminalFrontier_subset.trans hTP.terminalFrontier_subset, ?_⟩
    intro p hpZA
    have hpLarge : IsPathBetween K (K.initialSet TT) K.target p ∨
        IsPathBetween K (K.initialSet Qplus) K.target p := by
      rcases hpZA.1 with hpTT | hpQ
      · exact Or.inl (hTTlink.endpointPure p hpTT.1)
      · exact Or.inr (hQlink.endpointPure p hpQ.1)
    rcases hpLarge with hpTT | hpQ
    · apply SingularFiniteExactBoundaryGlobalExchange.IsPathBetween.narrow_endpoint_colours
        hpTT hAPTT Set.subset_union_left hpZA.2
      intro q hpq
      subst p
      exact hZA.terminalFrontier_subset ⟨.inl q, hpZA, rfl⟩ |>
        hTP.terminalFrontier_subset
    · apply SingularFiniteExactBoundaryGlobalExchange.IsPathBetween.narrow_endpoint_colours
        hpQ hAPQ Set.subset_union_left hpZA.2
      intro q hpq
      subst p
      exact hZA.terminalFrontier_subset ⟨.inl q, hpZA, rfl⟩ |>
        hTP.terminalFrontier_subset
  have hRPsubRT : RP ⊆ RT := by
    rintro p hp
    refine ⟨Or.inl hp.1, ?_⟩
    intro hpTT
    exact hp.2 ⟨hp.1, hpTT.2⟩
  have hRPZA : Disjoint (K.vertexSet RP) (K.vertexSet ZA) := by
    apply Set.disjoint_left.2
    rintro x ⟨p, hpRP, hxp⟩ ⟨q, hqZA, hxq⟩
    exact Set.disjoint_left.1 hRTZ
      ⟨p, hRPsubRT hpRP, hxp⟩ ⟨q, hqZA.1, hxq⟩
  have hRPTP : RP ∪ TP = P := untouched_union_touched K P l
  have hfullInit : K.initialSet RP ∪ AP = A := by
    rw [← K.initialSet_union, hRPTP]
    exact hP_K.initialSet_eq
  have hPplusK : IsLinkageBetween K A G.target Pplus := by
    rw [← hfullInit]
    exact linkage_union_of_vertexDisjoint hRP hZA_target hRPZA
  have hPplusG : IsLinkageBetween G A G.target Pplus := by
    change IsLinkageBetween K A G.target Pplus
    exact hPplusK
  have hAPfinite : AP.Finite := by
    change (K.initialSet TP).Finite
    have himage : ((fun p : K.DPath ↦ p.initial) '' TP).Finite :=
      hTPfinite.image fun p : K.DPath ↦ p.initial
    simpa only [DWeb.initialSet] using himage
  have hZAfinite : ZA.Finite := by
    apply AharoniBerger.finite_of_isWarp_of_initialSet_finite
      K hZA.isWarp
    rw [hZA.initialSet_eq]
    exact hAPfinite
  have vertexSetFiniteOfFamilyFinite :
      ∀ {W : Set K.DPath}, W.Finite → K.HasFiniteCharacter W →
        (K.vertexSet W).Finite := by
    intro W hW hcharacter
    have hunion : K.vertexSet W = ⋃ p ∈ W, p.support := by
      ext x
      simp [DWeb.vertexSet]
    rw [hunion]
    exact hW.biUnion fun p hp ↦ by
      obtain ⟨q, rfl⟩ := hcharacter hp
      exact q.support_finite
  have hlocalCarrierFinite : (K.vertexSet (TP ∪ ZA)).Finite := by
    rw [K.vertexSet_union]
    exact (vertexSetFiniteOfFamilyFinite hTPfinite hTP.finiteCharacter).union
      (vertexSetFiniteOfFamilyFinite hZAfinite hZA.finiteCharacter)
  have hfreedSubsetLocal : K.vertexSet P \ K.vertexSet Pplus ⊆
      K.vertexSet (TP ∪ ZA) := by
    rintro x ⟨hxP, hxNotPplus⟩
    have hxSplit : x ∈ K.vertexSet (RP ∪ TP) := by
      rw [hRPTP]
      exact hxP
    rw [K.vertexSet_union] at hxSplit ⊢
    rcases hxSplit with hxRP | hxTP
    · exfalso
      apply hxNotPplus
      change x ∈ K.vertexSet (RP ∪ ZA)
      rw [K.vertexSet_union]
      exact Or.inl hxRP
    · exact Or.inl hxTP
  have hfreedFinite : (G.vertexSet P \ G.vertexSet Pplus).Finite := by
    change (K.vertexSet P \ K.vertexSet Pplus).Finite
    exact hlocalCarrierFinite.subset hfreedSubsetLocal
  have hfreedFresh : G.vertexSet P \ G.vertexSet Pplus ⊆ Cfresh := by
    change K.vertexSet P \ K.vertexSet Pplus ⊆ Cfresh
    rintro x ⟨hxP, hxNotPplus⟩
    have hxSplit : x ∈ K.vertexSet (RP ∪ TP) := by
      rw [hRPTP]
      exact hxP
    rw [K.vertexSet_union] at hxSplit
    rcases hxSplit with hxRP | hxTP
    · exact False.elim <| hxNotPplus <| by
        change x ∈ K.vertexSet (RP ∪ ZA)
        rw [K.vertexSet_union]
        exact Or.inl hxRP
    · obtain ⟨p, hpTP, hxp⟩ := hxTP
      have hpTT : p ∈ TT :=
        ⟨Or.inl hpTP.1, hpTP.2⟩
      by_cases hpC : p.initial ∈ Cfresh
      · obtain ⟨q, hpq⟩ := hTP.finiteCharacter hpTP
        subst p
        exact AlternatingComponents.finitePath_support_subset_component_of_touches_left
          hpC hpTT q.start_mem_support hxp
      · exfalso
        apply hxNotPplus
        change x ∈ K.vertexSet (RP ∪ ZA)
        rw [K.vertexSet_union]
        apply Or.inr
        refine ⟨p, ⟨?_, ?_⟩, hxp⟩
        · change p ∈ componentMixedFamily K TT Qplus E
          apply Or.inl
          refine ⟨hpTT, ?_⟩
          have heq : exceptionalComponentVertices K TT
              (show Set K.DPath from Qplus) E = Cfreshᶜ := by
            dsimp only [E, Cfresh]
            exact exceptionalComponentVertices_compl_component K TT
              (show Set K.DPath from Qplus) a
          rw [heq]
          exact hpC
        · exact ⟨p, hpTP, rfl⟩
  have hPplusInitial : K.initialSet Pplus = K.initialSet P := by
    rw [K.initialSet_union, hZAinitial, ← K.initialSet_union, hRPTP]
  have hPplusTerminal : K.terminalFrontier Pplus =
      K.terminalFrontier P := by
    rw [K.terminalFrontier_union, hZAterminal,
      ← K.terminalFrontier_union, hRPTP]
  have hPplusJplus : Pplus ⊆ Jplus := by
    intro p hp
    rcases hp with hpRP | hpZA
    · exact Or.inl (hRPsubRT hpRP)
    · exact Or.inr hpZA.1
  have hLwarp : K.IsWarp L := by
    change G.IsWarp (G.liftDeleteFamily (G.vertexSet P) U)
    exact hU.1.1.liftDeleteFamily
  obtain ⟨hRplus, hRplusAvoid⟩ :=
    complementary_onePointAugmentation_of_global_exact_repair
      K hP.isWarp hLwarp hPL hPplusJplus hJplus
        hPplusInitial hPplusTerminal
  exact ⟨Pplus, Jplus, Rplus, hPplusG, hfreedFinite, hfreedFresh,
    hPplusInitial, hPplusTerminal, hPplusJplus, hJplus, rfl,
    hRplus, hRplusAvoid⟩

#print axioms exists_globalFreshComponentExchange_of_marked_outside

end SingularFiniteFreshComponentGlobalExchange
end CardinalInduction
end Erdos599
