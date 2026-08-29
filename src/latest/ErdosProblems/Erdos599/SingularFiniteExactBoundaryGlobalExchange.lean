/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteExactBoundaryRepair
import ErdosProblems.Erdos599.SingularFiniteTargetLinkageUpdate

/-!
# Globalizing an exact finite boundary exchange

The simultaneous repair is performed on a finite touched block.  This file
records the algebra needed to put the untouched whole block back and then
subtract an exact-boundary designated sublinkage.  The output is deliberately
an augmentation of the complementary residual family, not a residual wave:
changing the designated carrier can expose old internal vertices, so a
separate roof-restoration argument is still necessary.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteExactBoundaryGlobalExchange

open DWeb Alternating
open SliceCandidate SliceSpliceSource
open SingularCombinedWaveResidualExtraction
open SingularComponentMixedAugmentation
open SingularFiniteEndpointColorRepair
open SingularFiniteExactBoundaryRepair
open SingularFiniteTargetLinkageUpdate
open SingularMarkedResidualFiniteFactor
open SingularMarkedResidualSimultaneousColourRepair
open SingularMarkedResidualTargetColourRepair
open SingularMarkedResidualTouchedPaths
open SingularResidualWaveExchange

universe u

variable {V : Type u}

/-- Narrow the endpoint colours of one finite path after separately
certifying its actual start and finish. -/
theorem IsPathBetween.narrow_endpoint_colours
    {G : DWeb V} {A A' B B' : Set V}
    {p : G.DPath} (hp : IsPathBetween G A B p)
    (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hstart : p.initial ∈ A')
    (hfinish : ∀ q : DirectedPath.FinitePath G.graph,
      p = .inl q → q.finish ∈ B') :
    IsPathBetween G A' B' p := by
  obtain ⟨q, rfl, hends, hsource⟩ := hp
  have hqfinish : q.finish ∈ B' := hfinish q rfl
  refine ⟨q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA' | hxB'⟩
      · exact hends ▸ ⟨hxq, Or.inl (hA hxA')⟩
      · have hxOld : x ∈ q.support ∩ (A ∪ B) :=
          ⟨hxq, Or.inr (hB hxB')⟩
        exact hends ▸ hxOld
    · rintro x (hxStart | hxFinish)
      · subst x
        exact ⟨q.start_mem_support, Or.inl hstart⟩
      · have hx : x = q.finish := Set.mem_singleton_iff.mp hxFinish
        subst x
        exact ⟨q.finish_mem_support, Or.inr hqfinish⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA'⟩
      exact hsource ▸ ⟨hxq, hA hxA'⟩
    · intro x hx
      have hxStart : x = q.start := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨q.start_mem_support, hstart⟩

/-- In the augmentation branch, the component mixture has exactly the
right-family boundary, not just the same one-point increment over the old
family. -/
theorem componentMixedFamily_boundary_eq_right_of_endpoints_compl
    (G : DWeb V) {W Y : Set G.DPath} (E : Set V) {a b : V}
    (hW : G.IsWarp W) (hWfinite : G.HasFiniteCharacter W)
    (ha : a ∈ G.source \ G.initialSet W)
    (hb : b ∈ G.target \ G.terminalFrontier W)
    (hY : G.IsWarp Y) (hYfinite : G.HasFiniteCharacter Y)
    (hinit : G.initialSet Y = insert a (G.initialSet W))
    (hterm : G.terminalFrontier Y = insert b (G.terminalFrontier W))
    (haD : a ∉ exceptionalComponentVertices G W Y E)
    (hbD : b ∉ exceptionalComponentVertices G W Y E) :
    G.initialSet (componentMixedFamily G W Y E) = G.initialSet Y ∧
      G.terminalFrontier (componentMixedFamily G W Y E) =
        G.terminalFrontier Y := by
  have hplus :=
    componentMixedFamily_isOnePointAugmentation_of_endpoints_compl
      G E hW hWfinite ha hb hY hYfinite hinit hterm haD hbD
  obtain ⟨_a, _ha, _b, _hb, _hwarp, _hfinite,
      hmixInitial, hmixTerminal⟩ := hplus
  have haMix : a ∈
      G.initialSet (componentMixedFamily G W Y E) := by
    rw [initialSet_componentMixedFamily, hinit]
    exact Or.inr ⟨Or.inl rfl, haD⟩
  have haa : _a = a := by
    rw [hmixInitial] at haMix
    rcases haMix with haa | haOld
    · exact haa.symm
    · exact False.elim (ha.2 haOld)
  have hbMix : b ∈
      G.terminalFrontier (componentMixedFamily G W Y E) := by
    rw [terminalFrontier_componentMixedFamily G E hWfinite hYfinite,
      hterm]
    exact Or.inr ⟨Or.inl rfl, hbD⟩
  have hbb : _b = b := by
    rw [hmixTerminal] at hbMix
    rcases hbMix with hbb | hbOld
    · exact hbb.symm
    · exact False.elim (hb.2 hbOld)
  subst _a
  subst _b
  exact ⟨hmixInitial.trans hinit.symm,
    hmixTerminal.trans hterm.symm⟩

/-- A replacement with the same initial and terminal boundary as the new
side of an augmentation is itself an augmentation of the old side. -/
theorem onePointAugmentation_of_same_new_boundary
    {G : DWeb V} {W Y Z : Set G.DPath}
    (hplus : G.IsOnePointAugmentation W Y)
    (hZwarp : G.IsWarp Z) (hZfinite : G.HasFiniteCharacter Z)
    (hinit : G.initialSet Z = G.initialSet Y)
    (hterm : G.terminalFrontier Z = G.terminalFrontier Y) :
    G.IsOnePointAugmentation W Z := by
  obtain ⟨a, ha, b, hb, _hYwarp, _hYfinite,
      hYinitial, hYterminal⟩ := hplus
  exact ⟨a, ha, b, hb, hZwarp, hZfinite,
    hinit.trans hYinitial, hterm.trans hYterminal⟩

/-- A component mixture uses only old-left or new-right members. -/
theorem componentMixedFamily_subset_union
    (G : DWeb V) (W Y : Set G.DPath) (E : Set V) :
    componentMixedFamily G W Y E ⊆ W ∪ Y := by
  rintro p (hpW | hpY)
  · exact Or.inl hpW.1
  · exact Or.inr hpY.1

/-- Disjoint fixed and changed blocks can be recombined after a component
mixture. -/
theorem vertexSet_disjoint_componentMixedFamily
    (G : DWeb V) {R W Y : Set G.DPath} (E : Set V)
    (hRW : Disjoint (G.vertexSet R) (G.vertexSet W))
    (hRY : Disjoint (G.vertexSet R) (G.vertexSet Y)) :
    Disjoint (G.vertexSet R)
      (G.vertexSet (componentMixedFamily G W Y E)) := by
  apply Set.disjoint_left.2
  rintro x hxR ⟨p, hpMix, hxp⟩
  rcases componentMixedFamily_subset_union G W Y E hpMix with hpW | hpY
  · exact Set.disjoint_left.1 hRW hxR ⟨p, hpW, hxp⟩
  · exact Set.disjoint_left.1 hRY hxR ⟨p, hpY, hxp⟩

/-- Put an untouched block back after a successful local component repair.
The new global family has exactly the boundary of the original global
augmentation and is therefore another augmentation of the same old global
family. -/
theorem onePointAugmentation_union_componentMixedFamily
    (G : DWeb V) {R W Y : Set G.DPath} (E : Set V) {a b : V}
    (hR : G.IsWarp R) (hRfinite : G.HasFiniteCharacter R)
    (hW : G.IsWarp W) (hWfinite : G.HasFiniteCharacter W)
    (ha : a ∈ G.source \ G.initialSet W)
    (hb : b ∈ G.target \ G.terminalFrontier W)
    (hY : G.IsWarp Y) (hYfinite : G.HasFiniteCharacter Y)
    (hinit : G.initialSet Y = insert a (G.initialSet W))
    (hterm : G.terminalFrontier Y = insert b (G.terminalFrontier W))
    (haD : a ∉ exceptionalComponentVertices G W Y E)
    (hbD : b ∉ exceptionalComponentVertices G W Y E)
    (hRW : Disjoint (G.vertexSet R) (G.vertexSet W))
    (hRY : Disjoint (G.vertexSet R) (G.vertexSet Y))
    (hglobal : G.IsOnePointAugmentation (R ∪ W) (R ∪ Y)) :
    G.IsOnePointAugmentation (R ∪ W)
      (R ∪ componentMixedFamily G W Y E) ∧
      G.initialSet (R ∪ componentMixedFamily G W Y E) =
        G.initialSet (R ∪ Y) ∧
      G.terminalFrontier (R ∪ componentMixedFamily G W Y E) =
        G.terminalFrontier (R ∪ Y) := by
  let Z := componentMixedFamily G W Y E
  have hZwarp : G.IsWarp Z :=
    componentMixedFamily_isWarp G E hW hY hWfinite hYfinite
  have hZfinite : G.HasFiniteCharacter Z :=
    componentMixedFamily_hasFiniteCharacter G E hWfinite hYfinite
  have hRZ : Disjoint (G.vertexSet R) (G.vertexSet Z) :=
    vertexSet_disjoint_componentMixedFamily G E hRW hRY
  have hRZwarp : G.IsWarp (R ∪ Z) := by
    apply Set.PairwiseDisjoint.union hR hZwarp
    intro p hpR q hqZ _hpq
    apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 hRZ
      ⟨p, hpR, hxp⟩ ⟨q, hqZ, hxq⟩
  have hRZfinite : G.HasFiniteCharacter (R ∪ Z) := by
    intro p hp
    exact hp.elim hRfinite hZfinite
  obtain ⟨hZinitial, hZterminal⟩ :=
    componentMixedFamily_boundary_eq_right_of_endpoints_compl
      G E hW hWfinite ha hb hY hYfinite hinit hterm haD hbD
  have hglobalInitial : G.initialSet (R ∪ Z) =
      G.initialSet (R ∪ Y) := by
    rw [G.initialSet_union, G.initialSet_union, hZinitial]
  have hglobalTerminal : G.terminalFrontier (R ∪ Z) =
      G.terminalFrontier (R ∪ Y) := by
    rw [G.terminalFrontier_union, G.terminalFrontier_union, hZterminal]
  exact ⟨onePointAugmentation_of_same_new_boundary hglobal
      hRZwarp hRZfinite hglobalInitial hglobalTerminal,
    hglobalInitial, hglobalTerminal⟩

/-- Global exact-boundary repair exposes a genuine complementary residual
augmentation disjoint from the *new* designated carrier.  This is the
strongest conclusion obtainable from endpoint algebra alone; no wave claim
is made. -/
theorem complementary_onePointAugmentation_of_global_exact_repair
    (G : DWeb V) {P L Jplus Pplus : Set G.DPath}
    (hP : G.IsWarp P) (hL : G.IsWarp L)
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (hPplusJplus : Pplus ⊆ Jplus)
    (hplus : G.IsOnePointAugmentation (P ∪ L) Jplus)
    (hPinitial : G.initialSet Pplus = G.initialSet P)
    (hPterminal : G.terminalFrontier Pplus = G.terminalFrontier P) :
    G.IsOnePointAugmentation L (Jplus \ Pplus) ∧
      Disjoint (G.vertexSet Pplus) (G.vertexSet (Jplus \ Pplus)) := by
  have hPsub : P ⊆ P ∪ L := Set.subset_union_left
  have hPLwarp : G.IsWarp (P ∪ L) := by
    apply Set.PairwiseDisjoint.union hP hL
    intro p hpP q hqL _hpq
    exact Set.disjoint_left.2 (fun x hxp hxq ↦
      Set.disjoint_left.1 hPL
        ⟨p, hpP, hxp⟩ ⟨q, hqL, hxq⟩)
  obtain ⟨hresidual, havoid⟩ :=
    complementary_onePointAugmentation_of_exact_boundary
      G hPLwarp
      hPsub hPplusJplus hplus hPinitial hPterminal
  rw [union_diff_left_eq_right_of_vertexSet_disjoint G hPL] at hresidual
  exact ⟨hresidual, havoid⟩

/-- The successful (outside-component) branch of the marked finite repair,
fully reassembled.  It produces a target linkage with the same exact
designated boundary and a complementary residual one-point augmentation
which avoids the new linkage carrier. -/
theorem exists_globalExactBoundaryExchange_of_marked_outside
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U)
    {a b : V} {l : List (OneHoleResidualState V)}
    {Qplus : Set G.DPath}
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
    (hQwarp :
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      K.IsWarp Qplus)
    (hQcharacter :
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      K.HasFiniteCharacter Qplus)
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
      a ∉ exceptionalComponentVertices K TT Qplus E)
    (hbD :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      let TT := touchedDesignatedPaths K (P ∪ L) l
      let TP := touchedDesignatedPaths K P l
      let AP := K.initialSet TP
      let BT := K.terminalFrontier TP
      let YA := initialRestriction K Qplus AP
      let E := badTerminalColour K YA BT
      b ∉ exceptionalComponentVertices K TT Qplus E) :
    let L := G.liftDeleteFamily (G.vertexSet P) U
    let K := G.retarget
      (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
    ∃ Pplus Jplus Rplus : Set K.DPath,
      IsLinkageBetween G A G.target Pplus ∧
      (G.vertexSet P \ G.vertexSet Pplus).Finite ∧
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
  let YA := initialRestriction K Qplus AP
  let E := badTerminalColour K YA BT
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
  have hAPQ : AP ⊆ K.initialSet Qplus := by
    intro x hx
    rw [hinit]
    exact Or.inr (hAPTT hx)
  have hBTK : BT ⊆ K.target := by
    intro x hx
    exact Set.subset_union_left (hTP.terminalFrontier_subset hx)
  have hOldRestriction : initialRestriction K TT AP = TP := by
    have hPL : Disjoint (K.vertexSet P) (K.vertexSet L) := by
      change Disjoint (G.vertexSet P)
        (G.vertexSet (G.liftDeleteFamily (G.vertexSet P) U))
      exact (G.vertexSet_liftDeleteFamily_disjoint hU.1.2.1).symm
    exact initialRestriction_touched_union_eq_left K hPL l
  have hOld : IsLinkageBetween K AP BT
      (initialRestriction K TT AP) := by
    rw [hOldRestriction]
    exact hTPexact
  have hZA : IsLinkageBetween K AP BT ZA := by
    exact initialRestriction_wholeComponentMix_repairs_terminalColour
      K hTTlink hQlink hAPTT hAPQ hBTK hOld
  have hTPfinite : TP.Finite := touchedDesignatedPaths_finite hP.isWarp l
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
  have hZboundary : K.initialSet Z = K.initialSet Qplus ∧
      K.terminalFrontier Z = K.terminalFrontier Qplus :=
    componentMixedFamily_boundary_eq_right_of_endpoints_compl
      K E hTTclean.isWarp hTTclean.hasFiniteCharacter ha hb
        hQwarp hQcharacter hinit hterm haD hbD
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
      ha hb hQwarp hQcharacter hinit hterm haD hbD hTTRT.symm hRTQ hglobal'
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
    · apply IsPathBetween.narrow_endpoint_colours
        hpTT hAPTT Set.subset_union_left hpZA.2
      intro q hpq
      subst p
      exact hZA.terminalFrontier_subset ⟨.inl q, hpZA, rfl⟩ |>
        hTP.terminalFrontier_subset
    · apply IsPathBetween.narrow_endpoint_colours
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
  have hRPTP : RP ∪ TP = P := by
    exact untouched_union_touched K P l
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
  have hfreedSubset : K.vertexSet P \ K.vertexSet Pplus ⊆
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
    exact hlocalCarrierFinite.subset hfreedSubset
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
  have hPL : Disjoint (K.vertexSet P) (K.vertexSet L) := by
    change Disjoint (G.vertexSet P)
      (G.vertexSet (G.liftDeleteFamily (G.vertexSet P) U))
    exact (G.vertexSet_liftDeleteFamily_disjoint hU.1.2.1).symm
  obtain ⟨hRplus, hRplusAvoid⟩ :=
    complementary_onePointAugmentation_of_global_exact_repair
      K hP.isWarp hLwarp hPL hPplusJplus hJplus
        hPplusInitial hPplusTerminal
  exact ⟨Pplus, Jplus, Rplus, hPplusG, hfreedFinite, hPplusInitial,
    hPplusTerminal, hPplusJplus, hJplus, rfl,
    hRplus, hRplusAvoid⟩

#print axioms componentMixedFamily_boundary_eq_right_of_endpoints_compl
#print axioms onePointAugmentation_of_same_new_boundary
#print axioms componentMixedFamily_subset_union
#print axioms vertexSet_disjoint_componentMixedFamily
#print axioms onePointAugmentation_union_componentMixedFamily
#print axioms complementary_onePointAugmentation_of_global_exact_repair
#print axioms exists_globalExactBoundaryExchange_of_marked_outside

end SingularFiniteExactBoundaryGlobalExchange
end CardinalInduction
end Erdos599
