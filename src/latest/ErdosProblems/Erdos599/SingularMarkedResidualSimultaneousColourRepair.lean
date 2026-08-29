/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularComponentMixedAugmentation
import ErdosProblems.Erdos599.SingularFiniteAugmentationEndpointComponent
import ErdosProblems.Erdos599.SingularMarkedResidualTargetColourRepair

/-!
# Simultaneous finite endpoint-colour repair

The designated-only component repair is not sufficient for a residual
exchange: retaining an old designated path can intersect a new residual
path.  Here the component cut is instead made in the *whole* old/new finite
block.  Restricting the resulting whole warp to the designated initials
still repairs every designated terminal, while its complementary members
remain carrier-disjoint automatically.

For a finite one-point augmentation the fresh initial and fresh terminal
belong to the same old/new alternating component.  Consequently the whole
component cut has an exact dichotomy: either it retains both fresh ends and
is still a one-point augmentation, or it discards both and restores the old
boundary.  There are no mismatched endpoint cases.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualSimultaneousColourRepair

open DWeb Alternating
open SliceCandidate SliceSpliceSource
open SingularFiniteEndpointColorRepair
open SingularComponentMixedAugmentation
open SingularFiniteAugmentationEndpointComponent
open SingularResidualWaveExchange
open SingularMarkedResidualTouchedPaths
open SingularMarkedResidualFiniteFactor
open SingularMarkedResidualTargetColourRepair

universe u

variable {V : Type u}

/-- Restricting the touched part of a carrier-disjoint two-colour union to
the initials of the touched left colour recovers that left colour exactly. -/
theorem initialRestriction_touched_union_eq_left
    (G : DWeb V) {P L : Set G.DPath}
    (hPL : Disjoint (G.vertexSet P) (G.vertexSet L))
    (l : List (OneHoleResidualState V)) :
    initialRestriction G (touchedDesignatedPaths G (P ∪ L) l)
        (G.initialSet (touchedDesignatedPaths G P l)) =
      touchedDesignatedPaths G P l := by
  apply Set.Subset.antisymm
  · intro p hp
    rcases hp.1.1 with hpP | hpL
    · exact ⟨hpP, hp.1.2⟩
    · obtain ⟨q, hqTP, hqp⟩ := hp.2
      have hqpSupport : p.initial ∈ q.support :=
        hqp.symm ▸ q.initial_mem_support
      exact False.elim (Set.disjoint_left.1 hPL
        ⟨q, hqTP.1, hqpSupport⟩
        ⟨p, hpL, p.initial_mem_support⟩)
  · intro p hp
    exact ⟨⟨Or.inl hp.1, hp.2⟩, ⟨p, hp, rfl⟩⟩

/-- If `a` and `b` are in the same alternating component, every union of
whole alternating components contains `a` exactly when it contains `b`. -/
theorem mem_exceptionalComponentVertices_iff_of_same_component
    {G : DWeb V} {W Y : Set G.DPath} {E : Set V} {a b : V}
    (hab : b ∈ AlternatingComponents.component W Y a) :
    a ∈ exceptionalComponentVertices G W Y E ↔
      b ∈ exceptionalComponentVertices G W Y E := by
  constructor
  · intro ha
    simp only [exceptionalComponentVertices, Set.mem_iUnion] at ha ⊢
    obtain ⟨root, hrootE, haroot⟩ := ha
    exact ⟨root, hrootE,
      AlternatingComponents.component_trans haroot hab⟩
  · intro hb
    simp only [exceptionalComponentVertices, Set.mem_iUnion] at hb ⊢
    obtain ⟨root, hrootE, hbroot⟩ := hb
    exact ⟨root, hrootE,
      AlternatingComponents.component_trans hbroot
        (AlternatingComponents.component_symm hab)⟩

/-- Narrow both endpoint sets of one finite linkage member once its actual
initial and terminal have the narrower colours. -/
private theorem IsPathBetween.narrow_endpoint_colours
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
      · have hxOld : x ∈ q.support ∩ (A ∪ B) :=
          ⟨hxq, Or.inl (hA hxA')⟩
        exact hends ▸ hxOld
      · have hxOld : x ∈ q.support ∩ (A ∪ B) :=
          ⟨hxq, Or.inr (hB hxB')⟩
        rcases hends ▸ hxOld with hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
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

/-- Every linkage can be regarded as a linkage to its *exact* terminal
frontier.  This elementary recolouring is useful below because equality of
the finite designated frontier, rather than mere containment in the ambient
target, is what preserves the complementary residual colour. -/
theorem linkageBetween_own_terminalFrontier
    (G : DWeb V) {A B : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A B P) :
    IsLinkageBetween G A (G.terminalFrontier P) P := by
  refine ⟨hP.isWarp, hP.finiteCharacter, hP.initialSet_eq,
    Set.Subset.rfl, ?_⟩
  intro p hp
  have hpInitial : p.initial ∈ A := by
    have hpInitial' : p.initial ∈ G.initialSet P := ⟨p, hp, rfl⟩
    rwa [hP.initialSet_eq] at hpInitial'
  apply IsPathBetween.narrow_endpoint_colours
    (hP.endpointPure p hp) Set.Subset.rfl hP.terminalFrontier_subset
      hpInitial
  intro q hpq
  subst p
  exact ⟨.inl q, hp, rfl⟩

/-- Cutting *whole* old/new alternating components at the bad designated
terminals repairs the designated colour.  Unlike a repair formed only from
the designated subfamilies, this one leaves a literal complementary
subfamily of the same whole mixed warp. -/
theorem initialRestriction_wholeComponentMix_repairs_terminalColour
    (G : DWeb V) {W Y : Set G.DPath} {A B C : Set V}
    (hW : IsLinkageBetween G (G.initialSet W) C W)
    (hY : IsLinkageBetween G (G.initialSet Y) C Y)
    (hAW : A ⊆ G.initialSet W) (hAY : A ⊆ G.initialSet Y)
    (hB : B ⊆ C)
    (hOld : IsLinkageBetween G A B (initialRestriction G W A)) :
    let Y_A := initialRestriction G Y A
    let E := badTerminalColour G Y_A B
    let Z := componentMixedFamily G W Y E
    IsLinkageBetween G A B (initialRestriction G Z A) := by
  let Y_A := initialRestriction G Y A
  let E := badTerminalColour G Y_A B
  let D := exceptionalComponentVertices G W Y E
  let Z := componentMixedFamily G W Y E
  let Z_A := initialRestriction G Z A
  have hZwarp : G.IsWarp Z :=
    componentMixedFamily_isWarp G E hW.isWarp hY.isWarp
      hW.finiteCharacter hY.finiteCharacter
  have hZfinite : G.HasFiniteCharacter Z :=
    componentMixedFamily_hasFiniteCharacter G E
      hW.finiteCharacter hY.finiteCharacter
  have hZAwarp : G.IsWarp Z_A := fun p hp q hq hpq ↦
    hZwarp hp.1 hq.1 hpq
  have hZAfinite : G.HasFiniteCharacter Z_A := fun {_p} hp ↦
    hZfinite hp.1
  have hZAinitial : G.initialSet Z_A = A := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact hp.2
    · intro x hxA
      by_cases hxD : x ∈ D
      · obtain ⟨p, hpW, hpx⟩ := hAW hxA
        refine ⟨p, ⟨Or.inl ⟨hpW, ?_⟩, ?_⟩, hpx⟩
        · exact hpx ▸ hxD
        · exact hpx ▸ hxA
      · obtain ⟨p, hpY, hpx⟩ := hAY hxA
        refine ⟨p, ⟨Or.inr ⟨hpY, ?_⟩, ?_⟩, hpx⟩
        · exact fun hpD ↦ hxD (hpx.symm ▸ hpD)
        · exact hpx ▸ hxA
  have hZAterminal : G.terminalFrontier Z_A ⊆ B := by
    rintro x ⟨p, hpZA, hpx⟩
    rcases hpZA.1 with hpW | hpY
    · exact hOld.terminalFrontier_subset
        ⟨p, ⟨hpW.1, hpZA.2⟩, hpx⟩
    · by_contra hxB
      have hxE : x ∈ E :=
        ⟨⟨p, ⟨hpY.1, hpZA.2⟩, hpx⟩, hxB⟩
      have hxD : x ∈ D :=
        mem_exceptionalComponentVertices_of_mem hxE
      have hpD : p.support ⊆ D :=
        path_support_subset_exceptionalComponents_right
          hY.finiteCharacter hpY.1 (G.terminal_mem_support hpx) hxD
      exact hpY.2 (hpD p.initial_mem_support)
  refine ⟨hZAwarp, hZAfinite, hZAinitial, hZAterminal, ?_⟩
  intro p hpZA
  have hpLarge : IsPathBetween G (G.initialSet W) C p ∨
      IsPathBetween G (G.initialSet Y) C p := by
    rcases hpZA.1 with hpW | hpY
    · exact Or.inl (hW.endpointPure p hpW.1)
    · exact Or.inr (hY.endpointPure p hpY.1)
  rcases hpLarge with hpW | hpY
  · apply IsPathBetween.narrow_endpoint_colours hpW hAW hB hpZA.2
    intro q hpq
    subst p
    apply hZAterminal
    exact ⟨.inl q, hpZA, rfl⟩
  · apply IsPathBetween.narrow_endpoint_colours hpY hAY hB hpZA.2
    intro q hpq
    subst p
    apply hZAterminal
    exact ⟨.inl q, hpZA, rfl⟩

/-- Exact simultaneous component-repair dichotomy for a finite one-point
augmentation.  The repaired designated subfamily is always target-coloured.
The whole mixed family either keeps the one-point augmentation, with both
fresh endpoints outside the reverted components, or cancels it completely,
with both fresh endpoints inside. -/
theorem exists_wholeComponentMix_colourRepair_dichotomy
    (G : DWeb V) {W Y : Set G.DPath} {A B C : Set V}
    (hW : IsLinkageBetween G (G.initialSet W) C W)
    (hY : IsLinkageBetween G (G.initialSet Y) C Y)
    (hWfinite : W.Finite) (hYfinite : Y.Finite)
    (hplus : G.IsOnePointAugmentation W Y)
    (hAW : A ⊆ G.initialSet W) (hAY : A ⊆ G.initialSet Y)
    (hB : B ⊆ C)
    (hOld : IsLinkageBetween G A B (initialRestriction G W A)) :
    let Y_A := initialRestriction G Y A
    let E := badTerminalColour G Y_A B
    let D := exceptionalComponentVertices G W Y E
    let Z := componentMixedFamily G W Y E
    IsLinkageBetween G A B (initialRestriction G Z A) ∧
      ∃ a b : V,
        a ∈ G.source \ G.initialSet W ∧
        b ∈ G.target \ G.terminalFrontier W ∧
        b ∈ AlternatingComponents.component W Y a ∧
        ((a ∉ D ∧ b ∉ D ∧ G.IsOnePointAugmentation W Z) ∨
          (a ∈ D ∧ b ∈ D ∧
            G.IsWarp Z ∧ G.HasFiniteCharacter Z ∧
            G.initialSet Z = G.initialSet W ∧
            G.terminalFrontier Z = G.terminalFrontier W)) := by
  let Y_A := initialRestriction G Y A
  let E := badTerminalColour G Y_A B
  let D := exceptionalComponentVertices G W Y E
  let Z := componentMixedFamily G W Y E
  have hrepair : IsLinkageBetween G A B
      (initialRestriction G Z A) :=
    initialRestriction_wholeComponentMix_repairs_terminalColour
      G hW hY hAW hAY hB hOld
  obtain ⟨a, ha, b, hb, hYwarp, hYcharacter, hinit, hterm⟩ := hplus
  have hab : b ∈ AlternatingComponents.component W Y a :=
    SingularFiniteAugmentationEndpointComponent.freshEndpoints_mem_same_component
      hW.isWarp hYwarp hW.finiteCharacter hYcharacter
        hWfinite hYfinite ha.2 hb.2 hinit hterm
  have habD : a ∈ D ↔ b ∈ D :=
    mem_exceptionalComponentVertices_iff_of_same_component hab
  refine ⟨hrepair, a, b, ha, hb, hab, ?_⟩
  by_cases haD : a ∈ D
  · have hbD : b ∈ D := habD.mp haD
    right
    refine ⟨haD, hbD, ?_⟩
    exact componentMixedFamily_oldBoundary_of_endpoints_mem
      G E hW.isWarp hW.finiteCharacter ha hb hY.isWarp
        hY.finiteCharacter hinit hterm haD hbD
  · have hbD : b ∉ D := fun hbD ↦ haD (habD.mpr hbD)
    left
    refine ⟨haD, hbD, ?_⟩
    exact componentMixedFamily_isOnePointAugmentation_of_endpoints_compl
      G E hW.isWarp hW.finiteCharacter ha hb hY.isWarp
        hY.finiteCharacter hinit hterm haD hbD

/-! ## Instantiation at the marked residual finite factor -/

/-- The total finite marked exchange admits the whole-family simultaneous
colour repair.  In particular, this does not merely return a target-coloured
subfamily: it retains the exact whole mixed block and records whether its
fresh residual source/target component survives or is reverted. -/
theorem markedResidual_wholeComponentMix_colourRepair_dichotomy
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
    let AP := K.initialSet (touchedDesignatedPaths K P l)
    let Y_A := initialRestriction K Qplus AP
    let E := badTerminalColour K Y_A G.target
    let D := exceptionalComponentVertices K TT Qplus E
    let Z := componentMixedFamily K TT Qplus E
    IsLinkageBetween K AP G.target (initialRestriction K Z AP) ∧
      ∃ a b : V,
        a ∈ K.source \ K.initialSet TT ∧
        b ∈ K.target \ K.terminalFrontier TT ∧
        b ∈ AlternatingComponents.component TT Qplus a ∧
        ((a ∉ D ∧ b ∉ D ∧ K.IsOnePointAugmentation TT Z) ∨
          (a ∈ D ∧ b ∈ D ∧
            K.IsWarp Z ∧ K.HasFiniteCharacter Z ∧
            K.initialSet Z = K.initialSet TT ∧
            K.terminalFrontier Z = K.terminalFrontier TT)) := by
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TT := touchedDesignatedPaths K (P ∪ L) l
  let TP := touchedDesignatedPaths K P l
  let AP := K.initialSet TP
  have hJclean : K.IsCleanFiniteWarp (P ∪ L) :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin
  have hTTclean : K.IsCleanFiniteWarp TT :=
    cleanFiniteWarp_mono hJclean
      (touchedDesignatedPaths_subset K (P ∪ L) l)
  have hQclean : K.IsCleanFiniteWarp Qplus :=
    localReplacement_clean hNorm hA hP hU hUfin hglobal
  have hTTlink : IsLinkageBetween K (K.initialSet TT) K.target TT :=
    isLinkageBetween_of_cleanFiniteWarp hTTclean
  have hQlink : IsLinkageBetween K (K.initialSet Qplus) K.target Qplus :=
    isLinkageBetween_of_cleanFiniteWarp hQclean
  have hP_K : IsLinkageBetween K A G.target P := by
    change IsLinkageBetween G A G.target P
    exact hP
  have hTP : IsLinkageBetween K AP G.target TP :=
    isLinkageBetween_subfamily hP_K
      (touchedDesignatedPaths_subset K P l)
  have hPL : Disjoint (K.vertexSet P) (K.vertexSet L) := by
    change Disjoint (G.vertexSet P)
      (G.vertexSet (G.liftDeleteFamily (G.vertexSet P) U))
    exact (G.vertexSet_liftDeleteFamily_disjoint hU.1.2.1).symm
  have hOldRestriction : initialRestriction K TT AP = TP :=
    initialRestriction_touched_union_eq_left K hPL l
  have hOld : IsLinkageBetween K AP G.target
      (initialRestriction K TT AP) := by
    rw [hOldRestriction]
    exact hTP
  have hAPTT : AP ⊆ K.initialSet TT :=
    initialSet_touched_designated_subset_total K P L l
  have hlocalCopy := hlocal
  obtain ⟨a, ha, b, hb, _hQwarp, _hQcharacter, hinit, _hterm⟩ :=
    hlocalCopy
  have hAPQ : AP ⊆ K.initialSet Qplus := by
    intro x hx
    rw [hinit]
    exact Or.inr (hAPTT hx)
  have hTTfinite : TT.Finite :=
    touchedDesignatedPaths_finite hJclean.isWarp l
  exact exists_wholeComponentMix_colourRepair_dichotomy
    K hTTlink hQlink hTTfinite hQfinite hlocal
      hAPTT hAPQ Set.subset_union_left hOld

/-- Exact-frontier form of the simultaneous colour repair.  Here the
designated colour is not the whole ambient target set: it is the precise
terminal frontier of the old touched designated block.  Consequently a
successful outside-component branch preserves that finite frontier exactly,
which is the datum needed by the complementary residual block. -/
theorem markedResidual_wholeComponentMix_exactFrontier_dichotomy
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
    let Y_A := initialRestriction K Qplus AP
    let E := badTerminalColour K Y_A BT
    let D := exceptionalComponentVertices K TT Qplus E
    let Z := componentMixedFamily K TT Qplus E
    IsLinkageBetween K AP BT (initialRestriction K Z AP) ∧
      ∃ a b : V,
        a ∈ K.source \ K.initialSet TT ∧
        b ∈ K.target \ K.terminalFrontier TT ∧
        b ∈ AlternatingComponents.component TT Qplus a ∧
        ((a ∉ D ∧ b ∉ D ∧ K.IsOnePointAugmentation TT Z) ∨
          (a ∈ D ∧ b ∈ D ∧
            K.IsWarp Z ∧ K.HasFiniteCharacter Z ∧
            K.initialSet Z = K.initialSet TT ∧
            K.terminalFrontier Z = K.terminalFrontier TT)) := by
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TT := touchedDesignatedPaths K (P ∪ L) l
  let TP := touchedDesignatedPaths K P l
  let AP := K.initialSet TP
  let BT := K.terminalFrontier TP
  have hJclean : K.IsCleanFiniteWarp (P ∪ L) :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin
  have hTTclean : K.IsCleanFiniteWarp TT :=
    cleanFiniteWarp_mono hJclean
      (touchedDesignatedPaths_subset K (P ∪ L) l)
  have hQclean : K.IsCleanFiniteWarp Qplus :=
    localReplacement_clean hNorm hA hP hU hUfin hglobal
  have hTTlink : IsLinkageBetween K (K.initialSet TT) K.target TT :=
    isLinkageBetween_of_cleanFiniteWarp hTTclean
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
  have hBT : BT ⊆ K.target := by
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
  have hAPTT : AP ⊆ K.initialSet TT :=
    initialSet_touched_designated_subset_total K P L l
  have hlocalCopy := hlocal
  obtain ⟨a, ha, b, hb, _hQwarp, _hQcharacter, hinit, _hterm⟩ :=
    hlocalCopy
  have hAPQ : AP ⊆ K.initialSet Qplus := by
    intro x hx
    rw [hinit]
    exact Or.inr (hAPTT hx)
  have hTTfinite : TT.Finite :=
    touchedDesignatedPaths_finite hJclean.isWarp l
  exact exists_wholeComponentMix_colourRepair_dichotomy
    K hTTlink hQlink hTTfinite hQfinite hlocal
      hAPTT hAPQ hBT hOld

#print axioms mem_exceptionalComponentVertices_iff_of_same_component
#print axioms initialRestriction_touched_union_eq_left
#print axioms initialRestriction_wholeComponentMix_repairs_terminalColour
#print axioms exists_wholeComponentMix_colourRepair_dichotomy
#print axioms markedResidual_wholeComponentMix_colourRepair_dichotomy
#print axioms linkageBetween_own_terminalFrontier
#print axioms markedResidual_wholeComponentMix_exactFrontier_dichotomy

end SingularMarkedResidualSimultaneousColourRepair
end CardinalInduction
end Erdos599
