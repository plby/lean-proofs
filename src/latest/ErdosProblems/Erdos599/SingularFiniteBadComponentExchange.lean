/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualSimultaneousColourRepair
import ErdosProblems.Erdos599.SingularFiniteEndpointColourImbalance

/-!
# The bad fresh component contains an opposite-coloured path

In the inside branch of the simultaneous whole-component repair, the fresh
component meets a terminal of a newly designated path having the wrong
terminal colour.  Finite endpoint balance forces the opposite crossing in
the same new family: a path whose initial is not designated ends at the old
designated frontier.  This is the concrete residual-to-target member needed
by the subsequent selective switch.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteBadComponentExchange

open DWeb
open SliceCandidate SliceSpliceSource
open SingularFiniteEndpointColorRepair
open SingularComponentMixedAugmentation
open SingularFiniteAugmentationEndpointComponent
open SingularFiniteEndpointColourImbalance
open SingularMarkedResidualSimultaneousColourRepair
open SingularResidualWaveExchange
open SingularMarkedResidualTouchedPaths
open SingularMarkedResidualFiniteFactor
open SingularMarkedResidualEndpointSupport
open SingularMarkedResidualTargetColourRepair

universe u

variable {V : Type u}

/-- Exact endpoint-colour balance persists after restricting the old whole
family to one alternating component.  The designated subfamily is assumed
to be exactly the initial restriction and to have exact terminal frontier.
-/
theorem ncard_endpointColours_eq_on_component
    (G : DWeb V) {W Y : Set G.DPath} {A B : Set V} (root : V)
    (hWfinite : G.HasFiniteCharacter W)
    (hAW : A ⊆ G.initialSet W)
    (hOld : IsLinkageBetween G A B (initialRestriction G W A))
    (hOldTerminal :
      G.terminalFrontier (initialRestriction G W A) = B) :
    let C := AlternatingComponents.component W Y root
    let Wc := initialPart G W C
    (G.initialSet Wc ∩ A).ncard =
      (G.terminalFrontier Wc ∩ B).ncard := by
  let C := AlternatingComponents.component W Y root
  let T := initialRestriction G W A
  let Tc := initialPart G T C
  let Wc := initialPart G W C
  have hTsub : T ⊆ W := fun _ hp ↦ hp.1
  have hTcwarp : G.IsWarp Tc := fun p hp q hq hpq ↦
    hOld.isWarp hp.1 hq.1 hpq
  have hTccharacter : G.HasFiniteCharacter Tc := fun {_p} hp ↦
    hOld.finiteCharacter hp.1
  have hTcInitial : G.initialSet Tc = A ∩ C := by
    rw [initialSet_initialPart, hOld.initialSet_eq]
  have hTcTerminal : G.terminalFrontier Tc = B ∩ C := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, hpTc, hpx⟩
      refine ⟨hOld.terminalFrontier_subset ⟨p, hpTc.1, hpx⟩, ?_⟩
      obtain ⟨q, rfl⟩ := hOld.finiteCharacter hpTc.1
      have hsupport : q.support ⊆ C :=
        AlternatingComponents.finitePath_support_subset_component_of_touches_left
          hpTc.2 (hTsub hpTc.1) q.start_mem_support
      exact hsupport (G.terminal_mem_support hpx)
    · rintro x ⟨hxB, hxC⟩
      rw [← hOldTerminal] at hxB
      obtain ⟨p, hpT, hpx⟩ := hxB
      obtain ⟨q, rfl⟩ := hOld.finiteCharacter hpT
      have hsupport : q.support ⊆ C :=
        AlternatingComponents.finitePath_support_subset_component_of_touches_left
          hxC (hTsub hpT) (G.terminal_mem_support hpx)
      exact ⟨.inl q, ⟨hpT, hsupport q.start_mem_support⟩, hpx⟩
  have hWcInitial : G.initialSet Wc ∩ A = A ∩ C := by
    rw [initialSet_initialPart]
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  have hBsub : B ⊆ G.terminalFrontier W := by
    intro x hxB
    rw [← hOldTerminal] at hxB
    obtain ⟨p, hpT, hpx⟩ := hxB
    exact ⟨p, hTsub hpT, hpx⟩
  have hWcTerminal : G.terminalFrontier Wc ∩ B = B ∩ C := by
    have hfront : G.terminalFrontier Wc =
        G.terminalFrontier W ∩ C := by
      apply Set.Subset.antisymm
      · rintro x ⟨p, hpWc, hpx⟩
        refine ⟨⟨p, hpWc.1, hpx⟩, ?_⟩
        obtain ⟨q, rfl⟩ := hWfinite hpWc.1
        exact AlternatingComponents.finitePath_support_subset_component_of_touches_left
          hpWc.2 hpWc.1 q.start_mem_support (G.terminal_mem_support hpx)
      · rintro x ⟨⟨p, hpW, hpx⟩, hxC⟩
        obtain ⟨q, rfl⟩ := hWfinite hpW
        have hsupport :=
          AlternatingComponents.finitePath_support_subset_component_of_touches_left
            hxC hpW (G.terminal_mem_support hpx)
        exact ⟨.inl q, ⟨hpW, hsupport q.start_mem_support⟩, hpx⟩
    rw [hfront]
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  change (G.initialSet Wc ∩ A).ncard =
    (G.terminalFrontier Wc ∩ B).ncard
  rw [hWcInitial, hWcTerminal, ← hTcInitial, ← hTcTerminal]
  exact ncard_initialSet_eq_terminalFrontier hTcwarp hTccharacter

/-- Strengthen the inside branch of the finite whole-component repair by
exhibiting a new path crossing in the opposite endpoint-colour direction.
The old designated frontier is assumed exact; this is the form supplied by
the touched designated subfamily in the marked residual exchange. -/
theorem exists_wholeComponentMix_colourRepair_dichotomy_with_oppositeCross
    (G : DWeb V) {W Y : Set G.DPath} {A B C : Set V}
    (hW : IsLinkageBetween G (G.initialSet W) C W)
    (hY : IsLinkageBetween G (G.initialSet Y) C Y)
    (hWfinite : W.Finite) (hYfinite : Y.Finite)
    (hplus : G.IsOnePointAugmentation W Y)
    (hAW : A ⊆ G.initialSet W) (hAY : A ⊆ G.initialSet Y)
    (hB : B ⊆ C)
    (hOld : IsLinkageBetween G A B (initialRestriction G W A))
    (hOldTerminal :
      G.terminalFrontier (initialRestriction G W A) = B) :
    let Y_A := initialRestriction G Y A
    let E := badTerminalColour G Y_A B
    let D := exceptionalComponentVertices G W Y E
    let Z := componentMixedFamily G W Y E
    IsLinkageBetween G A B (initialRestriction G Z A) ∧
      ∃ a b : V,
        a ∈ G.source \ G.initialSet W ∧
        b ∈ G.target \ G.terminalFrontier W ∧
        b ∈ AlternatingComponents.component W Y a ∧
        G.initialSet Y = insert a (G.initialSet W) ∧
        G.terminalFrontier Y = insert b (G.terminalFrontier W) ∧
        ((a ∉ D ∧ b ∉ D ∧ G.IsOnePointAugmentation W Z) ∨
          (a ∈ D ∧ b ∈ D ∧
            G.IsWarp Z ∧ G.HasFiniteCharacter Z ∧
            G.initialSet Z = G.initialSet W ∧
            G.terminalFrontier Z = G.terminalFrontier W ∧
            ∃ p ∈ Y, p.initial ∉ A ∧
              p.initial ∈ AlternatingComponents.component W Y a ∧
              ∃ q : DirectedPath.FinitePath G.graph,
                p = .inl q ∧ q.finish ∈ B)) := by
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
    freshEndpoints_mem_same_component hW.isWarp hYwarp
      hW.finiteCharacter hYcharacter hWfinite hYfinite
      ha.2 hb.2 hinit hterm
  have habD : a ∈ D ↔ b ∈ D :=
    mem_exceptionalComponentVertices_iff_of_same_component hab
  refine ⟨hrepair, a, b, ha, hb, hab, hinit, hterm, ?_⟩
  by_cases haD : a ∈ D
  · have hbD : b ∈ D := habD.mp haD
    right
    refine ⟨haD, hbD, ?_⟩
    obtain ⟨hZwarp, hZcharacter, hZinit, hZterm⟩ :=
      componentMixedFamily_oldBoundary_of_endpoints_mem G E
        hW.isWarp hW.finiteCharacter ha hb hYwarp hYcharacter
        hinit hterm haD hbD
    refine ⟨hZwarp, hZcharacter, hZinit, hZterm, ?_⟩
    have haA : a ∉ A := fun haA ↦ ha.2 (hAW haA)
    have hBterminalW : B ⊆ G.terminalFrontier W := by
      intro x hxB
      rw [← hOldTerminal] at hxB
      obtain ⟨p, hp, hpx⟩ := hxB
      exact ⟨p, hp.1, hpx⟩
    have hbB : b ∉ B := fun hbB ↦ hb.2 (hBterminalW hbB)
    let Ca := AlternatingComponents.component W Y a
    let Wc := initialPart G W Ca
    let Yc := initialPart G Y Ca
    have haCa : a ∈ Ca :=
      AlternatingComponents.mem_component_self W Y a
    have hbCa : b ∈ Ca := hab
    have hWcwarp : G.IsWarp Wc := fun p hp q hq hpq ↦
      hW.isWarp hp.1 hq.1 hpq
    have hWccharacter : G.HasFiniteCharacter Wc := fun {_p} hp ↦
      hW.finiteCharacter hp.1
    have hYcwarp : G.IsWarp Yc := fun p hp q hq hpq ↦
      hYwarp hp.1 hq.1 hpq
    have hYccharacter : G.HasFiniteCharacter Yc := fun {_p} hp ↦
      hYcharacter hp.1
    have hYcfinite : Yc.Finite := hYfinite.subset (fun _ hp ↦ hp.1)
    have hinitC : G.initialSet Yc = insert a (G.initialSet Wc) := by
      dsimp only [Yc, Wc, Ca]
      rw [initialSet_initialPart, initialSet_initialPart, hinit]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨rfl | hxW, hxC⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hxW, hxC⟩
      · rintro (rfl | ⟨hxW, hxC⟩)
        · exact ⟨Or.inl rfl, haCa⟩
        · exact ⟨Or.inr hxW, hxC⟩
    have htermC : G.terminalFrontier Yc =
        insert b (G.terminalFrontier Wc) := by
      dsimp only [Yc, Wc, Ca]
      rw [terminalFrontier_initialPart_component_right hYcharacter a,
        terminalFrontier_initialPart_component hW.finiteCharacter a,
        hterm]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨rfl | hxW, hxC⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hxW, hxC⟩
      · rintro (rfl | ⟨hxW, hxC⟩)
        · exact ⟨Or.inl rfl, hbCa⟩
        · exact ⟨Or.inr hxW, hxC⟩
    have hOldCount : (G.initialSet Wc ∩ A).ncard =
        (G.terminalFrontier Wc ∩ B).ncard :=
      ncard_endpointColours_eq_on_component G a hW.finiteCharacter
        hAW hOld hOldTerminal
    have hbad : ∃ p ∈ Yc, p.initial ∈ A ∧
        ∃ q : DirectedPath.FinitePath G.graph,
          p = .inl q ∧ q.finish ∉ B := by
      simp only [D, exceptionalComponentVertices, Set.mem_iUnion] at haD
      obtain ⟨x, hxE, hax⟩ := haD
      have hxBad : x ∈ G.terminalFrontier Y_A \ B := hxE
      obtain ⟨p, hpYA, hpx⟩ := hxBad.1
      obtain ⟨q, rfl⟩ := hY.finiteCharacter hpYA.1
      have hxa : x ∈ Ca := by
        exact AlternatingComponents.component_symm hax
      have hsupport : q.support ⊆ Ca :=
        AlternatingComponents.finitePath_support_subset_component_of_touches_right
          hxa hpYA.1 (G.terminal_mem_support hpx)
      refine ⟨.inl q, ⟨hpYA.1, hsupport q.start_mem_support⟩,
        hpYA.2, q, rfl, ?_⟩
      have hfinish : q.finish = x := Option.some.inj hpx
      exact fun hfinishB ↦ hxBad.2 (hfinish ▸ hfinishB)
    obtain ⟨p, hpYc, hpA, q, hpq, hqB⟩ :=
      exists_oppositeCrossColouredPath_of_fresh_boundary
        hYcwarp hYccharacter hYcfinite haA hbB
          hinitC htermC hOldCount hbad
    exact ⟨p, hpYc.1, hpA, hpYc.2, q, hpq, hqB⟩
  · have hbD : b ∉ D := fun hbD ↦ haD (habD.mpr hbD)
    left
    refine ⟨haD, hbD, ?_⟩
    exact componentMixedFamily_isOnePointAugmentation_of_endpoints_compl
      G E hW.isWarp hW.finiteCharacter ha hb hYwarp hYcharacter
        hinit hterm haD hbD

/-! ## The marked residual specialization -/

/-- In the marked residual exchange, the inside branch contains a concrete
new residual-coloured path ending at the exact old touched designated
frontier.  Thus the branch is not merely an endpoint-counting obstruction:
it exposes the opposite path which a selective switch must retain. -/
theorem markedResidual_wholeComponentMix_dichotomy_with_oppositeCross
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
        K.initialSet Qplus = insert a (K.initialSet TT) ∧
        K.terminalFrontier Qplus = insert b (K.terminalFrontier TT) ∧
        ((a ∉ D ∧ b ∉ D ∧ K.IsOnePointAugmentation TT Z) ∨
          (a ∈ D ∧ b ∈ D ∧
            K.IsWarp Z ∧ K.HasFiniteCharacter Z ∧
            K.initialSet Z = K.initialSet TT ∧
            K.terminalFrontier Z = K.terminalFrontier TT ∧
            ∃ p ∈ Qplus, p.initial ∉ AP ∧
              p.initial ∈ AlternatingComponents.component TT Qplus a ∧
              ∃ q : DirectedPath.FinitePath K.graph,
                p = .inl q ∧ q.finish ∈ BT)) := by
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
  have hOldTerminal :
      K.terminalFrontier (initialRestriction K TT AP) = BT := by
    rw [hOldRestriction]
  have hAPTT : AP ⊆ K.initialSet TT :=
    initialSet_touched_designated_subset_total K P L l
  have hlocalCopy := hlocal
  obtain ⟨_a, _ha, _b, _hb, _hQwarp, _hQcharacter, hinit, _hterm⟩ :=
    hlocalCopy
  have hAPQ : AP ⊆ K.initialSet Qplus := by
    intro x hx
    rw [hinit]
    exact Or.inr (hAPTT hx)
  have hTTfinite : TT.Finite :=
    touchedDesignatedPaths_finite hJclean.isWarp l
  exact exists_wholeComponentMix_colourRepair_dichotomy_with_oppositeCross
    K hTTlink hQlink hTTfinite hQfinite hlocal
      hAPTT hAPQ hBT hOld hOldTerminal

#print axioms exists_wholeComponentMix_colourRepair_dichotomy_with_oppositeCross
#print axioms markedResidual_wholeComponentMix_dichotomy_with_oppositeCross

end SingularFiniteBadComponentExchange
end CardinalInduction
end Erdos599
