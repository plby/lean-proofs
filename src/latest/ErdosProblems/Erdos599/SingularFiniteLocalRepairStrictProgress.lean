/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualGlobalTargetRepair
import ErdosProblems.Erdos599.SingularFiniteObstacleTrivialization
import ErdosProblems.Erdos599.SingularFiniteCarrierRoofLocalization
import ErdosProblems.Erdos599.SingularFiniteRoofDefectAbsorption
import ErdosProblems.Erdos599.SingularFiniteRoofDefectAbsorptionStrong
import ErdosProblems.Erdos599.SingularFiniteRepairProfileProgress
import ErdosProblems.Erdos599.SingularSafeCompletedMachine

/-!
# Turning an arbitrary finite marked repair into strict residual progress

The target-colour repair changes only the finite marked block.  Independently
of how its alternating components are coloured, keep from the total augmented
warp all paths whose initial is not a designated source.  Those paths have the
strictly enlarged residual initial profile.  Their only intersections with the
new target linkage occur in the finite marked block, so trivializing the paths
which meet that block moves the family behind the new carrier while losing
only finitely many terminal vertices.  The finite roof-defect absorber then
turns this warp into a wave with the same enlarged initial profile.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteLocalRepairStrictProgress

open DWeb Alternating
open SliceSpliceSource
open SingularFiniteCarrierRoofLocalization
open SingularFiniteExactBoundaryRepair
open SingularFiniteObstacleTrivialization
open SingularFiniteRepairProfileProgress
open SingularFiniteRoofDefectAbsorption
open SingularFiniteRoofDefectAbsorptionStrong
open SingularMarkedResidualFiniteFactor
open SingularMarkedResidualGlobalTargetRepair
open SingularMarkedResidualColorOrder
open SingularMarkedResidualTargetColourRepair
open SingularMarkedResidualTouchedPaths
open SingularMarkedResidualTotalFiniteFactor
open SingularMaximalWaveTargetAbsorption
open SingularMaximalWaveOrderedContact
open SingularMaximalWaveTotalFiniteExchange
open SingularResidualWaveExchange
open _root_.Erdos599.Blueprint.LinkageBlueprint

universe u

variable {V : Type u}

/-- The residual-coloured initial restriction of a total one-point
augmentation retains the old residual frontier except for terminals of the
finite touched block. -/
theorem residualInitialRestriction_data
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    {l : List (OneHoleResidualState V)} {Qplus : Set G.DPath}
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
    let Jplus := untouchedDesignatedPaths K (P ∪ L) l ∪ Qplus
    let B := K.initialSet Jplus \ A
    let R := initialRestriction K Jplus B
    K.IsWarp R ∧ K.HasFiniteCharacter R ∧
      K.initialSet R = B ∧
      K.initialSet L ⊂ B ∧
      (K.terminalFrontier L \ K.terminalFrontier R) ⊆
        K.terminalFrontier TT := by
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TT := touchedDesignatedPaths K (P ∪ L) l
  let RT := untouchedDesignatedPaths K (P ∪ L) l
  let Jplus := RT ∪ Qplus
  let B := K.initialSet Jplus \ A
  let R := initialRestriction K Jplus B
  obtain ⟨a, ha, _b, _hb, hJwarp, hJfinite, hJinitial, _hJterminal⟩ :=
    hglobal
  have hP_K : IsLinkageBetween K A G.target P := by
    change IsLinkageBetween G A G.target P
    exact hP
  have hPL : Disjoint (K.vertexSet P) (K.vertexSet L) := by
    change Disjoint (G.vertexSet P)
      (G.vertexSet (G.liftDeleteFamily (G.vertexSet P) U))
    exact (G.vertexSet_liftDeleteFamily_disjoint hU.1.2.1).symm
  have hLinitialAvoidA : Disjoint (K.initialSet L) A := by
    rw [Set.disjoint_left]
    intro x hxL hxA
    obtain ⟨p, hpL, hpx⟩ := hxL
    have hxP : x ∈ K.vertexSet P := by
      have hxPinitial : x ∈ K.initialSet P :=
        hP_K.initialSet_eq.symm ▸ hxA
      obtain ⟨q, hqP, hqx⟩ := hxPinitial
      exact ⟨q, hqP, hqx ▸ q.initial_mem_support⟩
    exact Set.disjoint_left.1 hPL hxP
      ⟨p, hpL, hpx ▸ p.initial_mem_support⟩
  have hBsubset : B ⊆ K.initialSet Jplus := Set.sdiff_subset
  have hRwarp : K.IsWarp R := fun p hp q hq hpq ↦
    hJwarp hp.1 hq.1 hpq
  have hRfinite : K.HasFiniteCharacter R := fun {_p} hp ↦
    hJfinite hp.1
  have hRinitial : K.initialSet R = B := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, hp, rfl⟩
      exact hp.2
    · intro x hxB
      obtain ⟨p, hpJ, hpx⟩ := hBsubset hxB
      exact ⟨p, ⟨hpJ, hpx ▸ hxB⟩, hpx⟩
  have hLsubB : K.initialSet L ⊆ B := by
    intro x hxL
    refine ⟨?_, fun hxA ↦ Set.disjoint_left.1 hLinitialAvoidA hxL hxA⟩
    change x ∈ K.initialSet Jplus
    rw [hJinitial]
    right
    obtain ⟨p, hpL, hpx⟩ := hxL
    exact ⟨p, Or.inr hpL, hpx⟩
  have haB : a ∈ B := by
    refine ⟨?_, ?_⟩
    · change a ∈ K.initialSet Jplus
      rw [hJinitial]
      exact Or.inl rfl
    · intro haA
      apply ha.2
      have haPinitial : a ∈ K.initialSet P :=
        hP_K.initialSet_eq.symm ▸ haA
      obtain ⟨p, hpP, hpa⟩ := haPinitial
      exact ⟨p, Or.inl hpP, hpa⟩
  have haNotL : a ∉ K.initialSet L := by
    intro haL
    apply ha.2
    obtain ⟨p, hpL, hpa⟩ := haL
    exact ⟨p, Or.inr hpL, hpa⟩
  have hstrict : K.initialSet L ⊂ B :=
    Set.ssubset_iff_subset_ne.mpr ⟨hLsubB, fun heq ↦ haNotL (heq ▸ haB)⟩
  have hgap : K.terminalFrontier L \ K.terminalFrontier R ⊆
      K.terminalFrontier TT := by
    rintro x ⟨hxL, hxNotR⟩
    obtain ⟨p, hpL, hpx⟩ := hxL
    by_cases hpTT : p ∈ TT
    · exact ⟨p, hpTT, hpx⟩
    · have hpRT : p ∈ RT := ⟨Or.inr hpL, hpTT⟩
      apply False.elim
      apply hxNotR
      refine ⟨p, ⟨Or.inl hpRT, ?_⟩, hpx⟩
      apply hLsubB
      exact ⟨p, hpL, rfl⟩
  exact ⟨hRwarp, hRfinite, hRinitial, hstrict, hgap⟩

/-- Every fixed total finite marked exchange, including the exceptional
colour-component branch, yields a replacement target linkage with a strictly
larger maximal residual-wave profile. -/
theorem exists_finiteCharacterResidualProfileUpdate_of_totalExchange
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
    (hcarrierFinite :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      (K.vertexSet
        (touchedDesignatedPaths K (P ∪ L) l ∪ Qplus)).Finite)
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
    ∃ Pnew : Set G.DPath,
      IsLinkageBetween G A G.target Pnew ∧
      ∃ Wnew : Set (G.delete (G.vertexSet Pnew)).DPath,
        (G.delete (G.vertexSet Pnew)).IsWave Wnew ∧
        (G.delete (G.vertexSet Pnew)).HasFiniteCharacter Wnew ∧
        (G.delete (G.vertexSet P)).initialSet U ⊂
          (G.delete (G.vertexSet Pnew)).initialSet Wnew := by
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TT := touchedDesignatedPaths K (P ∪ L) l
  let RT := untouchedDesignatedPaths K (P ∪ L) l
  let TP := touchedDesignatedPaths K P l
  let RP := untouchedDesignatedPaths K P l
  let Jplus := RT ∪ Qplus
  let B := K.initialSet Jplus \ A
  let R := initialRestriction K Jplus B
  obtain ⟨Pnew, hPnewK, hRPsub, hPnewSub⟩ :=
    exists_globalTargetColouredRepair_of_totalExchange
      hNorm hA hP hU hUfin hlocal hglobal hRTQ
  have hPnew : IsLinkageBetween G A G.target Pnew := by
    change IsLinkageBetween K A G.target Pnew at hPnewK
    change IsLinkageBetween G A G.target Pnew
    exact hPnewK
  obtain ⟨hRwarpK, hRfiniteK, hRinitialK, hstrictK, hgapK⟩ :=
    residualInitialRestriction_data hNorm hA hP hU hglobal
  let S := K.vertexSet (TP ∪ Qplus)
  have hTPsubTT : TP ⊆ TT := by
    rintro p hp
    exact ⟨Or.inl hp.1, hp.2⟩
  have hSsub : S ⊆ K.vertexSet (TT ∪ Qplus) := by
    rintro x ⟨p, hp, hxp⟩
    rcases hp with hpTP | hpQ
    · exact ⟨p, Or.inl (hTPsubTT hpTP), hxp⟩
    · exact ⟨p, Or.inr hpQ, hxp⟩
  have hSfinite : S.Finite := hcarrierFinite.subset hSsub
  have hRPsubRT : RP ⊆ RT :=
    untouchedDesignatedPaths_mono_left K P L l
  have hJwarp : K.IsWarp Jplus := by
    obtain ⟨_a, _ha, _b, _hb, hwarp, _hfinite, _hinit, _hterm⟩ := hglobal
    exact hwarp
  have hcontact : K.vertexSet R ∩ K.vertexSet Pnew ⊆ S := by
    rintro x ⟨⟨r, hrR, hxr⟩, ⟨p, hpNew, hxp⟩⟩
    rcases hPnewSub hpNew with hpRP | hpLocal
    · have hpJ : p ∈ Jplus := Or.inl (hRPsubRT hpRP)
      have hrp : r = p :=
        DWeb.IsWarp.eq_of_mem_support hJwarp hrR.1 hpJ hxr hxp
      subst p
      have hrA : r.initial ∈ A := by
        rw [← hPnewK.initialSet_eq]
        exact ⟨r, hpNew, rfl⟩
      exact False.elim (hrR.2.2 hrA)
    · exact ⟨p, hpLocal, hxp⟩
  have hBsource : B ⊆ K.source := by
    obtain ⟨a, ha, _b, _hb, _hwarp, _hfinite, hinit, _hterm⟩ := hglobal
    intro x hxB
    have hxJ : x ∈ K.initialSet Jplus := hxB.1
    rw [hinit] at hxJ
    rcases hxJ with rfl | hxOld
    · exact ha.1
    · obtain ⟨p, hpOld, hpx⟩ := hxOld
      rcases hpOld with hpP | hpL
      · apply hA
        have hxPinitialK : x ∈ K.initialSet P := ⟨p, hpP, hpx⟩
        have hxPinitialG : x ∈ G.initialSet P := hxPinitialK
        rw [hP.initialSet_eq] at hxPinitialG
        exact hxPinitialG
      · have hxU : x ∈ (G.delete (G.vertexSet P)).initialSet U := by
          rw [← G.initialSet_liftDeleteFamily]
          exact ⟨p, hpL, hpx⟩
        exact hU.1.2.1 hxU |>.1
  have hBavoid : Disjoint B (K.vertexSet Pnew) := by
    rw [Set.disjoint_left]
    intro x hxB hxPnew
    have hxA : x ∈ A := by
      rw [← _root_.Erdos599.Blueprint.LinkageBlueprint.IsLinkageBetween.vertexSet_inter_source_eq
        hNorm hPnew hA]
      exact ⟨hxPnew, hBsource hxB⟩
    exact hxB.2 hxA
  have hRinitialAvoid : Disjoint (K.initialSet R) (K.vertexSet Pnew) := by
    rw [hRinitialK]
    exact hBavoid
  obtain ⟨W, hWwarpK, hWfiniteK, hWinitialK, hRgapFiniteK⟩ :=
    exists_deleteWarp_preserving_initial_losing_finite_frontier
      K hRwarpK hRfiniteK hSfinite hcontact hRinitialAvoid
  let X := G.vertexSet P
  let Xnew := G.vertexSet Pnew
  let Hnew := G.delete Xnew
  have hWwarp : Hnew.IsWarp W := by
    change (K.delete (K.vertexSet Pnew)).IsWarp W at hWwarpK
    exact hWwarpK
  have hWfinite : Hnew.HasFiniteCharacter W := by
    change (K.delete (K.vertexSet Pnew)).HasFiniteCharacter W at hWfiniteK
    exact hWfiniteK
  have hWinitial : Hnew.initialSet W = B := by
    change (K.delete (K.vertexSet Pnew)).initialSet W = K.initialSet R at hWinitialK
    rw [hRinitialK] at hWinitialK
    exact hWinitialK
  have hWsource : Hnew.initialSet W ⊆ Hnew.source := by
    rw [hWinitial]
    intro x hxB
    exact ⟨hBsource hxB, Set.disjoint_left.1 hBavoid hxB⟩
  have hTTfrontierFinite : (K.terminalFrontier TT).Finite := by
    exact terminalFrontier_finite_of_family_finite
      (touchedDesignatedPaths_finite
        (combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin).isWarp l)
  have hOldGapFinite :
      ((G.delete X).terminalFrontier U \ Hnew.terminalFrontier W).Finite := by
    have hLgap : (K.terminalFrontier L \ K.terminalFrontier R).Finite :=
      hTTfrontierFinite.subset hgapK
    have hRWgap : (K.terminalFrontier R \
        (K.delete (K.vertexSet Pnew)).terminalFrontier W).Finite :=
      hRgapFiniteK
    have hLfrontier : K.terminalFrontier L =
        (G.delete X).terminalFrontier U := by
      change G.terminalFrontier
        (G.liftDeleteFamily (G.vertexSet P) U) =
          (G.delete (G.vertexSet P)).terminalFrontier U
      rw [G.terminalFrontier_liftDeleteFamily]
    have hWfrontier : (K.delete (K.vertexSet Pnew)).terminalFrontier W =
        Hnew.terminalFrontier W := by
      rfl
    apply (hLgap.union hRWgap).subset
    rintro x hx
    rw [← hLfrontier, ← hWfrontier] at hx
    by_cases hxR : x ∈ K.terminalFrontier R
    · exact Or.inr ⟨hxR, hx.2⟩
    · exact Or.inl ⟨hx.1, hxR⟩
  have hFreedSub : G.vertexSet P \ G.vertexSet Pnew ⊆ S := by
    rintro x ⟨⟨p, hpP, hxp⟩, hxNotNew⟩
    by_cases hpTP : p ∈ TP
    · exact ⟨p, Or.inl hpTP, hxp⟩
    · have hpRP : p ∈ RP := ⟨hpP, hpTP⟩
      exact False.elim (hxNotNew ⟨p, hRPsub hpRP, hxp⟩)
  have hFreedFinite : (G.vertexSet P \ G.vertexSet Pnew).Finite :=
    hSfinite.subset hFreedSub
  let F := ((G.delete X).terminalFrontier U \
      Hnew.terminalFrontier W) ∪ (G.vertexSet P \ G.vertexSet Pnew)
  have hFfinite : F.Finite := hOldGapFinite.union hFreedFinite
  have hroofOld : Hnew.source ⊆ Hnew.roof
      ((G.delete X).terminalFrontier U ∪
        (G.vertexSet P \ G.vertexSet Pnew)) := by
    exact source_subset_roof_frontier_union_freedCarrier
      G (G.vertexSet P) (G.vertexSet Pnew) hU.1
  have hroof : Hnew.source ⊆ Hnew.roof (Hnew.terminalFrontier W ∪ F) := by
    apply hroofOld.trans
    apply Hnew.roof_cut
    intro x hx
    rcases hx with hxOld | hxFreed
    · by_cases hxW : x ∈ Hnew.terminalFrontier W
      · exact Hnew.subset_roof _ (Or.inl hxW)
      · exact Hnew.subset_roof _ (Or.inr (Or.inl ⟨hxOld, hxW⟩))
    · exact Hnew.subset_roof _ (Or.inr (Or.inr hxFreed))
  obtain ⟨Wwave, hWwave, hWwaveFinite, hWsub⟩ :=
    exists_finiteCharacter_wave_initialSet_superset_of_finite_roof_defect
      (SingularSafeCompletedMachine.isNormalized_delete hNorm Xnew)
      hWwarp hWfinite hWsource hFfinite hroof
  have hOldStrictW : (G.delete X).initialSet U ⊂ Hnew.initialSet W := by
    rw [hWinitial]
    have hLinitial : K.initialSet L = (G.delete X).initialSet U := by
      change G.initialSet
        (G.liftDeleteFamily (G.vertexSet P) U) =
          (G.delete (G.vertexSet P)).initialSet U
      rw [G.initialSet_liftDeleteFamily]
    rw [← hLinitial]
    exact hstrictK
  have hOldStrictWave : (G.delete X).initialSet U ⊂
      Hnew.initialSet Wwave :=
    Set.ssubset_of_ssubset_of_subset hOldStrictW hWsub
  exact ⟨Pnew, hPnew, Wwave, hWwave, hWwaveFinite, hOldStrictWave⟩

/-- Every specified finite-character residual hindrance admits a strict
finite-character profile update.  This is the ray-free successor used by a
maximal-profile argument: unlike maximalizing the new wave, the conclusion
retains finite character literally.

The only degenerate case is when the fresh residual source is itself the
fresh ambient target.  Then adjoining its trivial path already gives the
strict residual wave.  Otherwise the marked route has distinct endpoints,
so the total finite factor and the finite-defect repair above apply. -/
theorem exists_finiteCharacterResidualProfileUpdate_of_hindrance
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U) :
    ∃ Pnew : Set G.DPath,
      IsLinkageBetween G A G.target Pnew ∧
      ∃ Wnew : Set ((G.delete (G.vertexSet Pnew)).DPath),
        (G.delete (G.vertexSet Pnew)).IsWave Wnew ∧
        (G.delete (G.vertexSet Pnew)).HasFiniteCharacter Wnew ∧
        (G.delete (G.vertexSet P)).initialSet U ⊂
          (G.delete (G.vertexSet Pnew)).initialSet Wnew := by
  obtain ⟨a, b, l, ha, hb, _hbP, hl⟩ :=
    exists_markedRoute_of_specified_residual_hindrance_targetFresh
      hNorm hG hA hP hU hUfin
  by_cases hab : a = b
  · subst b
    let H := G.delete (G.vertexSet P)
    let q := DirectedPath.FinitePath.trivial H.graph a
    let Wnew : Set H.DPath := insert (.inl q : H.DPath) U
    have hNormH : H.IsNormalized :=
      SingularSafeCompletedMachine.isNormalized_delete hNorm (G.vertexSet P)
    have hdisj : Disjoint q.support (H.vertexSet U) := by
      rw [Set.disjoint_left]
      intro x hxq hxU
      have hxa : x = a := by
        simpa only [q, DirectedPath.FinitePath.support_trivial,
          Set.mem_singleton_iff] using hxq
      subst x
      obtain ⟨p, hpU, hap⟩ := hxU
      have hae : a = p.initial :=
        hNormH.eq_initial_of_mem_path p hap ha.1
      exact ha.2 ⟨p, hpU, hae.symm⟩
    have hWwarp : H.IsWarp Wnew := by
      exact DWeb.IsWarp.insert_finite_of_disjoint H hU.1.1 q hdisj
    have hWfinite : H.HasFiniteCharacter Wnew := by
      exact H.hasFiniteCharacter_insert_finite hUfin q
    have hWinitial : H.initialSet Wnew = insert a (H.initialSet U) := by
      exact H.initialSet_insert_finite U q
    have hWterminal : H.terminalFrontier Wnew =
        insert a (H.terminalFrontier U) := by
      exact H.terminalFrontier_insert_finite U q
    have hWsource : H.initialSet Wnew ⊆ H.source := by
      rw [hWinitial]
      rintro x (rfl | hx)
      · exact ha.1
      · exact hU.1.2.1 hx
    have hWroof : H.source ⊆ H.roof (H.terminalFrontier Wnew) := by
      apply hU.1.2.2.trans
      apply H.roof_mono
      rw [hWterminal]
      exact Set.subset_insert a _
    have hWwave : H.IsWave Wnew := ⟨hWwarp, hWsource, hWroof⟩
    have hstrict : H.initialSet U ⊂ H.initialSet Wnew :=
      hWinitial ▸ Set.ssubset_insert ha.2
    exact ⟨P, hP, Wnew, hWwave, hWfinite, hstrict⟩
  · let L := G.liftDeleteFamily (G.vertexSet P) U
    let K := G.retarget
      (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
    have hclean : K.IsCleanFiniteWarp (P ∪ L) :=
      combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin
    have haGap : a ∈ K.source \ K.initialSet (P ∪ L) := by
      refine ⟨ha.1.1, ?_⟩
      change a ∉ G.initialSet (P ∪ L)
      rw [G.initialSet_union, G.initialSet_liftDeleteFamily]
      rintro (haP | haU)
      · obtain ⟨p, hpP, rfl⟩ := haP
        exact ha.1.2 ⟨p, hpP, p.initial_mem_support⟩
      · exact ha.2 haU
    have hbGap : b ∈ K.target \ K.terminalFrontier (P ∪ L) := by
      refine ⟨Or.inl hb.1, ?_⟩
      change b ∉ G.terminalFrontier (P ∪ L)
      rw [G.terminalFrontier_union, G.terminalFrontier_liftDeleteFamily]
      rintro (hbPfrontier | hbU)
      · obtain ⟨p, hpP, hpterm⟩ := hbPfrontier
        exact _hbP ⟨p, hpP, G.terminal_mem_support hpterm⟩
      · exact hb.2 hbU
    obtain ⟨_hTfinite, Qplus, hQfinite, hlocal, hcarrierFinite,
        hRTQ, hglobal, _hinit, _hterminal,
        _C, _hCpath, _hCedges, _hCisolated⟩ :=
      exists_totalFiniteSupportedOnePointAugmentation_exactRelation
        hclean hl haGap hbGap hab
    exact exists_finiteCharacterResidualProfileUpdate_of_totalExchange
      hNorm hA hP hU hUfin hQfinite hlocal hcarrierFinite hRTQ hglobal

/-- Sound scheduler-facing form of the finite repair.  A chosen
finite-character hindrance can always be repaired either to a full residual
wave, or to another finite-character hindrance with a strictly larger
initial profile.  The full-wave branch is deliberately not called safe:
residual unhinderedness quantifies over every wave. -/
theorem exists_fullResidualWave_or_strictFiniteHindranceUpdate
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U) :
    (∃ Pnew : Set G.DPath,
        IsLinkageBetween G A G.target Pnew ∧
        ∃ Wnew : Set ((G.delete (G.vertexSet Pnew)).DPath),
          (G.delete (G.vertexSet Pnew)).IsWave Wnew ∧
          (G.delete (G.vertexSet Pnew)).HasFiniteCharacter Wnew ∧
          (G.delete (G.vertexSet Pnew)).initialSet Wnew =
            (G.delete (G.vertexSet Pnew)).source) ∨
      ∃ Pnew : Set G.DPath,
        IsLinkageBetween G A G.target Pnew ∧
        ∃ Wnew : Set ((G.delete (G.vertexSet Pnew)).DPath),
          (G.delete (G.vertexSet Pnew)).IsHindrance Wnew ∧
          (G.delete (G.vertexSet Pnew)).HasFiniteCharacter Wnew ∧
          (G.delete (G.vertexSet P)).initialSet U ⊂
            (G.delete (G.vertexSet Pnew)).initialSet Wnew := by
  obtain ⟨Pnew, hPnew, Wnew, hWnew, hWnewFinite, hstrict⟩ :=
    exists_finiteCharacterResidualProfileUpdate_of_hindrance
      hNorm hG hA hP hU hUfin
  by_cases hfull : (G.delete (G.vertexSet Pnew)).initialSet Wnew =
      (G.delete (G.vertexSet Pnew)).source
  · exact Or.inl ⟨Pnew, hPnew, Wnew, hWnew, hWnewFinite, hfull⟩
  · exact Or.inr ⟨Pnew, hPnew, Wnew, ⟨hWnew, hfull⟩,
      hWnewFinite, hstrict⟩

/-- Maximal-wave projection of the finite-character fixed-exchange
successor. -/
theorem exists_strictResidualProfileUpdate_of_totalExchange
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
    (hcarrierFinite :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      (K.vertexSet
        (touchedDesignatedPaths K (P ∪ L) l ∪ Qplus)).Finite)
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
    ∃ Pnew : Set G.DPath,
      IsLinkageBetween G A G.target Pnew ∧
      ∃ Mnew : (G.delete (G.vertexSet Pnew)).Wave, IsMax Mnew ∧
        (G.delete (G.vertexSet P)).initialSet U ⊂
          (G.delete (G.vertexSet Pnew)).initialSet Mnew.1 := by
  obtain ⟨Pnew, hPnew, Wnew, hWnew, _hWnewFinite, hstrict⟩ :=
    exists_finiteCharacterResidualProfileUpdate_of_totalExchange
      hNorm hA hP hU hUfin hQfinite hlocal hcarrierFinite hRTQ hglobal
  obtain ⟨Mnew, hMnewMax, hMnewStrict⟩ :=
    exists_maximalWave_with_strictly_larger_initialProfile
      (M := ⟨U, hU.1⟩) hWnew hstrict
  exact ⟨Pnew, hPnew, Mnew, hMnewMax, hMnewStrict⟩

/-- Successor theorem for a *specified* maximal residual hindrance.  This is
the exact form needed by a Zorn state: the improved profile is compared with
the essential finite part of the supplied maximal hindrance, not with an
unrelated maximal witness chosen afresh. -/
theorem exists_strictResidualProfileUpdate_of_maximalHindrance
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (M : (G.delete (G.vertexSet P)).Wave) (hMmax : IsMax M)
    (hMh : (G.delete (G.vertexSet P)).IsHindrance M.1) :
    let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
    ∃ Pnew : Set G.DPath,
      IsLinkageBetween G A G.target Pnew ∧
      ∃ Mnew : (G.delete (G.vertexSet Pnew)).Wave, IsMax Mnew ∧
        (G.delete (G.vertexSet P)).initialSet U ⊂
          (G.delete (G.vertexSet Pnew)).initialSet Mnew.1 := by
  let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
  obtain ⟨hUh, hUfin⟩ :=
    essentialWarpPart_isHindrance_hasFiniteCharacter M hMh
  obtain ⟨a, b, l, ha, hb, hbP, hl⟩ :=
    exists_markedRoute_of_specified_residual_hindrance_targetFresh
      hNorm hG hA hP hUh hUfin
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  have hclean : K.IsCleanFiniteWarp (P ∪ L) :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hUh hUfin
  have haGap : a ∈ K.source \ K.initialSet (P ∪ L) := by
    refine ⟨ha.1.1, ?_⟩
    change a ∉ G.initialSet (P ∪ L)
    rw [G.initialSet_union, G.initialSet_liftDeleteFamily]
    rintro (haP | haU)
    · obtain ⟨p, hpP, rfl⟩ := haP
      exact ha.1.2 ⟨p, hpP, p.initial_mem_support⟩
    · exact ha.2 haU
  have hbGap : b ∈ K.target \ K.terminalFrontier (P ∪ L) := by
    refine ⟨Or.inl hb.1, ?_⟩
    change b ∉ G.terminalFrontier (P ∪ L)
    rw [G.terminalFrontier_union, G.terminalFrontier_liftDeleteFamily]
    rintro (hbPfrontier | hbU)
    · obtain ⟨p, hpP, hpterm⟩ := hbPfrontier
      exact hbP ⟨p, hpP, G.terminal_mem_support hpterm⟩
    · exact hb.2 hbU
  have hcontact : ¬ Disjoint
      (oneHoleRouteBackwardEdges K (P ∪ L) l) (familyEdges P) :=
    markedRoute_not_disjoint_designatedBackward_of_maximalHindrance
      hNorm hA hP M hMmax hMh ha hb hl
  obtain ⟨i, _hi⟩ :=
    (exists_designatedBackwardContact_iff K P L l).2 hcontact
  have hab : a ≠ b := by
    intro hab
    subst b
    have hlong : 1 < l.length := by
      have hiLt := i.isLt
      omega
    have hfirst := oneHoleRoute_first hl
    have hlast := oneHoleRoute_last hl
    have heq : l[0]'(by omega) = l[l.length - 1]'(by omega) :=
      hfirst.trans hlast.symm
    have hindices : 0 = l.length - 1 :=
      (hl.2.1.getElem_inj_iff).1 heq
    omega
  obtain ⟨_hTfinite, Qplus, hQfinite, hlocal, hcarrierFinite,
      hRTQ, hglobal, _hinit, _hterminal,
      _C, _hCpath, _hCedges, _hCisolated⟩ :=
    exists_totalFiniteSupportedOnePointAugmentation_exactRelation
      hclean hl haGap hbGap hab
  exact exists_strictResidualProfileUpdate_of_totalExchange
    hNorm hA hP hUh hUfin hQfinite hlocal hcarrierFinite hRTQ hglobal

/-- Unconditional local improvement theorem.  If deleting a provisional
target linkage is hindered, the canonical marked exchange and the finite
defect absorption above produce another target linkage whose residual
maximal-wave initial profile is strictly larger. -/
theorem exists_strictResidualProfileUpdate_of_residual_hindered
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧ (G.delete (G.vertexSet P)).IsHindrance M.1 ∧
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      (G.delete (G.vertexSet P)).HasFiniteCharacter U ∧
      ∃ Pnew : Set G.DPath,
        IsLinkageBetween G A G.target Pnew ∧
        ∃ Mnew : (G.delete (G.vertexSet Pnew)).Wave, IsMax Mnew ∧
          (G.delete (G.vertexSet P)).initialSet U ⊂
            (G.delete (G.vertexSet Pnew)).initialSet Mnew.1 := by
  obtain ⟨M, hMmax, hMh, hUh, hUfin, _a, _b, l, _ha, _hb, _hbP,
      _hl, _hcontact, _hwindow, _hTfinite, _hTnonempty,
      Qplus, hQfinite, hlocal, hcarrierFinite, hRTQ, hglobal,
      _hinit, _hterminal⟩ :=
    exists_totalFiniteWindowExchangeExact_of_residual_hindered
      hNorm hG hA hP hresidual
  let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
  obtain ⟨Pnew, hPnew, Mnew, hMnew, hstrict⟩ :=
    exists_strictResidualProfileUpdate_of_totalExchange
      hNorm hA hP hUh hUfin hQfinite hlocal hcarrierFinite hRTQ hglobal
  exact ⟨M, hMmax, hMh, hUh, hUfin,
    Pnew, hPnew, Mnew, hMnew, hstrict⟩

#print axioms residualInitialRestriction_data
#print axioms exists_finiteCharacterResidualProfileUpdate_of_totalExchange
#print axioms exists_finiteCharacterResidualProfileUpdate_of_hindrance
#print axioms exists_fullResidualWave_or_strictFiniteHindranceUpdate
#print axioms exists_strictResidualProfileUpdate_of_totalExchange
#print axioms exists_strictResidualProfileUpdate_of_maximalHindrance
#print axioms exists_strictResidualProfileUpdate_of_residual_hindered

end SingularFiniteLocalRepairStrictProgress
end CardinalInduction
end Erdos599
