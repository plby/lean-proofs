/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualTargetColourRepair

/-!
# Splicing the finite target-colour repair into the untouched linkage

The component repair of the finite mixed block has support only in the old
touched designated family and the new finite replacement.  The total-factor
construction makes both of those carriers disjoint from every untouched old
component.  Consequently the repaired block can be united with the untouched
designated paths to recover a target linkage on the whole original designated
source set.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualGlobalTargetRepair

open DWeb Alternating
open SingularRetargetedRow
  SingularMarkedResidualTouchedPaths
  SingularMarkedResidualFiniteFactor
  SingularMarkedResidualEndpointSupport
  SingularMarkedResidualTargetColourRepair
  SingularFiniteEndpointColorRepair
  SliceSpliceSource

universe u

variable {V : Type u}

/-- Untouched members of a subfamily are untouched in the corresponding
larger family. -/
theorem untouchedDesignatedPaths_mono_left
    (K : DWeb V) (P L : Set K.DPath)
    (l : List (OneHoleResidualState V)) :
    untouchedDesignatedPaths K P l ⊆
      untouchedDesignatedPaths K (P ∪ L) l := by
  rintro p hp
  refine ⟨Or.inl hp.1, ?_⟩
  intro hpTotal
  exact hp.2 ⟨hp.1, hpTotal.2⟩

/-- The finite target-colour repair is compatible with every untouched
designated component.  Their union is a linkage from the entire original
designated source set to the original target. -/
theorem exists_globalTargetColouredRepair_of_totalExchange
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U)
    {l : List (OneHoleResidualState V)} {Qplus : Set G.DPath}
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
        (untouchedDesignatedPaths K (P ∪ L) l ∪ Qplus))
    (havoid :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      Disjoint
        (K.vertexSet (untouchedDesignatedPaths K (P ∪ L) l))
        (K.vertexSet Qplus)) :
    let K := G.retarget
      (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
    let TP := touchedDesignatedPaths K P l
    let RP := untouchedDesignatedPaths K P l
    ∃ Pnew : Set K.DPath,
      IsLinkageBetween K A G.target Pnew ∧
      RP ⊆ Pnew ∧ Pnew ⊆ RP ∪ (TP ∪ Qplus) := by
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TP := touchedDesignatedPaths K P l
  let RP := untouchedDesignatedPaths K P l
  let RT := untouchedDesignatedPaths K (P ∪ L) l
  let AP := K.initialSet TP
  have hP_K : IsLinkageBetween K A G.target P := by
    change IsLinkageBetween G A G.target P
    exact hP
  have hTP : IsLinkageBetween K AP G.target TP :=
    isLinkageBetween_subfamily hP_K
      (touchedDesignatedPaths_subset K P l)
  have hRP : IsLinkageBetween K (K.initialSet RP) G.target RP :=
    isLinkageBetween_subfamily hP_K
      (untouchedDesignatedPaths_subset K P l)
  have hQclean : K.IsCleanFiniteWarp Qplus :=
    localReplacement_clean hNorm hA hP hU hUfin hglobal
  obtain ⟨a, _ha, b, _hb, _hQwarp, _hQfinite,
      hQinitial, _hQterminal⟩ := hlocal
  have hAPtotal : AP ⊆
      K.initialSet (touchedDesignatedPaths K (P ∪ L) l) :=
    initialSet_touched_designated_subset_total K P L l
  have hAPQ : AP ⊆ K.initialSet Qplus := by
    intro x hx
    rw [hQinitial]
    exact Or.inr (hAPtotal hx)
  obtain ⟨Y, Q, hYeq, _hYlink, _hQeq, hQsub, hQlink⟩ :=
    exists_targetColouredComponentRepair_of_clean_with_support
      hTP hQclean hAPQ Set.subset_union_left
  have hYsub : Y ⊆ Qplus := by
    intro p hp
    rw [hYeq] at hp
    exact hp.1
  have hQsub' : Q ⊆ TP ∪ Qplus := by
    intro p hp
    rcases hQsub hp with hpTP | hpY
    · exact Or.inl hpTP
    · exact Or.inr (hYsub hpY)
  have hRPRT : RP ⊆ RT :=
    untouchedDesignatedPaths_mono_left K P L l
  have hdisjoint : Disjoint (K.vertexSet RP) (K.vertexSet Q) := by
    rw [Set.disjoint_left]
    rintro x hxRP hxQ
    obtain ⟨q, hqQ, hxq⟩ := hxQ
    rcases hQsub' hqQ with hqTP | hqPlus
    · exact Set.disjoint_left.1
        (disjoint_vertexSet_touched_untouched hP_K.isWarp l).symm
        hxRP ⟨q, hqTP, hxq⟩
    · apply Set.disjoint_left.1 havoid
      · obtain ⟨p, hpRP, hxp⟩ := hxRP
        exact ⟨p, hRPRT hpRP, hxp⟩
      · exact ⟨q, hqPlus, hxq⟩
  have hunion : IsLinkageBetween K
      (K.initialSet RP ∪ AP) G.target (RP ∪ Q) :=
    linkageBetween_union_of_vertexSet_disjoint K hRP hQlink hdisjoint
  have hdomain : K.initialSet RP ∪ AP = A := by
    change K.initialSet RP ∪ K.initialSet TP = A
    rw [← K.initialSet_union,
      untouched_union_touched K P l, hP_K.initialSet_eq]
  rw [hdomain] at hunion
  refine ⟨RP ∪ Q, hunion, Set.subset_union_left, ?_⟩
  rintro p (hpRP | hpQ)
  · exact Or.inl hpRP
  · exact Or.inr (hQsub' hpQ)

#print axioms untouchedDesignatedPaths_mono_left
#print axioms exists_globalTargetColouredRepair_of_totalExchange

end SingularMarkedResidualGlobalTargetRepair
end CardinalInduction
end Erdos599
