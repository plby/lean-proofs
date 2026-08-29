/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMarkedResidualTargetColourRepair

/-!
# A finite-support target-linkage update

The colour repair of the finite marked window is assembled here with every
untouched designated member.  The result is a full target linkage on the
original designated source set.  Outside the finite contact block the old
linkage is retained literally.

This is deliberately an update of the linkage rather than a residual
augmentation avoiding its old carrier: the latter would contradict the
maximal residual hindrance and is not available for an arbitrary provisional
linkage.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteTargetLinkageUpdate

open DWeb Alternating
open SingularResidualWaveExchange
  SingularMarkedResidualTouchedPaths
  SingularMarkedResidualFiniteFactor
  SingularMarkedResidualEndpointSupport
  SingularMaximalWaveTotalFiniteExchange
  SingularFiniteEndpointColorRepair
  SingularMarkedResidualTargetColourRepair
  SliceSpliceSource SliceCandidate

universe u

variable {V : Type u}

private theorem initialSet_subset_vertexSet
    (G : DWeb V) (W : Set G.DPath) :
    G.initialSet W ⊆ G.vertexSet W := by
  rintro x ⟨p, hp, rfl⟩
  exact ⟨p, hp, p.initial_mem_support⟩

private theorem IsPathBetween.expand_source_union_left
    {G : DWeb V} {A A' B : Set V} {W W' : Set G.DPath}
    {p : G.DPath} (hp : IsPathBetween G A B p)
    (hpW : p ∈ W) (hA' : A' ⊆ G.initialSet W')
    (hdisjoint : Disjoint (G.vertexSet W) (G.vertexSet W')) :
    IsPathBetween G (A ∪ A') B p := by
  obtain ⟨q, rfl, hends, hsource⟩ := hp
  have havoid : Disjoint q.support A' := by
    apply Set.disjoint_left.2
    intro x hxq hxA'
    exact Set.disjoint_left.1 hdisjoint
      ⟨.inl q, hpW, hxq⟩
      (initialSet_subset_vertexSet G W' (hA' hxA'))
  refine ⟨q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, (hxA | hxA') | hxB⟩
      · have hxOld : x ∈ q.support ∩ (A ∪ B) :=
          ⟨hxq, Or.inl hxA⟩
        exact hends ▸ hxOld
      · exact False.elim (Set.disjoint_left.1 havoid hxq hxA')
      · have hxOld : x ∈ q.support ∩ (A ∪ B) :=
          ⟨hxq, Or.inr hxB⟩
        exact hends ▸ hxOld
    · rintro x (hxStart | hxFinish)
      · have hxOld : x ∈ q.support ∩ (A ∪ B) := by
          rw [hends]
          exact Or.inl hxStart
        exact ⟨hxOld.1, hxOld.2.elim
          (fun hxA ↦ Or.inl (Or.inl hxA)) Or.inr⟩
      · have hxOld : x ∈ q.support ∩ (A ∪ B) := by
          rw [hends]
          exact Or.inr hxFinish
        exact ⟨hxOld.1, hxOld.2.elim
          (fun hxA ↦ Or.inl (Or.inl hxA)) Or.inr⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA | hxA'⟩
      · have hxOld : x ∈ q.support ∩ A := ⟨hxq, hxA⟩
        exact hsource ▸ hxOld
      · exact False.elim (Set.disjoint_left.1 havoid hxq hxA')
    · rintro x hx
      have hxOld : x ∈ q.support ∩ A := by
        rw [hsource]
        exact hx
      exact ⟨hxOld.1, Or.inl hxOld.2⟩

/-- Disjoint linkages with disjoint carriers may be united.  Their source
sets are united and their target is unchanged. -/
theorem linkage_union_of_vertexDisjoint
    {G : DWeb V} {A A' B : Set V} {W W' : Set G.DPath}
    (hW : IsLinkageBetween G A B W)
    (hW' : IsLinkageBetween G A' B W')
    (hdisjoint : Disjoint (G.vertexSet W) (G.vertexSet W')) :
    IsLinkageBetween G (A ∪ A') B (W ∪ W') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpW | hpW'
    · rcases hq with hqW | hqW'
      · exact hW.isWarp hpW hqW hpq
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 hdisjoint
          ⟨p, hpW, hxp⟩ ⟨q, hqW', hxq⟩
    · rcases hq with hqW | hqW'
      · apply Set.disjoint_left.2
        intro x hxp hxq
        exact Set.disjoint_left.1 hdisjoint
          ⟨q, hqW, hxq⟩ ⟨p, hpW', hxp⟩
      · exact hW'.isWarp hpW' hqW' hpq
  · intro p hp
    exact hp.elim hW.finiteCharacter hW'.finiteCharacter
  · rw [G.initialSet_union, hW.initialSet_eq, hW'.initialSet_eq]
  · rw [G.terminalFrontier_union]
    exact Set.union_subset hW.terminalFrontier_subset
      hW'.terminalFrontier_subset
  · intro p hp
    rcases hp with hpW | hpW'
    · exact IsPathBetween.expand_source_union_left
        (hW.endpointPure p hpW) hpW
        (by rw [hW'.initialSet_eq]) hdisjoint
    · rw [Set.union_comm]
      exact IsPathBetween.expand_source_union_left
        (hW'.endpointPure p hpW') hpW'
        (by rw [hW.initialSet_eq]) hdisjoint.symm

/-- If the provisional target linkage has a hindered deletion, it admits a
finite-support target-linkage update.  Every untouched member is retained
literally, while the touched designated block is replaced by a linkage to
the original target. -/
theorem exists_finiteSupportTargetLinkageUpdate_of_residual_hindered
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ l : List (OneHoleResidualState V), ∃ Q P' : Set G.DPath,
      let TP := touchedDesignatedPaths G P l
      let RP := untouchedDesignatedPaths G P l
      TP.Finite ∧ TP.Nonempty ∧ Q.Finite ∧
      (G.vertexSet (TP ∪ Q)).Finite ∧
      P = RP ∪ TP ∧ P' = RP ∪ Q ∧ RP ⊆ P' ∧
      Disjoint (G.vertexSet RP) (G.vertexSet Q) ∧
      IsLinkageBetween G A G.target P' := by
  obtain ⟨M, _hMmax, _hMh, hUh, hUfin, a, b, l, _ha, _hb, _hbP,
      _hl, _hcontact, _hwindow, _hTTfinite, hTPnonempty,
      Qplus, _hQfinite, hlocal, _hcarrierFinite, hRtotalQ, hglobal⟩ :=
    exists_totalFiniteWindowExchange_of_residual_hindered
      hNorm hG hA hP hresidual
  let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TP := touchedDesignatedPaths K P l
  let RP := untouchedDesignatedPaths K P l
  let TT := touchedDesignatedPaths K (P ∪ L) l
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
    localReplacement_clean hNorm hA hP hUh hUfin hglobal
  obtain ⟨a', _ha', _b', _hb', _hwarp, _hfinite, hinitial, _hterminal⟩ :=
    hlocal
  have hAPTT : AP ⊆ K.initialSet TT :=
    initialSet_touched_designated_subset_total K P L l
  have hAPQplus : AP ⊆ K.initialSet Qplus := by
    intro x hx
    rw [hinitial]
    exact Or.inr (hAPTT hx)
  obtain ⟨Y, Q, hYeq, hY, _hQeq, hQsub, hQ⟩ :=
    exists_targetColouredComponentRepair_of_clean_with_support
      hTP hQclean hAPQplus Set.subset_union_left
  have hYsubQplus : Y ⊆ Qplus := by
    rw [hYeq]
    intro p hp
    exact hp.1
  have hRPRT : RP ⊆ RT := by
    rintro p hp
    refine ⟨Or.inl hp.1, ?_⟩
    intro hpTT
    exact hp.2 ⟨hp.1, hpTT.2⟩
  have hTPRP : Disjoint (K.vertexSet TP) (K.vertexSet RP) :=
    disjoint_vertexSet_touched_untouched hP.isWarp l
  have hQRP : Disjoint (K.vertexSet Q) (K.vertexSet RP) := by
    apply Set.disjoint_left.2
    rintro x ⟨p, hpQ, hxp⟩ hxRP
    rcases hQsub hpQ with hpTP | hpY
    · exact Set.disjoint_left.1 hTPRP
        ⟨p, hpTP, hxp⟩ hxRP
    · exact Set.disjoint_left.1 hRtotalQ
        (by
          obtain ⟨r, hrRP, hxr⟩ := hxRP
          exact ⟨r, hRPRT hrRP, hxr⟩)
        ⟨p, hYsubQplus hpY, hxp⟩
  have hfullInit : K.initialSet RP ∪ AP = A := by
    rw [← K.initialSet_union]
    have hRPTP : RP ∪ TP = P :=
      untouched_union_touched K P l
    rw [hRPTP]
    exact hP.initialSet_eq
  have hP'K : IsLinkageBetween K A G.target (RP ∪ Q) := by
    rw [← hfullInit]
    exact linkage_union_of_vertexDisjoint hRP hQ hQRP.symm
  have hP'G : IsLinkageBetween G A G.target (RP ∪ Q) := by
    change IsLinkageBetween K A G.target (RP ∪ Q)
    exact hP'K
  have hTPfinite : TP.Finite := touchedDesignatedPaths_finite hP.isWarp l
  have hlocalCarrierSubset : K.vertexSet (TP ∪ Q) ⊆
      K.vertexSet (TT ∪ Qplus) := by
    rintro x ⟨p, hp, hxp⟩
    rcases hp with hpTP | hpQ
    · exact ⟨p, Or.inl
        ⟨Or.inl (touchedDesignatedPaths_subset K P l hpTP), hpTP.2⟩, hxp⟩
    · rcases hQsub hpQ with hpTP | hpY
      · exact ⟨p, Or.inl
          ⟨Or.inl (touchedDesignatedPaths_subset K P l hpTP), hpTP.2⟩, hxp⟩
      · exact ⟨p, Or.inr (hYsubQplus hpY), hxp⟩
  have hlocalCarrierFinite : (K.vertexSet (TP ∪ Q)).Finite :=
    _hcarrierFinite.subset hlocalCarrierSubset
  have hYfinite : Y.Finite := _hQfinite.subset hYsubQplus
  have hQfinite : Q.Finite :=
    (hTPfinite.union hYfinite).subset hQsub
  have hPsplit : P = RP ∪ TP :=
    (untouched_union_touched K P l).symm
  exact ⟨l, Q, RP ∪ Q, hTPfinite, hTPnonempty, hQfinite,
    hlocalCarrierFinite, hPsplit, rfl, Set.subset_union_left,
    hQRP.symm, hP'G⟩

#print axioms linkage_union_of_vertexDisjoint
#print axioms exists_finiteSupportTargetLinkageUpdate_of_residual_hindered

end SingularFiniteTargetLinkageUpdate
end CardinalInduction
end Erdos599
