/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMaximalWaveTotalFiniteExchange
import ErdosProblems.Erdos599.SingularFiniteEndpointColorRepair
import ErdosProblems.Erdos599.SingularMarkedResidualEndpointSupport

/-!
# Repairing the designated colour in the finite residual exchange

The total finite factor of a marked residual rerouting supplies an uncoloured
one-point augmentation.  Its members starting at the finitely many touched
designated sources can finish either in the original target or in the
residual frontier.  Here we apply whole-component replacement to repair that
endpoint colour.  Untouched paths are first factored out globally; this is
also what lets us prove cleanliness of the local replacement in the
retargeted web, whose enlarged target need not be normalized.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularMarkedResidualTargetColourRepair

open DWeb Alternating
open SingularResidualWaveExchange
  SingularMarkedResidualTouchedPaths
  SingularMarkedResidualFiniteFactor
  SingularMarkedResidualEndpointSupport
  SingularMarkedResidualTotalFiniteFactor
  SingularMaximalWaveTotalFiniteExchange
  SingularFiniteEndpointColorRepair
  SliceSpliceSource

universe u

variable {V : Type u}

private theorem isPathBetween_mono_source
    {K : DWeb V} {A A' B : Set V} {p : K.DPath}
    (h : IsPathBetween K A B p) (hsub : A' ⊆ A)
    (hinit : p.initial ∈ A') : IsPathBetween K A' B p := by
  obtain ⟨q, rfl, hends, hsource⟩ := h
  refine ⟨q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA' | hxB⟩
      · exact hends ▸ ⟨hxq, Or.inl (hsub hxA')⟩
      · exact hends ▸ ⟨hxq, Or.inr hxB⟩
    · rintro x (hxs | hxf)
      · subst x
        exact ⟨q.start_mem_support, Or.inl hinit⟩
      · have hfinishOld : q.finish ∈ q.support ∩ (A ∪ B) := by
          have hxfEq : x = q.finish := Set.mem_singleton_iff.mp hxf
          subst x
          rw [hends]
          exact Or.inr rfl
        have hxfEq : x = q.finish := Set.mem_singleton_iff.mp hxf
        subst x
        rcases hfinishOld.2 with hfinishA | hfinishB
        · have hfinishStart : q.finish = q.start := by
            have : q.finish ∈ ({q.start} : Set V) := by
              rw [← hsource]
              exact ⟨q.finish_mem_support, hfinishA⟩
            exact Set.mem_singleton_iff.mp this
          exact ⟨q.finish_mem_support,
            Or.inl (hfinishStart.symm ▸ hinit)⟩
        · exact ⟨q.finish_mem_support, Or.inr hfinishB⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA'⟩
      exact hsource ▸ ⟨hxq, hsub hxA'⟩
    · rintro x hx
      have hxs : x = q.start := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨q.start_mem_support, hinit⟩

/-- The touched designated initials occur among the initials of the total
touched old block. -/
theorem initialSet_touched_designated_subset_total
    (K : DWeb V) (P L : Set K.DPath)
    (l : List (OneHoleResidualState V)) :
    K.initialSet (touchedDesignatedPaths K P l) ⊆
      K.initialSet (touchedDesignatedPaths K (P ∪ L) l) := by
  rintro x ⟨p, hp, rfl⟩
  refine ⟨p, ?_, rfl⟩
  exact ⟨Or.inl hp.1, hp.2⟩

/-- Any subfamily of a linkage remains a linkage on the initial vertices of
that subfamily, with the same target. -/
theorem isLinkageBetween_subfamily
    {K : DWeb V} {A B : Set V} {P T : Set K.DPath}
    (hP : IsLinkageBetween K A B P) (hTP : T ⊆ P) :
    IsLinkageBetween K (K.initialSet T) B T := by
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · intro p hp q hq hpq
    exact hP.isWarp (hTP hp) (hTP hq) hpq
  · intro p hp
    exact hP.finiteCharacter (hTP hp)
  · intro x hx
    obtain ⟨p, hpT, hpx⟩ := hx
    exact hP.terminalFrontier_subset ⟨p, hTP hpT, hpx⟩
  · intro p hp
    apply isPathBetween_mono_source
      (hP.endpointPure p (hTP hp))
    · intro x hx
      rw [← hP.initialSet_eq]
      obtain ⟨q, hqT, hqx⟩ := hx
      exact ⟨q, hTP hqT, hqx⟩
    · exact ⟨p, hp, rfl⟩

/-- A global augmentation which fixes the untouched total block makes the
local replacement clean.  The proof uses the old residual frontier as a
protected part of the enlarged target. -/
theorem localReplacement_clean
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U)
    {l : List (OneHoleResidualState V)} {Qplus : Set G.DPath}
    (hglobal :
      let L := G.liftDeleteFamily (G.vertexSet P) U
      let K := G.retarget
        (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
      K.IsOnePointAugmentation (P ∪ L)
        (untouchedDesignatedPaths K (P ∪ L) l ∪ Qplus)) :
    let K := G.retarget
      (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
    K.IsCleanFiniteWarp Qplus := by
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let S := (G.delete (G.vertexSet P)).terminalFrontier U
  let K := G.retarget (G.target ∪ S)
  let R := untouchedDesignatedPaths K (P ∪ L) l
  have hJclean : K.IsCleanFiniteWarp (P ∪ L) :=
    combinedWarp_isCleanFiniteWarp hNorm hA hP hU hUfin
  have hSfrontier : S ⊆ K.terminalFrontier (P ∪ L) := by
    intro x hx
    change x ∈ G.terminalFrontier (P ∪ L)
    rw [G.terminalFrontier_union, G.terminalFrontier_liftDeleteFamily]
    exact Or.inr hx
  have hglobalClean : K.IsCleanFiniteWarp (R ∪ Qplus) :=
    onePointAugmentation_clean_of_protectedFrontier
      hNorm hJclean hSfrontier hglobal
  exact SingularFiniteEndpointColorRepair.cleanFiniteWarp_mono
    hglobalClean Set.subset_union_right

/-- The finite uncoloured block produced by a marked residual exchange has
an honest replacement linkage on the touched designated initials which ends
in the *original* target. -/
theorem exists_targetColouredRepair_of_totalExchange
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsHindrance U)
    (hUfin : (G.delete (G.vertexSet P)).HasFiniteCharacter U)
    {a b : V} {l : List (OneHoleResidualState V)}
    {Qplus : Set G.DPath}
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
    let K := G.retarget
      (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
    let AP := K.initialSet (touchedDesignatedPaths K P l)
    ∃ Y Q : Set K.DPath,
      Y = initialRestriction K Qplus AP ∧
      IsLinkageBetween K AP K.target Y ∧
      IsLinkageBetween K AP G.target Q := by
  let L := G.liftDeleteFamily (G.vertexSet P) U
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TP := touchedDesignatedPaths K P l
  let TT := touchedDesignatedPaths K (P ∪ L) l
  let AP := K.initialSet TP
  have hP_K : IsLinkageBetween K A G.target P := by
    change IsLinkageBetween G A G.target P
    exact hP
  have hTP : IsLinkageBetween K AP G.target TP := by
    exact isLinkageBetween_subfamily hP_K
      (touchedDesignatedPaths_subset K P l)
  have hQclean : K.IsCleanFiniteWarp Qplus :=
    localReplacement_clean hNorm hA hP hU hUfin hglobal
  obtain ⟨a', _ha', _b', _hb', _hwarp, _hfinite, hinitial, _hterminal⟩ :=
    hlocal
  have hAPTT : AP ⊆ K.initialSet TT :=
    initialSet_touched_designated_subset_total K P L l
  have hAPQ : AP ⊆ K.initialSet Qplus := by
    intro x hx
    rw [hinitial]
    exact Or.inr (hAPTT hx)
  exact exists_targetColouredComponentRepair_of_clean
    hTP hQclean hAPQ Set.subset_union_left

/-- Unconditional finite designated-colour repair extracted from every
hindered deletion of a target linkage.  The repaired request is finite,
nonempty, lies in the original designated source set, and links to the
original target in the residual-frontier retargeting. -/
theorem exists_finiteNonemptyTargetColouredRepair_of_residual_hindered
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered) :
    ∃ M : (G.delete (G.vertexSet P)).Wave,
      IsMax M ∧
      let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
      (G.delete (G.vertexSet P)).IsHindrance U ∧
      ∃ AP : Set V, ∃ Q : Set G.DPath,
        AP.Finite ∧ AP.Nonempty ∧ AP ⊆ A ∧
        let K := G.retarget
          (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
        IsLinkageBetween K AP G.target Q := by
  obtain ⟨M, hMmax, _hMh, hUh, hUfin, a, b, l, _ha, _hb, _hbP,
      _hl, _hcontact, _hwindow, _hTTfinite, hTPnonempty,
      Qplus, _hQfinite, hlocal, _hcarrierFinite, _havoid, hglobal⟩ :=
    exists_totalFiniteWindowExchange_of_residual_hindered
      hNorm hG hA hP hresidual
  let U := (G.delete (G.vertexSet P)).essentialWarpPart M.1
  let K := G.retarget
    (G.target ∪ (G.delete (G.vertexSet P)).terminalFrontier U)
  let TP := touchedDesignatedPaths K P l
  let AP := K.initialSet TP
  obtain ⟨_Y, Q, _hYeq, _hY, hQ⟩ :=
    exists_targetColouredRepair_of_totalExchange
      hNorm hA hP hUh hUfin (a := a) (b := b) hlocal hglobal
  have hAPfinite : AP.Finite := by
    exact initialSet_touchedDesignatedPaths_finite hP.isWarp l
  have hAPnonempty : AP.Nonempty := by
    obtain ⟨p, hp⟩ := hTPnonempty
    exact ⟨p.initial, p, hp, rfl⟩
  have hAPsub : AP ⊆ A := by
    exact initialSet_touchedDesignatedPaths_subset hP l
  exact ⟨M, hMmax, hUh, AP, Q, hAPfinite, hAPnonempty, hAPsub, hQ⟩

#print axioms initialSet_touched_designated_subset_total
#print axioms isLinkageBetween_subfamily
#print axioms localReplacement_clean
#print axioms exists_targetColouredRepair_of_totalExchange
#print axioms exists_finiteNonemptyTargetColouredRepair_of_residual_hindered

end SingularMarkedResidualTargetColourRepair
end CardinalInduction
end Erdos599
