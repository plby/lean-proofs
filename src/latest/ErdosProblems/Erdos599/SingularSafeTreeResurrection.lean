/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeDesignatedLimit

/-!
# Resurrecting a residual wave around a retained target linkage

At a limit of a safe-link construction it is not enough that every proper
initial deletion is unhindered.  A maximal wave in the final residual must
be promoted back across the entire limiting carrier.  This file isolates a
sharp sufficient certificate for that promotion.

Let `P` be a target linkage and let `X` be its carrier.  If every first
vertex after an exit from `X` is roofed by some wave of `G.delete X`, then a
maximal residual wave roofs all those exit vertices simultaneously: the
source-arrow construction and maximality absorb each witnessing wave.  The
union of `P` and the lifted maximal wave is then a wave of `G`.  Paths which
hit `X` at their target are stopped by the terminal frontier of `P`; all
other paths are treated after their last exit from `X`.

Thus, in an unhindered normalized web, the final residual is unhindered.
The certificate records exactly the safe-tree information which must be
retained by an infinite designated-source selection, rather than assuming
continuity of unhinderedness under an arbitrary union of carriers.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeTreeResurrection

open SingularSafeDesignatedLinkage SingularSafeDesignatedLimit

universe u

variable {V : Type u}

/-- Promote a residual wave around a retained target linkage.

`T` may contain target vertices, unlike the tree set in the usual
source-faithful boundary-promotion lemma.  The weaker and exact condition is
that every target vertex of `T` already belongs to the terminal frontier of
the retained linkage. -/
theorem linkage_boundary_promotes_deleted_wave
    (G : DWeb V) {A T : Set V} {P : Set G.DPath}
    (hA : A ⊆ G.source)
    (hP : IsLinkageBetween G A G.target P)
    (hcarrier : G.vertexSet P ⊆ T)
    (hTtarget : T ∩ G.target ⊆ G.terminalFrontier P)
    {U : Set ((G.delete (G.vertexSet P)).DPath)}
    (hU : (G.delete (G.vertexSet P)).IsWave U)
    (hboundary : SafeLink.Walk.outBoundary G.graph T ⊆
      (G.delete (G.vertexSet P)).roof
        ((G.delete (G.vertexSet P)).terminalFrontier U)) :
    G.IsWave (P ∪ G.liftDeleteFamily (G.vertexSet P) U) := by
  let X : Set V := G.vertexSet P
  let H : DWeb V := G.delete X
  let L : Set G.DPath := G.liftDeleteFamily X U
  have hLavoid : Disjoint (G.vertexSet L) X := by
    exact G.vertexSet_liftDeleteFamily_disjoint hU.2.1
  have hwarp : G.IsWarp (P ∪ L) := by
    apply Set.PairwiseDisjoint.union hP.isWarp hU.1.liftDeleteFamily
    intro p hp q hq _hpq
    apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 hLavoid ⟨q, hq, hxq⟩ ⟨p, hp, hxp⟩
  have hinitial : G.initialSet (P ∪ L) ⊆ G.source := by
    rw [G.initialSet_union, hP.initialSet_eq,
      G.initialSet_liftDeleteFamily]
    exact Set.union_subset hA (hU.2.1.trans Set.sdiff_subset)
  refine ⟨hwarp, hinitial, ?_⟩
  rw [G.terminalFrontier_union, G.terminalFrontier_liftDeleteFamily]
  intro b hb p hp
  by_cases hpfinishT : p.finish ∈ T
  · exact ⟨p.finish, p.finish_mem_support,
      Or.inl (hTtarget ⟨hpfinishT, hp.2⟩)⟩
  · by_cases hmeetT : p.walk.Meets T
    · obtain ⟨E⟩ := SafeLink.Walk.exists_lastExit
        p.walk T hmeetT hpfinishT
      have hboundaryE : E.outside ∈
          SafeLink.Walk.outBoundary G.graph T :=
        ⟨E.outside_not_mem, E.inside, E.inside_mem, E.edge⟩
      have hsuffixAvoidX : SafeLink.Walk.Avoids E.suffix X := by
        intro x hx hxX
        exact E.suffix_avoids x hx (hcarrier hxX)
      let original : DirectedPath.FinitePath G.graph :=
        { start := E.outside
          finish := p.finish
          walk := E.suffix
          isPath := E.suffix_isPath p.isPath }
      let deleted : DirectedPath.FinitePath H.graph :=
        SafeLink.FinitePath.toDelete G X original hsuffixAvoidX
      have hpfinishX : p.finish ∉ X := fun hfinishX ↦
        hpfinishT (hcarrier hfinishX)
      obtain ⟨x, hxdeleted, hxfrontier⟩ :=
        hboundary hboundaryE deleted ⟨rfl, hp.2, hpfinishX⟩
      have hxsuffix : x ∈ E.suffix.support := by
        change x ∈ deleted.support at hxdeleted
        rw [SafeLink.FinitePath.support_toDelete] at hxdeleted
        exact hxdeleted
      exact ⟨x, E.support_suffix.subset hxsuffix, Or.inr hxfrontier⟩
    · have havoidX : SafeLink.Walk.Avoids p.walk X := by
        intro x hxp hxX
        exact hmeetT ⟨x, hxp, hcarrier hxX⟩
      let deleted : DirectedPath.FinitePath H.graph :=
        SafeLink.FinitePath.toDelete G X p havoidX
      have hbX : b ∉ X := havoidX b
        (hp.1 ▸ p.walk.start_mem_support)
      have hpfinishX : p.finish ∉ X :=
        havoidX p.finish p.walk.end_mem_support
      obtain ⟨x, hxdeleted, hxfrontier⟩ := hU.2.2 ⟨hb, hbX⟩
        deleted ⟨by simpa [deleted] using hp.1, hp.2, hpfinishX⟩
      have hxp : x ∈ p.support := by
        simpa [deleted] using hxdeleted
      exact ⟨x, hxp, Or.inr hxfrontier⟩

/-- In a normalized target linkage, every target vertex of the entire
carrier is the terminal vertex of its component. -/
theorem vertexSet_inter_target_subset_terminalFrontier
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P) :
    G.vertexSet P ∩ G.target ⊆ G.terminalFrontier P := by
  rintro x ⟨⟨p, hpP, hxp⟩, hxTarget⟩
  obtain ⟨q, rfl⟩ := hP.finiteCharacter hpP
  have hxfinish : x = q.finish :=
    hNorm.eq_finish_of_mem_walk q.walk hxp hxTarget
  subst x
  exact ⟨Sum.inl q, hpP, rfl⟩

/-- Every carrier-boundary vertex has an individual residual-wave
certificate.  Maximal-wave absorption will make these certificates
simultaneous without choosing one enormous union of waves. -/
def CarrierBoundaryWaveCovered (G : DWeb V) (P : Set G.DPath) : Prop :=
  ∀ y ∈ SafeLink.Walk.outBoundary G.graph (G.vertexSet P),
    ∃ U : (G.delete (G.vertexSet P)).Wave,
      y ∈ (G.delete (G.vertexSet P)).roof
        ((G.delete (G.vertexSet P)).terminalFrontier U.1)

/-- A forward-extension-maximal residual wave absorbs all the individual
boundary-wave certificates. -/
theorem boundary_subset_roof_of_isMax
    {G : DWeb V} {P : Set G.DPath}
    (hcover : CarrierBoundaryWaveCovered G P)
    (M : (G.delete (G.vertexSet P)).Wave) (hMmax : IsMax M) :
    SafeLink.Walk.outBoundary G.graph (G.vertexSet P) ⊆
      (G.delete (G.vertexSet P)).roof
        ((G.delete (G.vertexSet P)).terminalFrontier M.1) := by
  intro y hy
  obtain ⟨U, hyU⟩ := hcover y hy
  exact (G.delete (G.vertexSet P)).roofLE_of_isMax hMmax U hyU

/-! ## Collective retained-tree certificates

The boundary of a single selected path is not the right object: a safely
deletable path can have an outgoing branch which is not roofed by any wave
after that path is deleted.  Section 6 retains a larger maximal safe tree.
For many choices the correct limit object is therefore the union of all
retained trees, and all boundary waves must live in one common deletion.
-/

/-- Every outer-boundary point of every retained tree is roofed by a wave in
the *same* residual web left by the whole selected linkage. -/
def CollectiveTreeBoundaryWaveCovered
    (G : DWeb V) (P : Set G.DPath) {I : Type*} (T : I → Set V) : Prop :=
  ∀ i y, y ∈ G.outerBoundary (T i) →
    ∃ U : (G.delete (G.vertexSet P)).Wave,
      y ∈ (G.delete (G.vertexSet P)).roof
        ((G.delete (G.vertexSet P)).terminalFrontier U.1)

/-- An exit from the union of retained trees is an exit from one of its
members. -/
theorem outerBoundary_iUnion_subset_iUnion_outerBoundary
    (G : DWeb V) {I : Type*} (T : I → Set V) :
    G.outerBoundary (⋃ i, T i) ⊆ ⋃ i, G.outerBoundary (T i) := by
  rintro y ⟨hyUnion, x, hxUnion, hxy⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxUnion
  apply Set.mem_iUnion.2
  refine ⟨i, ?_⟩
  refine ⟨?_, x, hxi, hxy⟩
  intro hyi
  exact hyUnion (Set.mem_iUnion.2 ⟨i, hyi⟩)

/-- A maximal wave in the common residual simultaneously absorbs the
boundary waves of every retained tree, and hence roofs the boundary of their
union.  This absorption is performed before any selected path is projected
out of the tree system. -/
theorem collective_outerBoundary_subset_roof_of_isMax
    {G : DWeb V} {P : Set G.DPath} {I : Type*} {T : I → Set V}
    (hcover : CollectiveTreeBoundaryWaveCovered G P T)
    (M : (G.delete (G.vertexSet P)).Wave) (hMmax : IsMax M) :
    SafeLink.Walk.outBoundary G.graph (⋃ i, T i) ⊆
      (G.delete (G.vertexSet P)).roof
        ((G.delete (G.vertexSet P)).terminalFrontier M.1) := by
  intro y hy
  have hy' : y ∈ ⋃ i, G.outerBoundary (T i) :=
    outerBoundary_iUnion_subset_iUnion_outerBoundary G T hy
  obtain ⟨i, hyi⟩ := Set.mem_iUnion.1 hy'
  obtain ⟨U, hyU⟩ := hcover i y hyi
  exact (G.delete (G.vertexSet P)).roofLE_of_isMax hMmax U hyU

/-- Resurrect a common-deletion maximal wave only after all retained safe
trees have been absorbed.  No boundary premise is imposed on any individual
selected path carrier. -/
theorem maximal_wave_resurrects_with_collective_trees
    {G : DWeb V} {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath} (hP : IsLinkageBetween G A G.target P)
    {I : Type*} {T : I → Set V}
    (hcarrier : G.vertexSet P ⊆ ⋃ i, T i)
    (htarget : (⋃ i, T i) ∩ G.target ⊆ G.terminalFrontier P)
    (hcover : CollectiveTreeBoundaryWaveCovered G P T)
    (M : (G.delete (G.vertexSet P)).Wave) (hMmax : IsMax M) :
    G.IsWave (P ∪ G.liftDeleteFamily (G.vertexSet P) M.1) := by
  apply linkage_boundary_promotes_deleted_wave G hA hP hcarrier htarget M.2
  exact collective_outerBoundary_subset_roof_of_isMax hcover M hMmax

/-- The collective retained-tree certificate makes the selected linkage
ambiently safe.  This is the common-deletion form suitable for a simultaneous
or transfinite tree selection. -/
theorem isUnhindered_delete_of_collective_trees
    {G : DWeb V} (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath} (hP : IsLinkageBetween G A G.target P)
    {I : Type*} {T : I → Set V}
    (hcarrier : G.vertexSet P ⊆ ⋃ i, T i)
    (htarget : (⋃ i, T i) ∩ G.target ⊆ G.terminalFrontier P)
    (hcover : CollectiveTreeBoundaryWaveCovered G P T) :
    (G.delete (G.vertexSet P)).IsUnhindered := by
  apply SingularSafeDesignatedLimit.isUnhindered_of_maximalWaveComplete
  intro M hMmax
  have hresurrect :
      G.IsWave (P ∪ G.liftDeleteFamily (G.vertexSet P) M.1) :=
    maximal_wave_resurrects_with_collective_trees hA hP hcarrier htarget
      hcover M hMmax
  have hfull := G.isUnhindered_iff.mp hG
    (P ∪ G.liftDeleteFamily (G.vertexSet P) M.1) hresurrect
  rw [G.initialSet_union, hP.initialSet_eq,
    G.initialSet_liftDeleteFamily] at hfull
  apply Set.Subset.antisymm M.2.2.1
  intro x hx
  have hxUnion : x ∈ A ∪
      (G.delete (G.vertexSet P)).initialSet M.1 := hfull.symm ▸ hx.1
  rcases hxUnion with hxA | hxM
  · have hxInitial : x ∈ G.initialSet P := by
      simpa [hP.initialSet_eq] using hxA
    obtain ⟨p, hpP, hxp⟩ := hxInitial
    exact (hx.2 ⟨p, hpP, hxp ▸ p.initial_mem_support⟩).elim
  · exact hxM

/-- Package the collective tree theorem in the machine-facing safe linkage
interface. -/
def safeDesignatedLinkageOfCollectiveTrees
    {G : DWeb V} (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source)
    {P : Set G.DPath} (hP : IsLinkageBetween G A G.target P)
    {I : Type*} {T : I → Set V}
    (hcarrier : G.vertexSet P ⊆ ⋃ i, T i)
    (htarget : (⋃ i, T i) ∩ G.target ⊆ G.terminalFrontier P)
    (hcover : CollectiveTreeBoundaryWaveCovered G P T) :
    SafeDesignatedLinkage G A where
  paths := P
  linkage := hP
  residual_unhindered := isUnhindered_delete_of_collective_trees
    hG hA hP hcarrier htarget hcover

/-- Every maximal wave in the residual can be resurrected together with
the retained linkage. -/
theorem maximal_wave_resurrects_with_linkage
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hcover : CarrierBoundaryWaveCovered G P)
    (M : (G.delete (G.vertexSet P)).Wave) (hMmax : IsMax M) :
    G.IsWave (P ∪ G.liftDeleteFamily (G.vertexSet P) M.1) := by
  apply linkage_boundary_promotes_deleted_wave G hA hP
    (Set.Subset.rfl)
    (vertexSet_inter_target_subset_terminalFrontier hNorm hP)
    M.2
  exact boundary_subset_roof_of_isMax hcover M hMmax

/-- A carrier-boundary-covered target linkage is ambiently safe.

This is the joint exchange/limit theorem needed by a retained-safe-tree
selection: the conclusion includes unhinderedness after deleting the whole
linkage carrier, not merely after each proper construction stage. -/
theorem isUnhindered_delete_vertexSet_of_boundary_covered
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hcover : CarrierBoundaryWaveCovered G P) :
    (G.delete (G.vertexSet P)).IsUnhindered := by
  apply SingularSafeDesignatedLimit.isUnhindered_of_maximalWaveComplete
  intro M hMmax
  have hresurrect :
      G.IsWave (P ∪ G.liftDeleteFamily (G.vertexSet P) M.1) :=
    maximal_wave_resurrects_with_linkage hNorm hA hP hcover M hMmax
  have hfull := G.isUnhindered_iff.mp hG
    (P ∪ G.liftDeleteFamily (G.vertexSet P) M.1) hresurrect
  rw [G.initialSet_union, hP.initialSet_eq,
    G.initialSet_liftDeleteFamily] at hfull
  apply Set.Subset.antisymm M.2.2.1
  intro x hx
  have hxUnion : x ∈ A ∪
      (G.delete (G.vertexSet P)).initialSet M.1 := hfull.symm ▸ hx.1
  rcases hxUnion with hxA | hxM
  · have hxInitial : x ∈ G.initialSet P := by
      simpa [hP.initialSet_eq] using hxA
    obtain ⟨p, hpP, hxp⟩ := hxInitial
    exact (hx.2 ⟨p, hpP, hxp ▸ p.initial_mem_support⟩).elim
  · exact hxM

/-- Constructor in the exact interface consumed by the safe-completed row
machine. -/
def safeDesignatedLinkageOfBoundaryCovered
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hcover : CarrierBoundaryWaveCovered G P) :
    SafeDesignatedLinkage G A where
  paths := P
  linkage := hP
  residual_unhindered :=
    isUnhindered_delete_vertexSet_of_boundary_covered
      hG hNorm hA hP hcover

#print axioms linkage_boundary_promotes_deleted_wave
#print axioms isUnhindered_delete_of_collective_trees
#print axioms safeDesignatedLinkageOfCollectiveTrees
#print axioms isUnhindered_delete_vertexSet_of_boundary_covered
#print axioms safeDesignatedLinkageOfBoundaryCovered

end SingularSafeTreeResurrection
end CardinalInduction
end Erdos599
