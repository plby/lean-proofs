/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawChangedBlockerRoot

/-!
# Stopped roots for unchanged fragments from sources or cut heads

All edges of an unchanged relevant fragment survive the actual simultaneous
deletions. Its prefix to the blocker has no boundary departure if its
initial is a source or a cut head. Combined with changed-fragment rooting,
this covers every relevant fragment on a grounded parent, and every
fragment with a cut predecessor. First hanging fragments remain separate.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Cardinal Order Set _root_.Erdos599.DirectedPath Alternating Ladder
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "D" => reservedStrongSelectedPruningData (L := L) (hL := hL) (S := S)

/-- An old request on any fragment is the fragment's actual initial. -/
theorem reservedOldRequest_mem_fragment_eq_initial
    (z : oldRequests J S.cut) (P : (J).Fragment) (hz : z.1 ∈ P.path.support) :
    z.1 = P.path.initial := by
  have hmarker := reservedOldRequest_mem_targetMarkers_of_mem_owner z P.parent_mem
    (P.support_subset hz)
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, (a, z.1) ∈ P.path.edgeSet := by
    cases hp : P.path with
    | inl p =>
        exact FinitePath.exists_incoming_edge_of_mem_support_of_ne_start p
          (by simpa only [hp, Path.support] using hz)
          (by simpa only [hp, Path.initial] using hne)
    | inr p =>
        exact Ray.hasIncoming_edgeSet_of_mem_support_of_ne_initial p
          (by simpa only [hp, Path.support] using hz)
          (by simpa only [hp, Path.initial] using hne)
  exact (popularAuxiliary_hasBoundaryIncidence L hL.legal).target_marker_root hmarker
    ⟨a, P.parent, P.parent_mem, P.edges_subset ha⟩

/-- An unchanged relevant fragment loses none of its edges globally. -/
theorem reservedRawUnchangedRelevantFragment_edges_retained
    (P : (J).Fragment) (hP : P ∈ (D).relevantG0)
    (hunchanged : ∀ (r : Request J S.cut) (e : V × V),
      e ∈ reservedRawRequestBackwardEdges r → e ∉ P.path.edgeSet) :
    P.path.edgeSet ⊆ reservedRawRetainedEdges (L := L) (hL := hL) (S := S) := by
  intro e he
  have hnotCut : e ∉ GroundingCut.CE J S.cut :=
    fun hc ↦ Set.disjoint_left.1 hP.1.1.1.1 he hc
  refine ⟨⟨⟨⟨P.parent, P.parent_mem, P.edges_subset he⟩, hnotCut⟩, ?_⟩, ?_⟩
  · intro howner
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp howner
    exact Set.disjoint_left.1 (reservedRawRelevantFragment_disjoint_startingRecord r P hP)
      (P.path.edgeSet_subset_support_prod he).1
      ((reservedStrongSelectedStartingRecord r).record.edgeSet_subset_support_prod hr).1
  · intro hback
    have hi : e ∈ ⋃ r : Request J S.cut, reservedRawRequestBackwardEdges r := by
      rw [← reservedRawBackward_diff_cut]
      exact ⟨hback, hnotCut⟩
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hi
    exact hunchanged r e hr he

section Canonical

variable (preferred : Stage kappa → Option V)
variable (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
variable (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
variable (hLc : IsKappaHindrance (canonicalDeferredLadder Gamma kappa preferred))
variable (Sc : Popular.PopularSeparator
  (popularAuxiliaryIndexed (canonicalDeferredLadder Gamma kappa preferred) hLc))

local notation "Lc" => canonicalDeferredLadder Gamma kappa preferred
local notation "Jc" => popularAuxiliaryInput Lc hLc.legal
local notation "Dc" => reservedStrongSelectedPruningData (L := Lc) (hL := hLc) (S := Sc)
local notation "Tc" => reservedStrongSelectedSourceFirstBB (L := Lc) (hL := hLc) (S := Sc)

include hkappa huncountable hNoEnter in
/-- A source-initial or cut-preceded fragment has no reference departure from CV. -/
theorem canonicalDeferredLadder_fragment_referenceTail_not_mem_CV
    (P : (Jc).Fragment)
    (hinit : P.path.initial ∈ Gamma.source ∨
      GroundingConcreteControls.hasCutPredecessor Jc Sc.cut P)
    {e : V × V} (he : e ∈ P.path.edgeSet) : e.1 ∉ GroundingCut.CV Jc Sc.cut := by
  intro hxCV
  have href : e ∈ (Jc).familyEdges := ⟨P.parent, P.parent_mem, P.edges_subset he⟩
  have hnotFinite : e.1 ∉ (Jc).finiteSource := by
    intro hxFinite
    exact (popularAuxiliary_hasBoundaryIncidence Lc hLc.legal).finite_source_sink
      hxFinite ⟨e.2, href⟩
  let z : oldRequests Jc Sc.cut := ⟨e.1, hxCV, hnotFinite⟩
  have hxinit := reservedOldRequest_mem_fragment_eq_initial z P
    (P.path.edgeSet_subset_support_prod he).1
  change e.1 = P.path.initial at hxinit
  rcases hinit with hsource | ⟨f, _hfCut, hfParent, hfHead⟩
  · apply canonicalDeferredLadder_rawRequest_not_source
      preferred hkappa huncountable hNoEnter hLc Sc (.inl z)
    change e.1 ∈ Gamma.source
    exact hxinit.symm ▸ hsource
  · have hmarker := reservedOldRequest_mem_targetMarkers_of_mem_owner z P.parent_mem
      (P.support_subset (P.path.edgeSet_subset_support_prod he).1)
    have hhead : f.2 = z.1 := hfHead.trans hxinit.symm
    apply (popularAuxiliary_hasBoundaryIncidence Lc hLc.legal).target_marker_root hmarker
    exact ⟨f.1, P.parent, P.parent_mem, by simpa only [← hhead] using hfParent⟩

include hkappa huncountable hNoEnter in
/-- The prefix to an unchanged blocker survives the exact stopping relation. -/
theorem canonicalDeferredLadder_rawUnchangedBlocker_prefix_stopped
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hinit : P.path.initial ∈ Gamma.source ∨
      GroundingConcreteControls.hasCutPredecessor Jc Sc.cut P)
    (hunchanged : ∀ (r : Request Jc Sc.cut) (e : V × V),
      e ∈ reservedRawRequestBackwardEdges r → e ∉ P.path.edgeSet)
    (q : FinitePath Gamma.graph)
    (hqEdges : q.edgeSet ⊆ P.path.edgeSet)
    (hqFinish : q.finish = GroundingCut.blockingPoint Jc Sc.cut P) :
    q.edgeSet ⊆ reservedRawStoppedEdges (L := Lc) (hL := hLc) (S := Sc) Tc := by
  intro e he
  have heP := hqEdges he
  refine ⟨Or.inl (reservedRawUnchangedRelevantFragment_edges_retained P hP hunchanged heP), ?_⟩
  intro hxT
  have hxBB := reservedStrongSelectedSourceFirstBB_subset_relevantBB hxT
  rcases hxBB with hxCV | hxBL
  · exact canonicalDeferredLadder_fragment_referenceTail_not_mem_CV
      preferred hkappa huncountable hNoEnter hLc Sc P hinit heP hxCV
  · have hxLegacy := (Dc).relevantBL_subset_legacyBL hxBL
    have hxb : e.1 = GroundingCut.blockingPoint Jc Sc.cut P :=
      Set.mem_singleton_iff.mp
        (GroundingFragmentUniqueness.support_inter_BL_subset_blockingPoint hP.1.1.1
          ⟨(P.path.edgeSet_subset_support_prod heP).1, hxLegacy⟩)
    exact FinitePath.source_ne_finish_of_mem_edgeSet q he (hxb.trans hqFinish.symm)

include hkappa huncountable hNoEnter in
/-- Source or cut-predecessor initials suffice to root every relevant blocker. -/
theorem canonicalDeferredLadder_rawBlocker_sourceRooted_of_source_or_cutPredecessor
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hinit : P.path.initial ∈ Gamma.source ∨
      GroundingConcreteControls.hasCutPredecessor Jc Sc.cut P) :
    reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc)
      (GroundingCut.blockingPoint Jc Sc.cut P) := by
  classical
  by_cases hchanged : ∃ (r : Request Jc Sc.cut) (e : V × V),
      e ∈ reservedRawRequestBackwardEdges r ∧ e ∈ P.path.edgeSet
  · obtain ⟨r, e, he, heP⟩ := hchanged
    exact canonicalDeferredLadder_rawChangedBlocker_sourceRooted
      preferred hkappa huncountable hNoEnter hLc Sc r P hP he heP
  · have hunchanged : ∀ (r : Request Jc Sc.cut) (e : V × V),
        e ∈ reservedRawRequestBackwardEdges r → e ∉ P.path.edgeSet :=
      fun r e he heP ↦ hchanged ⟨r, e, he, heP⟩
    have hiRoot : reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc)
        P.path.initial := by
      rcases hinit with hsource | ⟨f, hfCut, _hfParent, hfHead⟩
      · exact reservedRawSourceRooted_of_source hsource
      · have hr := canonicalDeferredLadder_rawRequest_sourceRooted
          preferred hkappa huncountable hNoEnter hLc Sc (.inr ⟨f, hfCut.1⟩)
        change reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc) f.2 at hr
        exact hfHead ▸ hr
    obtain ⟨q, hstart, hfinish, _hsupport, hedges⟩ :=
      GroundingPathPrefix.exists_initialFinitePrefix P.path
        (GroundingCut.blockingPoint_mem_support Jc Sc.cut P hP.1.2)
    have hstopped := canonicalDeferredLadder_rawUnchangedBlocker_prefix_stopped
      preferred hkappa huncountable hNoEnter hLc Sc P hP hinit hunchanged q hedges hfinish
    obtain ⟨a, ha, hai⟩ := hiRoot
    refine ⟨a, ha, hai.trans ?_⟩
    have hroute := Relation.ReflTransGen.mono
      (fun _ _ he ↦ hstopped he) q.start q.finish (Walk.reflTransGen_edgeSet q.walk)
    simpa only [hstart, hfinish] using hroute

include hkappa huncountable hNoEnter in
/-- All relevant fragments of a source-grounded parent have stopped blocker roots. -/
theorem canonicalDeferredLadder_rawBlocker_sourceRooted_of_parent_grounded
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hground : P.parent.initial ∈ Gamma.source) :
    reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc)
      (GroundingCut.blockingPoint Jc Sc.cut P) := by
  apply canonicalDeferredLadder_rawBlocker_sourceRooted_of_source_or_cutPredecessor
    preferred hkappa huncountable hNoEnter hLc Sc P hP
  rcases GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
      Jc Sc.cut P hP.1.1.1 with hi | hc
  · exact Or.inl (hi ▸ hground)
  · exact Or.inr hc

include hkappa huncountable hNoEnter in
/-- Any still-unrooted relevant blocker is confined to an unchanged first
fragment of a hanging parent. No such case is declared impossible here. -/
theorem canonicalDeferredLadder_rawUnrootedBlocker_first_hanging
    (P : (Jc).Fragment) (hP : P ∈ (Dc).relevantG0)
    (hnotRoot : ¬ reservedRawSourceRooted (L := Lc) (hL := hLc) (S := Sc)
      (GroundingCut.blockingPoint Jc Sc.cut P)) :
    P.path.initial = P.parent.initial ∧ P.parent.initial ∉ Gamma.source ∧
      ¬ GroundingConcreteControls.hasCutPredecessor Jc Sc.cut P ∧
      ∀ r : Request Jc Sc.cut, Disjoint (reservedRawRequestBackwardEdges r) P.path.edgeSet := by
  have hnoCut : ¬ GroundingConcreteControls.hasCutPredecessor Jc Sc.cut P := by
    intro hc
    exact hnotRoot (canonicalDeferredLadder_rawBlocker_sourceRooted_of_source_or_cutPredecessor
      preferred hkappa huncountable hNoEnter hLc Sc P hP (Or.inr hc))
  refine ⟨(GroundingFragmentPredecessor.initial_eq_parent_initial_or_hasCutPredecessor
    Jc Sc.cut P hP.1.1.1).resolve_right hnoCut, ?_, hnoCut, ?_⟩
  · intro hground
    exact hnotRoot (canonicalDeferredLadder_rawBlocker_sourceRooted_of_parent_grounded
      preferred hkappa huncountable hNoEnter hLc Sc P hP hground)
  · intro r
    apply Set.disjoint_left.mpr
    intro e he heP
    exact hnotRoot (canonicalDeferredLadder_rawChangedBlocker_sourceRooted
      preferred hkappa huncountable hNoEnter hLc Sc r P hP he heP)

end Canonical

#print axioms reservedOldRequest_mem_fragment_eq_initial
#print axioms reservedRawUnchangedRelevantFragment_edges_retained
#print axioms canonicalDeferredLadder_rawBlocker_sourceRooted_of_source_or_cutPredecessor
#print axioms canonicalDeferredLadder_rawBlocker_sourceRooted_of_parent_grounded
#print axioms canonicalDeferredLadder_rawUnrootedBlocker_first_hanging

end Erdos599.DWeb.KappaLadder.Deferred
