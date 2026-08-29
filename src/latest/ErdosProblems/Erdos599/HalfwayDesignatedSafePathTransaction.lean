/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayScheduledSafePathTransaction
import ErdosProblems.Erdos599.Alternating
import ErdosProblems.Erdos599.SliceSuffixFromAux

/-!
# A scheduled safe path for a designated current-cardinal source set

The public half-way clause schedules vertices of the designated set `A0`,
not necessarily every source of the ambient web.  The correct current-
cardinal construction therefore runs in the source subweb on `A0`.  Its
graph and target are unchanged, while its source has cardinality exactly
`kappa`.  A safely deletable singleton path can consequently be retained
when the current extension clause completes the remaining sources.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath
open CardinalInduction
open CardinalInduction.ControlledSlices
open CardinalInduction.RegularSafeCompletion
open CardinalInduction.SliceCandidate

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

/-- The source-subweb form of the scheduled safe-path transaction.

The complete ambient linkage starts exactly at `A`, while `front` is its
first-hit prefix at the later ladder slice and `tail` is the suffix of the
same deletion-safe path. -/
structure DesignatedSafePathTransaction
    (C : ClubStageGeometry Gamma Y kappa theta)
    (A : Set V) (z : V) where
  path : FinitePath Gamma.graph
  path_start : path.start = z
  path_finish : path.finish ∈ Gamma.target
  current : CurrentLaterLinkage C A
  path_mem_ambient :
    (Sum.inl path : Gamma.DPath) ∈ current.ambient
  front : FinitePath Gamma.graph
  front_mem_later : (Sum.inl front : Gamma.DPath) ∈ current.later
  front_start : front.start = z
  front_finish_mem : front.finish ∈ C.newSlice
  front_slice_pure : front.support ∩ C.newSlice = {front.finish}
  front_isPrefix : front.IsPrefixOf path
  tail : FinitePath Gamma.graph
  tail_start : tail.start = front.finish
  front_tail_inter : front.support ∩ tail.support = {front.finish}
  splice_eq : front.appendFinite tail tail_start
      front_tail_inter.subset = path

namespace DesignatedSafePathTransaction

variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {A : Set V} {z : V}

theorem prefix_support_subset_outerRoof
    (T : DesignatedSafePathTransaction C A z) :
    T.front.support ⊆ C.outerRoof :=
  T.current.later_in_outerRoof _ T.front_mem_later

theorem suffix_finish_mem_target
    (T : DesignatedSafePathTransaction C A z) :
    T.tail.finish ∈ Gamma.target := by
  have hfinish : T.tail.finish = T.path.finish := by
    calc
      T.tail.finish =
          (T.front.appendFinite T.tail T.tail_start
            T.front_tail_inter.subset).finish :=
        (T.front.appendFinite_finish T.tail T.tail_start
          T.front_tail_inter.subset).symm
      _ = T.path.finish := congrArg FinitePath.finish T.splice_eq
  rw [hfinish]
  exact T.path_finish

theorem prefix_support_subset_path
    (T : DesignatedSafePathTransaction C A z) :
    T.front.support ⊆ T.path.support :=
  T.front_isPrefix.support_subset

theorem prefix_edgeSet_subset_path
    (T : DesignatedSafePathTransaction C A z) :
    T.front.edgeSet ⊆ T.path.edgeSet := by
  apply Walk.edgeSet_subset_of_support_prefix
  exact T.front_isPrefix

theorem suffix_support_subset_path
    (T : DesignatedSafePathTransaction C A z) :
    T.tail.support ⊆ T.path.support := by
  rw [← T.splice_eq,
    T.front.support_appendFinite_eq_union T.tail T.tail_start
      T.front_tail_inter.subset]
  exact Set.subset_union_right

theorem suffix_edgeSet_subset_path
    (T : DesignatedSafePathTransaction C A z) :
    T.tail.edgeSet ⊆ T.path.edgeSet := by
  rw [← T.splice_eq]
  intro e he
  rw [FinitePath.edgeSet_appendFinite]
  exact Or.inr he

end DesignatedSafePathTransaction

/-- Complete a safely deletable singleton path inside a designated source
subweb, retaining that exact path as a member of the resulting linkage. -/
theorem exists_designatedLinkage_containing_safeChoice
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsUnhindered) (hNorm : Gamma.IsNormalized)
    (hkappa : aleph0 ≤ kappa)
    {A : Set V} (hA : A ⊆ Gamma.source) (hAcard : #A = kappa)
    {z : V} (hz : z ∈ A)
    (c : SafeCompletionChoice (Gamma.sourceSubweb A) ∅ z) :
    ∃ W : Set Gamma.DPath,
      IsLinkageBetween Gamma A Gamma.target W ∧
        (Sum.inl c.path : Gamma.DPath) ∈ W := by
  let H := Gamma.sourceSubweb A
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hH : H.IsUnhindered := hGamma.sourceSubweb Gamma hNoEnter hA
  have hHNorm : H.IsNormalized := by
    intro x y hxy
    exact ⟨fun hy ↦ (hNorm hxy).1 (hA hy), (hNorm hxy).2⟩
  let P : Set H.DPath := c.family
  have hP : IsLinkageBetween H {z} H.target P :=
    c.family_isLinkageBetween
  have hzH : z ∈ H.source := hz
  have hzsub : ({z} : Set V) ⊆ H.source := by
    simpa only [Set.singleton_subset_iff]
  have hsafe : (H.delete (H.vertexSet P)).IsUnhindered := by
    rw [c.vertexSet_family]
    simpa only [Set.empty_union] using c.next_unhindered
  have hsmall : #({z} : Set V) < kappa := by
    rw [Cardinal.mk_singleton]
    exact Cardinal.one_lt_aleph0.trans_le hkappa
  have hresCard : #(H.delete (H.vertexSet P)).source = kappa := by
    apply IsLinkageBetween.delete_vertexSet_source_card_eq
      hHNorm hP hzsub
    · simpa only [H, DWeb.sourceSubweb_source] using hAcard
    · simpa only [H, DWeb.sourceSubweb_source, hAcard] using hkappa
    · exact hsmall
  obtain ⟨W, hW, hPW⟩ :=
    exists_fullLinkage_containing_of_delete_unhindered
      hext hHNorm hzsub hP hsafe hresCard
  change ∃ W : Set Gamma.DPath,
    IsLinkageBetween Gamma A Gamma.target W ∧
      (Sum.inl c.path : Gamma.DPath) ∈ W
  exact ⟨W, hW, hPW (Set.mem_singleton _)⟩

/-- Unconditional current-cardinal scheduled transaction on the designated
source set.  This is the source-side producer consumed by the augmented
front-plus-tail macro transaction. -/
theorem ClubStageGeometry.exists_designatedSafePathTransaction
    (C : ClubStageGeometry Gamma Y kappa theta)
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsUnhindered)
    {A : Set V} (hA : A ⊆ Gamma.source) (hAcard : #A = kappa)
    {z : V} (hz : z ∈ A) :
    Nonempty (DesignatedSafePathTransaction C A z) := by
  let H := Gamma.sourceSubweb A
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (C.normalized hxy).1 hy
  have hH : H.IsUnhindered := hGamma.sourceSubweb Gamma hNoEnter hA
  obtain ⟨c⟩ := exists_safeCompletionChoice H ∅
    (by simpa only [DWeb.delete_empty] using hH) hz (by simp)
  obtain ⟨W, hW, hpathW⟩ :=
    exists_designatedLinkage_containing_safeChoice
      hext hGamma C.normalized C.capacity_infinite hA hAcard hz c
  have hAroof : A ⊆ C.outerRoof := hA.trans C.source_subset_outerRoof
  let hsep : RelationalRoof.Separates Gamma.graph.Adj
      A Gamma.target C.newSlice :=
    separates_target_of_subset_roof hAroof
  let later : Set Gamma.DPath := firstHitPrefixFamily hW hsep
  have hlater : IsLinkageBetween Gamma A C.newSlice later :=
    firstHitPrefixFamily_isLinkageBetween hW hsep
  have hlaterRoof : ∀ q ∈ later, q.support ⊆ C.outerRoof := by
    rintro q hq
    change q ∈ SliceSegmentCore.segmentFamily
      (firstHitSegmentRealization hW hsep) at hq
    obtain ⟨a, rfl⟩ := hq
    exact SliceRestrictedDelta.firstHit_support_subset_roof_ambient
      Gamma C.newSlice (linkageFiniteAt hW a)
      (by simpa only [linkageFiniteAt_start] using hAroof a.2)
      (linkageFiniteAt_meets hW hsep a)
  have hlaterFragment : ∀ q ∈ later,
      IsLadderFragment Gamma W q := by
    change ∀ q ∈ SliceSegmentCore.segmentFamily
        (firstHitSegmentRealization hW hsep),
      IsLadderFragment Gamma W q
    exact SliceSegmentCore.segmentFamily_isLadderFragment
      (firstHitSegmentRealization hW hsep)
  let D : CurrentLaterLinkage C A := {
    ambient := W
    later := later
    ambient_linkage := hW
    later_linkage := hlater
    later_in_outerRoof := hlaterRoof
    later_is_ambient_fragment := hlaterFragment }
  let a : A := ⟨z, hz⟩
  have hmember : (linkageMemberAt hW a).1 =
      (Sum.inl c.path : Gamma.DPath) := by
    have hinit : (linkageMemberAt hW a).1.initial = c.path.start :=
      (linkageMemberAt_initial hW a).trans c.start_eq.symm
    apply Alternating.DWeb.IsWarp.eq_of_mem_support hW.isWarp
      (x := c.path.start)
      (linkageMemberAt hW a).2 hpathW
    ·
      rw [← hinit]
      exact (linkageMemberAt hW a).1.initial_mem_support
    · change c.path.start ∈ c.path.support
      exact c.path.start_mem_support
  have hfinite : linkageFiniteAt hW a = c.path := by
    have hm := linkageMemberAt_eq_finite hW a
    rw [hmember] at hm
    exact Sum.inl.inj hm.symm
  let front : FinitePath Gamma.graph := linkageFirstHitAt hW hsep a
  have hfrontLater : (Sum.inl front : Gamma.DPath) ∈ later :=
    ⟨a, rfl⟩
  have hfrontPath : front.IsPrefixOf c.path := by
    have hpref : (linkageFirstHitAt hW hsep a).IsPrefixOf
        (linkageFiniteAt hW a) :=
      (linkageFiniteAt hW a).walk.firstHit C.newSlice
        (linkageFiniteAt_meets hW hsep a) |>.support_prefix
    simpa only [front, hfinite] using hpref
  let hfinish : front.finish ∈ c.path.support :=
    hfrontPath.support_subset front.finish_mem_support
  let tail : FinitePath Gamma.graph :=
    c.path.suffixFromAux front.finish hfinish
  obtain ⟨htailStart, _hinter, hinterEq, hsplice⟩ :=
    appendFinite_suffixFromAux_eq_of_prefix hfrontPath
  exact ⟨{
    path := c.path
    path_start := c.start_eq
    path_finish := c.finish_target
    current := D
    path_mem_ambient := hpathW
    front := front
    front_mem_later := hfrontLater
    front_start := by
      simpa only [front, a] using linkageFirstHitAt_start hW hsep a
    front_finish_mem := linkageFirstHitAt_finish_mem hW hsep a
    front_slice_pure := linkageFirstHitAt_targetPure hW hsep a
    front_isPrefix := hfrontPath
    tail := tail
    tail_start := htailStart
    front_tail_inter := hinterEq
    splice_eq := hsplice }⟩

end LinkageBlueprint
end Blueprint
end Erdos599
