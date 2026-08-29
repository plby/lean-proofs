/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayRetainedLaterLinkage
import ErdosProblems.Erdos599.RegularSafeCompletion
import ErdosProblems.Erdos599.SliceSuffixFromAux

/-!
# The scheduled safe path in Assertion 9.31

Assertion 9.31 does not retain the selected ladder reference in the later
linkage.  It chooses one safe path from the scheduled vertex to the ambient
target, extends the singleton linkage consisting of that path to a full
linkage, and stops the full linkage at its first visit to the later slice.

This file packages precisely that construction.  Its two path pieces are
paired by an exact finite-path splice equation.  In particular the target
continuation is the suffix of the originally selected safe path, not an
arbitrary path recovered from the carrier of the ambient linkage.
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

/-- Directed edges of a finite splice are exactly the edges of its two
pieces. -/
theorem FinitePath.edgeSet_appendFinite
    {D : Digraph V} (p q : FinitePath D)
    (hstart : q.start = p.finish)
    (hinter : p.support ∩ q.support ⊆ {p.finish}) :
    (p.appendFinite q hstart hinter).edgeSet =
      p.edgeSet ∪ q.edgeSet := by
  rcases p with ⟨ps, pf, pw, hp⟩
  rcases q with ⟨qs, qf, qw, hq⟩
  dsimp only at hstart
  subst qs
  change (pw.append qw).edgeSet = pw.edgeSet ∪ qw.edgeSet
  exact pw.edgeSet_append' qw

/-- A safe completion selected with no previously frozen carrier is an
ordinary safe target path in the original web. -/
theorem safeCompletionChoice_isSafeTargetPath_of_frozen_empty
    {z : V} (c : SafeCompletionChoice Gamma ∅ z) :
    Gamma.IsSafeTargetPath z c.path := by
  refine ⟨c.start_eq, c.finish_target, ?_⟩
  simpa only [Set.empty_union] using c.next_unhindered

/-- The source-faithful scheduled transaction.

`front` is the first-hit portion which belongs to the honest later row.
`tail` is the unused part of the same selected safe path.  The
`splice_eq` field says that these pieces recover that path literally.
No inclusion involving the selected ladder reference occurs here. -/
structure ScheduledSafePathTransaction
    (C : ClubStageGeometry Gamma Y kappa theta) (z : V) where
  choice : SafeCompletionChoice Gamma ∅ z
  current : CurrentLaterLinkage C Gamma.source
  path_mem_ambient :
    (Sum.inl choice.path : Gamma.DPath) ∈ current.ambient
  front : FinitePath Gamma.graph
  front_mem_later : (Sum.inl front : Gamma.DPath) ∈ current.later
  front_start : front.start = z
  front_finish_mem : front.finish ∈ C.newSlice
  front_slice_pure : front.support ∩ C.newSlice = {front.finish}
  front_isPrefix : front.IsPrefixOf choice.path
  tail : FinitePath Gamma.graph
  tail_start : tail.start = front.finish
  front_tail_inter : front.support ∩ tail.support = {front.finish}
  splice_eq : front.appendFinite tail tail_start
      front_tail_inter.subset = choice.path

namespace ScheduledSafePathTransaction

variable {C : ClubStageGeometry Gamma Y kappa theta} {z : V}

/-- The retained prefix is owned by the ambient linkage selected by the
extension step. -/
theorem prefix_is_ambient_fragment
    (T : ScheduledSafePathTransaction C z) :
    IsLadderFragment Gamma T.current.ambient
      (Sum.inl T.front : Gamma.DPath) :=
  T.current.later_is_ambient_fragment _ T.front_mem_later

/-- The retained prefix lies in the selected later roof and can therefore
be put in a closure seed constrained to that roof. -/
theorem prefix_support_subset_outerRoof
    (T : ScheduledSafePathTransaction C z) :
    T.front.support ⊆ C.outerRoof :=
  T.current.later_in_outerRoof _ T.front_mem_later

/-- The prefix carrier has size at most the transaction capacity. -/
theorem prefix_support_card_le
    (T : ScheduledSafePathTransaction C z) :
    #T.front.support ≤ kappa :=
  (Gamma.finitePath_support_finite T.front).lt_aleph0.le.trans
    C.capacity_infinite

/-- The suffix starts at the later slice and reaches the ambient target. -/
theorem suffix_finish_mem_target
    (T : ScheduledSafePathTransaction C z) :
    T.tail.finish ∈ Gamma.target := by
  have hfinish : T.tail.finish = T.choice.path.finish := by
    calc
      T.tail.finish =
          (T.front.appendFinite T.tail T.tail_start
            T.front_tail_inter.subset).finish :=
        (T.front.appendFinite_finish T.tail T.tail_start
          T.front_tail_inter.subset).symm
      _ = T.choice.path.finish := congrArg FinitePath.finish T.splice_eq
  rw [hfinish]
  exact T.choice.finish_target

/-- The stored suffix has exactly the desired boundary orientation. -/
theorem suffix_boundary
    (T : ScheduledSafePathTransaction C z) :
    T.tail.start ∈ C.newSlice ∧ T.tail.finish ∈ Gamma.target :=
  ⟨T.tail_start.symm ▸ T.front_finish_mem,
    T.suffix_finish_mem_target⟩

/-- Both pieces are literal subpaths of the chosen safe path. -/
theorem prefix_support_subset_path
    (T : ScheduledSafePathTransaction C z) :
    T.front.support ⊆ T.choice.path.support :=
  T.front_isPrefix.support_subset

theorem prefix_edgeSet_subset_path
    (T : ScheduledSafePathTransaction C z) :
    T.front.edgeSet ⊆ T.choice.path.edgeSet := by
  apply Walk.edgeSet_subset_of_support_prefix
  exact T.front_isPrefix

theorem suffix_support_subset_path
    (T : ScheduledSafePathTransaction C z) :
    T.tail.support ⊆ T.choice.path.support := by
  rw [← T.splice_eq,
    T.front.support_appendFinite_eq_union T.tail T.tail_start
      T.front_tail_inter.subset]
  exact Set.subset_union_right

theorem suffix_edgeSet_subset_path
    (T : ScheduledSafePathTransaction C z) :
    T.tail.edgeSet ⊆ T.choice.path.edgeSet := by
  rw [← T.splice_eq]
  intro e he
  rw [FinitePath.edgeSet_appendFinite]
  exact Or.inr he

/-- The spliced path retains the safe-deletion certificate selected in
Assertion 9.23. -/
theorem spliced_isSafeTargetPath
    (T : ScheduledSafePathTransaction C z) :
    Gamma.IsSafeTargetPath z
      (T.front.appendFinite T.tail T.tail_start
        T.front_tail_inter.subset) := by
  rw [T.splice_eq]
  exact safeCompletionChoice_isSafeTargetPath_of_frozen_empty T.choice

end ScheduledSafePathTransaction

/-- Construct the exact scheduled transaction from a particular safe path
choice.  Only the singleton family containing that path is retained. -/
theorem ClubStageGeometry.scheduledSafePathTransaction_of_choice
    (C : ClubStageGeometry Gamma Y kappa theta)
    (hext : UniversalExtensionClauseAt V kappa)
    (hsource : #Gamma.source = kappa)
    {z : V} (c : SafeCompletionChoice Gamma ∅ z) :
    Nonempty (ScheduledSafePathTransaction C z) := by
  let P : Set Gamma.DPath := c.family
  have hP : IsLinkageBetween Gamma {z} Gamma.target P :=
    c.family_isLinkageBetween
  have hzsource : z ∈ Gamma.source := by
    rw [← c.start_eq]
    exact c.start_source
  have hAsource : ({z} : Set V) ⊆ Gamma.source := by
    simpa only [Set.singleton_subset_iff]
  have hAroof : ({z} : Set V) ⊆ C.outerRoof :=
    hAsource.trans C.source_subset_outerRoof
  let hsep : RelationalRoof.Separates Gamma.graph.Adj
      ({z} : Set V) Gamma.target C.newSlice :=
    separates_target_of_subset_roof hAroof
  let R : Set Gamma.DPath := firstHitPrefixFamily hP hsep
  have hresidual :
      (Gamma.delete (Gamma.vertexSet P)).IsUnhindered := by
    rw [c.vertexSet_family]
    exact (safeCompletionChoice_isSafeTargetPath_of_frozen_empty c).2.2
  have hsmall : #({z} : Set V) < kappa := by
    rw [Cardinal.mk_singleton]
    exact Cardinal.one_lt_aleph0.trans_le C.capacity_infinite
  have hcard : #(Gamma.delete (Gamma.vertexSet P)).source = kappa :=
    IsLinkageBetween.delete_vertexSet_source_card_eq C.normalized hP
      hAsource hsource C.capacity_infinite hsmall
  obtain ⟨D, hPambient, hRlater⟩ :=
    C.exists_currentLaterLinkage_containing_prefixes_with_ambient
      hext C.normalized hAsource hP hresidual hcard hsep
      (Set.Subset.rfl : R ⊆ R)
  let a : ({z} : Set V) := ⟨z, Set.mem_singleton z⟩
  let front : FinitePath Gamma.graph := linkageFirstHitAt hP hsep a
  have hfrontR : (Sum.inl front : Gamma.DPath) ∈ R := by
    change (Sum.inl front : Gamma.DPath) ∈
      SliceSegmentCore.segmentFamily (firstHitSegmentRealization hP hsep)
    exact ⟨a, rfl⟩
  have hfrontLater : (Sum.inl front : Gamma.DPath) ∈ D.later :=
    hRlater hfrontR
  have hmember : (linkageMemberAt hP a).1 =
      (Sum.inl c.path : Gamma.DPath) := by
    simpa only [P, SafeCompletionChoice.family, Set.mem_singleton_iff]
      using (linkageMemberAt hP a).2
  have hfinite : linkageFiniteAt hP a = c.path := by
    have hm := linkageMemberAt_eq_finite hP a
    rw [hmember] at hm
    exact Sum.inl.inj hm.symm
  have hfrontPath : front.IsPrefixOf c.path := by
    have hpref : (linkageFirstHitAt hP hsep a).IsPrefixOf
        (linkageFiniteAt hP a) :=
      (linkageFiniteAt hP a).walk.firstHit C.newSlice
        (linkageFiniteAt_meets hP hsep a) |>.support_prefix
    simpa only [front, hfinite] using hpref
  let hfinish : front.finish ∈ c.path.support :=
    hfrontPath.support_subset front.finish_mem_support
  let tail : FinitePath Gamma.graph :=
    c.path.suffixFromAux front.finish hfinish
  obtain ⟨htailStart, hinter, hinterEq, hsplice⟩ :=
    appendFinite_suffixFromAux_eq_of_prefix hfrontPath
  refine ⟨{
    choice := c
    current := D
    path_mem_ambient := hPambient (Set.mem_singleton _)
    front := front
    front_mem_later := hfrontLater
    front_start := by
      simpa only [front, a] using linkageFirstHitAt_start hP hsep a
    front_finish_mem := linkageFirstHitAt_finish_mem hP hsep a
    front_slice_pure := linkageFirstHitAt_targetPure hP hsep a
    front_isPrefix := hfrontPath
    tail := tail
    tail_start := htailStart
    front_tail_inter := hinterEq
    splice_eq := hsplice }⟩

/-- Unconditional scheduled-path selection from unhinderedness.  This is
the direct Assertion 9.23-to-9.31 entry point: Theorem 6.1 supplies the
safe singleton path and the deletion-safe extension retains it. -/
theorem ClubStageGeometry.exists_scheduledSafePathTransaction
    (C : ClubStageGeometry Gamma Y kappa theta)
    (hext : UniversalExtensionClauseAt V kappa)
    (hGamma : Gamma.IsUnhindered)
    (hsource : #Gamma.source = kappa)
    {z : V} (hz : z ∈ Gamma.source) :
    Nonempty (ScheduledSafePathTransaction C z) := by
  obtain ⟨c⟩ := exists_safeCompletionChoice Gamma ∅
    (by simpa only [DWeb.delete_empty] using hGamma) hz (by simp)
  exact C.scheduledSafePathTransaction_of_choice hext hsource c

end LinkageBlueprint
end Blueprint
end Erdos599
