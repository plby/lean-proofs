/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOldSliceDiamondAdvance

/-!
# The mixed-frontier state of a scheduled old-slice diamond

A single Assertion 9.31 transaction extends one old-frontier terminal to the
next frontier.  It does not extend all other old-frontier terminals.  Thus the
first diamond is not, in general, a blueprint whose terminal boundary is only
the new frontier.  This file records the honest intermediate invariant: its
terminal boundary is the union of the old and new frontiers.

The elementary lemmas below also show that a finite diamond preserves initial
vertices, ray members, and the cardinal bound on the path family.  These are
the invariants needed by the eventual old-terminal exhaustion recursion.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

section Diamond

variable (cut : LinkageBlueprint Gamma Y kappa)
variable (p : FinitePath (imaginaryGraph Gamma Y kappa))
variable (hp : (.inl p : Path _) ∈ cut.paths)
variable (P : FinitePath Gamma.graph)
variable (hstart : P.start = p.finish)
variable (hfresh : cut.vertexSet ∩ P.support ⊆ {p.finish})

private abbrev hold : p.support ∩ P.support ⊆ {p.finish} :=
  fun _x hx ↦ hfresh ⟨⟨.inl p, hp, hx.1⟩, hx.2⟩

/-- A finite diamond does not create or delete a ray member. -/
theorem mem_diamond_paths_ray_iff
    (r : Ray (imaginaryGraph Gamma Y kappa)) :
    (.inr r : Path _) ∈ (cut.diamond p hp P hstart hfresh).paths ↔
      (.inr r : Path _) ∈ cut.paths := by
  simp [diamond, diamondPaths]

/-- A finite diamond keeps the initial set literally unchanged. -/
theorem initialSet_diamond :
    (cut.diamond p hp P hstart hfresh).initialSet = cut.initialSet := by
  ext x
  change
    (∃ q ∈ (cut.diamond p hp P hstart hfresh).paths, q.initial = x) ↔
      ∃ q ∈ cut.paths, q.initial = x
  constructor
  · rintro ⟨q, hq, rfl⟩
    change q ∈ diamondPaths cut p P hstart (hold cut p hp P hfresh) at hq
    simp only [diamondPaths, Set.mem_union, Set.mem_sdiff,
      Set.mem_singleton_iff] at hq
    rcases hq with hq | hq
    · exact ⟨q, hq.1, rfl⟩
    · subst q
      exact ⟨.inl p, hp, (diamondPath_start p P hstart
        (hold cut p hp P hfresh)).symm⟩
  · rintro ⟨q, hq, rfl⟩
    by_cases hqp : q = (.inl p : Path _)
    · subst q
      refine ⟨.inl (diamondPath p P hstart
        (hold cut p hp P hfresh)), ?_, ?_⟩
      · change (.inl (diamondPath p P hstart
          (hold cut p hp P hfresh)) : Path _) ∈
          diamondPaths cut p P hstart (hold cut p hp P hfresh)
        exact Or.inr rfl
      · exact diamondPath_start p P hstart
          (hold cut p hp P hfresh)
    · refine ⟨q, ?_, rfl⟩
      change q ∈ diamondPaths cut p P hstart
        (hold cut p hp P hfresh)
      exact Or.inl ⟨hq, hqp⟩

/-- A finite diamond can only retain an old terminal or create the finish of
the appended path. -/
theorem terminalSet_diamond_subset :
    (cut.diamond p hp P hstart hfresh).terminalSet ⊆
      cut.terminalSet ∪ {P.finish} := by
  intro x hx
  change ∃ q ∈ (cut.diamond p hp P hstart hfresh).paths,
    (imaginaryWeb Gamma Y kappa).terminal? q = some x at hx
  obtain ⟨q, hq, hqx⟩ := hx
  change q ∈ diamondPaths cut p P hstart
    (hold cut p hp P hfresh) at hq
  simp only [diamondPaths, Set.mem_union, Set.mem_sdiff,
    Set.mem_singleton_iff] at hq
  rcases hq with hq | hq
  · exact Or.inl ⟨q, hq.1, hqx⟩
  · subst q
    apply Or.inr
    apply Set.mem_singleton_iff.2
    change some (diamondPath p P hstart
      (hold cut p hp P hfresh)).finish = some x at hqx
    have hsome : some P.finish = some x := by
      simpa only [diamondPath_finish] using hqx
    exact Option.some.inj hsome |>.symm

/-- Replacing one path by one path does not increase the cardinality beyond
one extra element. -/
theorem mk_diamond_paths_le :
    #(cut.diamond p hp P hstart hfresh).paths ≤ #cut.paths + 1 := by
  change #(diamondPaths cut p P hstart
    (hold cut p hp P hfresh)) ≤ #cut.paths + 1
  refine (Cardinal.mk_union_le _ _).trans ?_
  apply add_le_add
  · exact Cardinal.mk_le_mk_of_subset Set.sdiff_subset
  · rw [Cardinal.mk_singleton]

/-- At an infinite capacity, the usual blueprint path bound survives a
finite diamond. -/
theorem mk_diamond_paths_le_of_infinite
    (hkappa : aleph0 ≤ kappa) (hcard : #cut.paths ≤ kappa) :
    #(cut.diamond p hp P hstart hfresh).paths ≤ kappa := by
  exact (mk_diamond_paths_le cut p hp P hstart hfresh).trans
    (Cardinal.add_le_of_le hkappa hcard (by
      simpa only [Cardinal.mk_singleton] using
        (Cardinal.one_le_aleph0.trans hkappa)))

/-- Since the only new member is finite, the strong-edge condition on ray
members is preserved exactly. -/
theorem infinitelyManyStrongEdges_diamond
    (hstrong : cut.InfinitelyManyStrongEdges) :
    (cut.diamond p hp P hstart hfresh).InfinitelyManyStrongEdges := by
  intro r hr
  exact hstrong r ((mem_diamond_paths_ray_iff
    cut p hp P hstart hfresh r).1 hr)

end Diamond

namespace strongEdgeIndices

/-- Strong indices on a ray tail are the translated strong indices of the
original ray. -/
theorem tail (r : Ray (imaginaryGraph Gamma Y kappa)) (m : ℕ) :
    strongEdgeIndices (r.tail m) =
      {n | m + n ∈ strongEdgeIndices r} := by
  ext n
  simp [strongEdgeIndices, Ray.tail_apply, Nat.add_assoc]

/-- Removing a finite prefix cannot destroy infinitude of strong indices. -/
theorem infinite_tail {r : Ray (imaginaryGraph Gamma Y kappa)}
    (hr : (strongEdgeIndices r).Infinite) (m : ℕ) :
    (strongEdgeIndices (r.tail m)).Infinite := by
  rw [tail]
  intro hfinite
  have hsubset : strongEdgeIndices r ⊆
      Set.Iio m ∪ (fun n : ℕ ↦ m + n) ''
        {n | m + n ∈ strongEdgeIndices r} := by
    intro n hn
    by_cases hnm : n < m
    · exact Or.inl hnm
    · apply Or.inr
      refine ⟨n - m, ?_, ?_⟩
      · change m + (n - m) ∈ strongEdgeIndices r
        rwa [Nat.add_sub_of_le (Nat.le_of_not_gt hnm)]
      · exact Nat.add_sub_of_le (Nat.le_of_not_gt hnm)
  apply hr
  apply (Set.finite_Iio m).union (hfinite.image (fun n : ℕ ↦ m + n)) |>.subset
  exact hsubset

end strongEdgeIndices

/-- The honest induction invariant while old-frontier terminals are being
scheduled one at a time. -/
structure IsMixedFrontierBlueprint
    {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
    (W : LinkageBlueprint Gamma C.selectedReference kappa)
    (Z : Set V) : Prop where
  vertices_roofed : W.vertexSet ⊆ Gamma.roof C.newSlice
  covers_source : Gamma.source ⊆
    W.initialSet ∪ W.retainedReferenceInitials (C.oldSlice ∪ C.newSlice)
  vertices_closed : W.vertexSet ⊆ Z
  card_paths : #W.paths ≤ kappa
  infinitely_many_strong : W.InfinitelyManyStrongEdges
  terminals_mixed : W.terminalSet ⊆
    {x | IsPopular Gamma C.selectedReference C.persistent kappa x} ∪
      (C.oldSlice ∪ C.newSlice)

namespace IsCutAt

variable {W cut : LinkageBlueprint Gamma Y kappa} {u : V}

/-- Deleting an edge cannot destroy an initial vertex. -/
theorem initialSet_mono (h : W.IsCutAt cut u) :
    W.initialSet ⊆ cut.initialSet := by
  rw [W.initialSet_eq_no_incoming, cut.initialSet_eq_no_incoming]
  rintro x ⟨hxW, hxin⟩
  refine ⟨?_, ?_⟩
  · rw [h.vertexSet_eq]
    exact hxW
  · rintro ⟨y, hyx⟩
    exact hxin ⟨y, h.edgeSet_subset hyx⟩

private theorem mk_paths_le_mk_vertexSet
    (U : LinkageBlueprint Gamma Y kappa) :
    #U.paths ≤ #U.vertexSet := by
  let f : U.paths → U.vertexSet := fun p ↦
    ⟨p.1.initial, ⟨p.1, p.2, p.1.initial_mem_support⟩⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro p q hpq
  apply Subtype.ext
  apply Alternating.DWeb.IsWarp.eq_of_mem_support U.isWarp
    p.2 q.2 p.1.initial_mem_support
  have hinitial : p.1.initial = q.1.initial :=
    congrArg Subtype.val hpq
  exact hinitial.symm ▸ q.1.initial_mem_support

/-- The cut retains the blueprint cardinal bound because it has exactly the
same carrier. -/
theorem card_paths_le (h : W.IsCutAt cut u)
    (hkappa : aleph0 ≤ kappa) (hcard : #W.paths ≤ kappa) :
    #cut.paths ≤ kappa := by
  refine (mk_paths_le_mk_vertexSet cut).trans ?_
  rw [h.vertexSet_eq]
  exact W.mk_vertexSet_le_of_mk_paths_le hkappa hcard

/-- Splitting a blueprint member at one imaginary edge preserves the
strong-edge infinitude condition.  A new ray component is necessarily a
tail of an old ray component. -/
theorem infinitelyManyStrongEdges (h : W.IsCutAt cut u)
    (hstrong : W.InfinitelyManyStrongEdges) :
    cut.InfinitelyManyStrongEdges := by
  intro r hrCut
  have hrEdgeOld : r.edgeSet ⊆ W.edgeSet := by
    intro e he
    apply h.edgeSet_subset
    exact Set.mem_iUnion.2 ⟨(.inr r : Path _),
      Set.mem_iUnion.2 ⟨hrCut, he⟩⟩
  have hr0Cut : r 0 ∈ cut.vertexSet :=
    ⟨(.inr r : Path _), hrCut, r.apply_mem_support 0⟩
  have hr0Old : r 0 ∈ W.vertexSet := by
    rw [← h.vertexSet_eq]
    exact hr0Cut
  obtain ⟨q, hqOld, hr0q⟩ := hr0Old
  have hrSupport : ∀ n : ℕ, r n ∈ q.support := by
    intro n
    induction n with
    | zero => exact hr0q
    | succ n ih =>
        have heOld := hrEdgeOld ⟨n, rfl⟩
        simp only [edgeSet, Set.mem_iUnion] at heOld
        obtain ⟨s, hsOld, hes⟩ := heOld
        have hrs : r n ∈ s.support :=
          (s.edgeSet_subset_support_prod hes).1
        have hsq : s = q :=
          W.path_eq_of_mem_support hsOld hqOld hrs ih
        subst s
        exact (q.edgeSet_subset_support_prod hes).2
  have hrEdgeQ : r.edgeSet ⊆ q.edgeSet := by
    rintro e ⟨n, rfl⟩
    have heOld := hrEdgeOld ⟨n, rfl⟩
    simp only [edgeSet, Set.mem_iUnion] at heOld
    obtain ⟨s, hsOld, hes⟩ := heOld
    have hrs : r n ∈ s.support :=
      (s.edgeSet_subset_support_prod hes).1
    have hsq : s = q :=
      W.path_eq_of_mem_support hsOld hqOld hrs (hrSupport n)
    exact hsq ▸ hes
  rcases q with f | s
  · exact False.elim <| Alternating.FinitePath.edgeSet_not_containsDirectedRay f
      ⟨⟨r, r.injective⟩, by
        rintro e ⟨n, rfl⟩
        exact hrEdgeQ ⟨n, rfl⟩⟩
  · obtain ⟨m, hm⟩ := hr0q
    have hreval : ∀ n : ℕ, r n = s (m + n) := by
      intro n
      induction n with
      | zero => simpa using hm.symm
      | succ n ih =>
          obtain ⟨j, hj⟩ := hrEdgeQ ⟨n, rfl⟩
          have hmj : m + n = j := s.injective <|
            ih.symm.trans (congrArg Prod.fst hj)
          calc
            r (n + 1) = s (j + 1) := congrArg Prod.snd hj
            _ = s ((m + n) + 1) := by rw [hmj]
            _ = s (m + (n + 1)) := by simp only [Nat.add_assoc]
    have hrequal : r = s.tail m := by
      apply Ray.ext
      funext n
      exact hreval n
    rw [hrequal]
    exact strongEdgeIndices.infinite_tail (hstrong s hqOld) m

/-- Cutting the one possible edge out of `u` creates no whole-blueprint
terminal other than `u`. -/
theorem terminalSet_subset_union_singleton (h : W.IsCutAt cut u) :
    cut.terminalSet ⊆ W.terminalSet ∪ {u} := by
  intro x hx
  rw [cut.terminalSet_eq_no_outgoing] at hx
  by_cases hxu : x = u
  · exact Or.inr (Set.mem_singleton_iff.2 hxu)
  · apply Or.inl
    rw [W.terminalSet_eq_no_outgoing]
    refine ⟨?_, ?_⟩
    · rw [← h.vertexSet_eq]
      exact hx.1
    · rintro ⟨y, hxy⟩
      exact hx.2 ⟨y, h.edge_mem_of_fst_ne hxu hxy⟩

end IsCutAt

namespace OldSliceDiamondAdvance

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {W : LinkageBlueprint Gamma C.selectedReference kappa}
variable {u : V} {P : OldSlice930IntervalTransaction C W u}
variable {hW : W.IsLinkageBlueprint C.oldSlice C.oldClosedSet C.persistent}

/-- Source-starting selected-reference components newly touched by the
scheduled front.  These are precisely the components which can disappear
from the retained-reference summand of blueprint source coverage. -/
def sourceReferenceMeetingFront : Set Gamma.DPath :=
  {p | p ∈ C.selectedReference ∧ p.initial ∈ Gamma.source ∧
    (p.support ∩ P.interval.front.support).Nonempty}

/-- Choose one literal front contact for every affected reference component.
The value is kept in the finite front support, not merely in the ambient
vertex type, so cardinality comparison is immediate. -/
noncomputable def sourceReferenceFrontContact
    (p : sourceReferenceMeetingFront (C := C) (P := P)) :
    P.interval.front.support :=
  ⟨Classical.choose p.property.2.2,
    (Classical.choose_spec p.property.2.2).2⟩

/-- Distinct reference components have distinct selected contacts because
the selected reference is a warp. -/
theorem sourceReferenceFrontContact_injective :
    Function.Injective
      (sourceReferenceFrontContact (C := C) (P := P)) := by
  intro p q hpq
  apply Subtype.ext
  apply Alternating.DWeb.IsWarp.eq_of_mem_support
    C.selectedReference_isWarp p.property.1 q.property.1
  · exact (Classical.choose_spec p.property.2.2).1
  · change
      (sourceReferenceFrontContact (C := C) (P := P) p).1 ∈ q.1.support
    rw [hpq]
    exact (Classical.choose_spec q.property.2.2).1

/-- Only `kappa`-many reference roots can be affected by a single scheduled
front.  In fact the family injects into the finite support of that front. -/
theorem mk_sourceReferenceMeetingFront_le :
    #(sourceReferenceMeetingFront (C := C) (P := P)) ≤ kappa := by
  refine (Cardinal.mk_le_of_injective
    sourceReferenceFrontContact_injective).trans ?_
  exact (Gamma.finitePath_support_finite P.interval.front).lt_aleph0.le.trans
    C.capacity_infinite

/-- Closing under the selected reference absorbs every affected component,
not merely its chosen contact.  This is the exact closure fact used by a
whole-family survivor to reintroduce the lost source roots. -/
theorem sourceReferenceMeetingFront_vertexSet_subset_closedSet :
    Gamma.vertexSet
        (sourceReferenceMeetingFront (C := C) (P := P)) ⊆
      P.closed.closedSet := by
  rintro x ⟨p, hp, hxp⟩
  obtain ⟨v, hvp, hvFront⟩ := hp.2.2
  have hpClosed : p.support ⊆ P.closed.closedSet :=
    P.closed.reference_closed p hp.1
      ⟨v, hvp, P.closed.front_support_subset hvFront⟩
  exact hpClosed hxp

/-- In particular all affected reference components remain inside the
selected later roof. -/
theorem sourceReferenceMeetingFront_vertexSet_subset_outerRoof :
    Gamma.vertexSet
        (sourceReferenceMeetingFront (C := C) (P := P)) ⊆ C.outerRoof :=
  sourceReferenceMeetingFront_vertexSet_subset_closedSet.trans
    P.closed.contained_in_roof

/-- The first diamond is roofed at the later frontier even though its
terminal boundary is still mixed. -/
theorem result_vertices_roofed (Q : OldSliceDiamondAdvance P hW) :
    Q.result.vertexSet ⊆ Gamma.roof C.newSlice := by
  rw [Q.result_vertexSet_eq]
  apply Set.union_subset
  · intro x hx
    apply Gamma.roof_cut (C.legal.frontierChronology C.old_lt_new)
    apply hW.vertices_roofed
    rw [← P.continuation.conclusion.isCutAt.vertexSet_eq]
    exact hx
  · exact P.interval.front_support_subset_outerRoof

/-- The dynamic closure selected for the joint 9.30--9.31 request contains
the complete first-diamond carrier. -/
theorem result_vertices_closed (Q : OldSliceDiamondAdvance P hW) :
    Q.result.vertexSet ⊆ P.closed.closedSet := by
  rw [Q.result_vertexSet_eq]
  apply Set.union_subset
  · intro x hx
    apply P.closed.seed_subset
    apply (PriorContact930Request.seed_subset_intervalSeed
      (PriorContact930Request.identity (C := C) (W := W) (u := u)
        P.old_mem) P.interval)
    apply (PriorContact930Request.contactSeed_subset
      (PriorContact930Request.identity (C := C) (W := W) (u := u)
        P.old_mem))
    apply continuation930ContactSeed.blueprint_subset C W
    rw [← P.continuation.conclusion.isCutAt.vertexSet_eq]
    exact hx
  · exact P.closed.front_support_subset

/-- Exact honest terminal boundary after one old-frontier transaction. -/
theorem result_terminalSet_subset_mixed
    (Q : OldSliceDiamondAdvance P hW) :
    Q.result.terminalSet ⊆
      W.terminalSet ∪ (C.oldSlice ∪ C.newSlice) := by
  intro x hx
  have hx' := terminalSet_diamond_subset
    P.cut Q.selectedPrefix Q.selectedPrefix_mem P.interval.front
      (P.interval.front_start.trans Q.selectedPrefix_finish.symm)
      (by simpa only [Q.selectedPrefix_finish] using Q.fresh) hx
  rcases hx' with hxCut | hxFinish
  · rcases P.continuation.conclusion.isCutAt.terminalSet_subset_union_singleton
        hxCut with hxOld | hxu
    · exact Or.inl hxOld
    · apply Or.inr
      apply Or.inl
      rw [Set.mem_singleton_iff] at hxu
      rw [hxu]
      exact P.old_mem
  · apply Or.inr
    apply Or.inr
    have hxeq : x = P.interval.front.finish := by
      simpa only [Set.mem_singleton_iff] using hxFinish
    rw [hxeq]
    exact P.interval.front_finish_mem

/-- Source coverage for the bare first diamond reduces to the exact missing
reference-contact provenance statement.  A retained reference component can
drop out only when it newly meets the appended front; all components still
disjoint from the result remain retained at the mixed frontier. -/
theorem result_covers_source_of_referenceFront
    (Q : OldSliceDiamondAdvance P hW)
    (hfront : ∀ p ∈ C.selectedReference,
      p.initial ∈ Gamma.source →
      (p.support ∩ P.interval.front.support).Nonempty →
      p.initial ∈ Q.result.initialSet) :
    Gamma.source ⊆
      Q.result.initialSet ∪
        Q.result.retainedReferenceInitials (C.oldSlice ∪ C.newSlice) := by
  intro x hxSource
  rcases hW.covers_source hxSource with hxInitial | hxRetained
  · apply Or.inl
    change x ∈ (P.cut.diamond Q.selectedPrefix Q.selectedPrefix_mem
      P.interval.front
      (P.interval.front_start.trans Q.selectedPrefix_finish.symm)
      (by simpa only [Q.selectedPrefix_finish] using Q.fresh)).initialSet
    rw [initialSet_diamond]
    exact P.continuation.conclusion.isCutAt.initialSet_mono hxInitial
  · obtain ⟨p, hpRetained, hpInitial⟩ := hxRetained
    by_cases hmeetResult : p ∈
        referencePathsMeeting C.selectedReference Q.result.vertexSet
    · apply Or.inl
      rw [← hpInitial]
      apply hfront p hpRetained.1.1
      · simpa only [hpInitial] using hxSource
      · obtain ⟨v, hvp, hvResult⟩ := hmeetResult.2
        rw [Q.result_vertexSet_eq] at hvResult
        rcases hvResult with hvCut | hvFront
        · exfalso
          apply hpRetained.2
          refine ⟨hpRetained.1.1, ⟨v, hvp, ?_⟩⟩
          rw [← P.continuation.conclusion.isCutAt.vertexSet_eq]
          exact hvCut
        · exact ⟨v, hvp, hvFront⟩
    · apply Or.inr
      refine ⟨p, ⟨⟨hpRetained.1.1, ?_⟩, hmeetResult⟩, hpInitial⟩
      obtain ⟨v, hvp, hvOld⟩ := hpRetained.1.2
      exact ⟨v, hvp, Or.inl hvOld⟩

/-- Exact obstruction for the bare first diamond.  If a reference component
is newly met by the front, but its initial is not an initial of the cut, then
that initial is absent from both parts of the mixed blueprint cover.  The
reference warp condition rules out a different component with the same
initial rescuing it. -/
theorem referenceFront_contact_obstructs_cover
    (Q : OldSliceDiamondAdvance P hW)
    (p : Gamma.DPath) (hp : p ∈ C.selectedReference)
    (hpFront : (p.support ∩ P.interval.front.support).Nonempty)
    (hpNotCutInitial : p.initial ∉ P.cut.initialSet) :
    p.initial ∉
      Q.result.initialSet ∪
        Q.result.retainedReferenceInitials (C.oldSlice ∪ C.newSlice) := by
  intro hcover
  rcases hcover with hinitial | hretained
  · apply hpNotCutInitial
    change p.initial ∈ (P.cut.diamond Q.selectedPrefix
      Q.selectedPrefix_mem P.interval.front
      (P.interval.front_start.trans Q.selectedPrefix_finish.symm)
      (by simpa only [Q.selectedPrefix_finish] using Q.fresh)).initialSet at hinitial
    rwa [initialSet_diamond] at hinitial
  · obtain ⟨q, hqRetained, hqInitial⟩ := hretained
    have hqp : q = p := by
      apply Alternating.DWeb.IsWarp.eq_of_mem_support
        C.selectedReference_isWarp
        hqRetained.1.1 hp
      · exact q.initial_mem_support
      · rw [hqInitial]
        exact p.initial_mem_support
    subst q
    apply hqRetained.2
    refine ⟨hp, ?_⟩
    obtain ⟨v, hvp, hvFront⟩ := hpFront
    refine ⟨v, hvp, ?_⟩
    rw [Q.result_vertexSet_eq]
    exact Or.inr hvFront

/-- In the source-starting case the preceding obstruction directly refutes
the mixed source-cover clause. -/
theorem not_result_covers_source_of_referenceFront_contact
    (Q : OldSliceDiamondAdvance P hW)
    (p : Gamma.DPath) (hp : p ∈ C.selectedReference)
    (hpSource : p.initial ∈ Gamma.source)
    (hpFront : (p.support ∩ P.interval.front.support).Nonempty)
    (hpNotCutInitial : p.initial ∉ P.cut.initialSet) :
    ¬ Gamma.source ⊆
      Q.result.initialSet ∪
        Q.result.retainedReferenceInitials (C.oldSlice ∪ C.newSlice) := by
  intro hcover
  exact Q.referenceFront_contact_obstructs_cover p hp hpFront hpNotCutInitial
    (hcover hpSource)

/-- Exact source-cover criterion for the bare scheduled diamond.

The old blueprint already covers every source.  Thus the only way coverage
can be lost is that the appended front newly meets a source-starting
reference component.  Such a component is no longer available on the
retained-reference side, so its initial vertex must be an actual root of the
cut (and hence, by `initialSet_diamond`, of the diamond result).  Conversely
that condition repairs every newly lost reference root. -/
theorem result_covers_source_iff_referenceFront
    (Q : OldSliceDiamondAdvance P hW) :
    (Gamma.source ⊆
        Q.result.initialSet ∪
          Q.result.retainedReferenceInitials (C.oldSlice ∪ C.newSlice)) ↔
      (∀ p ∈ C.selectedReference,
        p.initial ∈ Gamma.source →
        (p.support ∩ P.interval.front.support).Nonempty →
        p.initial ∈ P.cut.initialSet) := by
  constructor
  · intro hcover p hp hpSource hpFront
    by_contra hpNotCutInitial
    exact Q.not_result_covers_source_of_referenceFront_contact
      p hp hpSource hpFront hpNotCutInitial hcover
  · intro hfront
    apply Q.result_covers_source_of_referenceFront
    intro p hp hpSource hpFront
    change p.initial ∈
      (P.cut.diamond Q.selectedPrefix Q.selectedPrefix_mem
        P.interval.front
        (P.interval.front_start.trans Q.selectedPrefix_finish.symm)
        (by simpa only [Q.selectedPrefix_finish] using Q.fresh)).initialSet
    rw [initialSet_diamond]
    exact hfront p hp hpSource hpFront

/-- Compile the structural first-diamond facts into the exact mixed state.
The sole remaining premise is retained-source coverage after the new carrier
is inserted.  Strong-edge infinitude for a ray component created by cutting
one imaginary edge is derived above by identifying it with an old ray tail. -/
theorem isMixedFrontierBlueprint
    (Q : OldSliceDiamondAdvance P hW)
    (hcover : Gamma.source ⊆
      Q.result.initialSet ∪
        Q.result.retainedReferenceInitials (C.oldSlice ∪ C.newSlice)) :
    Q.result.IsMixedFrontierBlueprint P.closed.closedSet := by
  refine {
    vertices_roofed := Q.result_vertices_roofed
    covers_source := hcover
    vertices_closed := Q.result_vertices_closed
    card_paths := ?_
    infinitely_many_strong := ?_
    terminals_mixed := ?_ }
  · exact mk_diamond_paths_le_of_infinite
      P.cut Q.selectedPrefix Q.selectedPrefix_mem P.interval.front
        (P.interval.front_start.trans Q.selectedPrefix_finish.symm)
        (by simpa only [Q.selectedPrefix_finish] using Q.fresh)
        C.capacity_infinite
        (P.continuation.conclusion.isCutAt.card_paths_le
          C.capacity_infinite hW.card_paths)
  · exact infinitelyManyStrongEdges_diamond
      P.cut Q.selectedPrefix Q.selectedPrefix_mem P.interval.front
        (P.interval.front_start.trans Q.selectedPrefix_finish.symm)
        (by simpa only [Q.selectedPrefix_finish] using Q.fresh)
        (P.continuation.conclusion.isCutAt.infinitelyManyStrongEdges
          hW.infinitely_many_strong)
  · intro x hx
    rcases Q.result_terminalSet_subset_mixed hx with hxW | hxBoundary
    · rcases hW.terminals_popular hxW with hxPopular | hxOld
      · exact Or.inl hxPopular
      · exact Or.inr (Or.inl hxOld)
    · exact Or.inr hxBoundary

/-- Provenance-facing form of the mixed-state compiler. -/
theorem isMixedFrontierBlueprint_of_referenceFront
    (Q : OldSliceDiamondAdvance P hW)
    (hfront : ∀ p ∈ C.selectedReference,
      p.initial ∈ Gamma.source →
      (p.support ∩ P.interval.front.support).Nonempty →
      p.initial ∈ Q.result.initialSet) :
    Q.result.IsMixedFrontierBlueprint P.closed.closedSet :=
  Q.isMixedFrontierBlueprint
    (Q.result_covers_source_of_referenceFront hfront)

end OldSliceDiamondAdvance

#print axioms IsCutAt.infinitelyManyStrongEdges
#print axioms OldSliceDiamondAdvance.mk_sourceReferenceMeetingFront_le
#print axioms
  OldSliceDiamondAdvance.sourceReferenceMeetingFront_vertexSet_subset_closedSet
#print axioms OldSliceDiamondAdvance.isMixedFrontierBlueprint
#print axioms OldSliceDiamondAdvance.isMixedFrontierBlueprint_of_referenceFront
#print axioms OldSliceDiamondAdvance.result_covers_source_iff_referenceFront

end LinkageBlueprint
end Blueprint
end Erdos599
