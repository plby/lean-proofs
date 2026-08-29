/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularMatrixScratch
import ErdosProblems.Erdos599.SingularContinuation
import ErdosProblems.Erdos599.SliceHalfwayCore
import ErdosProblems.Erdos599.RegularNormalization
import ErdosProblems.Erdos599.SafeLinkBridge
import ErdosProblems.Erdos599.SafeLink

/-!
# The singular extension step

This module packages all cardinal and competitor bookkeeping for the
singular branch.  `SingularRows` is the remaining graph-theoretic content
of Assertion 9.17: coherent half-way rows for the recursively closed source
sets.  Once such rows are supplied, the exact extension clause follows from
the least-column construction in `ExtensionClause`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

universe u

namespace SingularExtension

open SingularMatrix

variable {V : Type u}

/-- An ordinary finite linkage to the target supplies the stronger
source-faithful `LinksToTarget` witness used by the matrix. -/
theorem linksToTarget_of_linkageToTarget
    {G : DWeb V} {A : Set V} {W : Set G.DPath}
    (hW : IsLinkageBetween G A G.target W) :
    LinksToTarget G W A := by
  intro a ha
  have haInitial : a ∈ G.initialSet W := hW.initialSet_eq.symm ▸ ha
  obtain ⟨p, hpW, hpInitial⟩ := haInitial
  obtain ⟨q, hq⟩ := hW.finiteCharacter hpW
  subst p
  have hstart : q.start = a := hpInitial
  subst a
  obtain ⟨r, hr, _hends, hsource⟩ := hW.endpointPure (.inl q) hpW
  have hrq : q = r := by simpa using hr
  subst r
  have hfinishTarget : q.finish ∈ G.target := by
    apply hW.terminalFrontier_subset
    exact ⟨.inl q, hpW, rfl⟩
  refine ⟨.inl q, hpW, q, rfl, ?_, ?_⟩
  · exact hsource
  · refine ⟨[], q.walk.support.tail, ?_, q.finish, hfinishTarget, ?_⟩
    · simp only [List.nil_append]
      calc
        q.walk.support =
            q.walk.support.head q.walk.support_ne_nil ::
              q.walk.support.tail :=
          (q.walk.support.cons_head_tail q.walk.support_ne_nil).symm
        _ = q.start :: q.walk.support.tail := by
          rw [q.walk.head_support]
    · have hfinishSupport : q.finish ∈ q.walk.support :=
        q.finish_mem_support
      have hcons : q.start :: q.walk.support.tail = q.walk.support := by
        calc
          q.start :: q.walk.support.tail =
              q.walk.support.head q.walk.support_ne_nil ::
                q.walk.support.tail := by rw [q.walk.head_support]
          _ = q.walk.support :=
            q.walk.support.cons_head_tail q.walk.support_ne_nil
      change q.finish ∈ q.start :: q.walk.support.tail
      rw [hcons]
      exact hfinishSupport

/-- Every strictly smaller source subset of a normalized unhindered web is
linkable by the universal lower-cardinal induction hypothesis.  This is the
constructive source of provisional target rows in the inner closing-up
iteration. -/
theorem exists_smallSourceLinkage_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (G : DWeb V) (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) (hcard : #A < kappa) :
    ∃ W : Set G.DPath, IsLinkageBetween G A G.target W := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro u v huv hv
    exact (hNorm huv).1 hv
  have hsubUnhindered : (G.sourceSubweb A).IsUnhindered :=
    hG.sourceSubweb G hNoEnter hA
  have hlinkable : IsLinkable (G.sourceSubweb A) :=
    linkable_of_cardinalInductionAt_source (G.sourceSubweb A)
      (hlower #A hcard (G.sourceSubweb A) hsubUnhindered)
  obtain ⟨W, hW⟩ := hlinkable
  change IsLinkageBetween G A G.target W at hW
  exact ⟨W, hW⟩

/-- Provisional row furnished by the lower induction hypothesis.  The
designated small source set is linked to the target, while every other
source is represented by its trivial path.  Normalization makes the two
families disjoint.  This theorem discharges existence of each individual
row; compatibility between different provisional rows is the separate
fixed-point obligation represented by `TargetRows.forward`. -/
theorem exists_provisionalTargetRow_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (G : DWeb V) (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) (hcard : #A < kappa) :
    ∃ W : Set G.DPath,
      G.IsWarp W ∧ G.HasFiniteCharacter W ∧
      G.initialSet W = G.source ∧ LinksToTarget G W A := by
  obtain ⟨P, hP⟩ :=
    exists_smallSourceLinkage_of_lower hlower G hG hNorm hA hcard
  let R : Set G.DPath := G.trivialPath '' (G.source \ A)
  let W : Set G.DPath := P ∪ R
  have hcross : ∀ p ∈ P, ∀ q ∈ R, p ≠ q →
      Disjoint p.support q.support := by
    intro p hp q hq _hpq
    obtain ⟨x, hx, rfl⟩ := hq
    rw [G.support_trivialPath]
    apply Set.disjoint_singleton_right.2
    intro hxp
    have hxInitial : x = p.initial :=
      hNorm.eq_initial_of_mem_path p hxp hx.1
    have hpInitial : p.initial ∈ A := by
      rw [← hP.initialSet_eq]
      exact ⟨p, hp, rfl⟩
    exact hx.2 (hxInitial.symm ▸ hpInitial)
  have hwarp : G.IsWarp W := by
    apply Set.PairwiseDisjoint.union hP.isWarp
      (G.isWarp_trivialPaths (G.source \ A))
    exact hcross
  have hRfinite : G.HasFiniteCharacter R := by
    rintro p ⟨x, _hx, rfl⟩
    exact ⟨DirectedPath.FinitePath.trivial G.graph x, rfl⟩
  have hfinite : G.HasFiniteCharacter W :=
    SingularContinuation.finiteCharacter_union G hP.finiteCharacter hRfinite
  have hinitial : G.initialSet W = G.source := by
    change G.initialSet (P ∪ (G.trivialPath '' (G.source \ A))) = G.source
    rw [G.initialSet_union, G.initialSet_trivialPaths, hP.initialSet_eq,
      Set.union_comm, Set.sdiff_union_of_subset hA]
  have hlinksP : LinksToTarget G P A := linksToTarget_of_linkageToTarget hP
  have hlinks : LinksToTarget G W A := by
    intro a ha
    obtain ⟨p, hp, hpa⟩ := hlinksP a ha
    exact ⟨p, Or.inl hp, hpa⟩
  exact ⟨W, hwarp, hfinite, hinitial, hlinks⟩

/-! ## The canonical completed/pending split -/

/-- Members of a row which have already reached the ambient target.  In a
normalized web these paths cannot be extended any further, so they are the
precise frozen part of the singular successor construction. -/
def completedPart (G : DWeb V) (W : Set G.DPath) : Set G.DPath :=
  {p | p ∈ W ∧ ∃ b ∈ G.target, G.terminal? p = some b}

/-- Members of a row which have not yet reached the ambient target. -/
def pendingPart (G : DWeb V) (W : Set G.DPath) : Set G.DPath :=
  W \ completedPart G W

theorem completedPart_union_pendingPart (G : DWeb V) (W : Set G.DPath) :
    completedPart G W ∪ pendingPart G W = W := by
  ext p
  simp only [completedPart, pendingPart, Set.mem_union, Set.mem_ofPred_eq,
    Set.mem_sdiff]
  tauto

theorem disjoint_completedPart_pendingPart (G : DWeb V)
    (W : Set G.DPath) :
    Disjoint (completedPart G W) (pendingPart G W) := by
  exact Set.disjoint_sdiff_right

theorem isTrimmedSeparator_mono {G : DWeb V} {C D : Set V}
    (hC : IsTrimmedSeparator G C) (hDC : D ⊆ C) :
    IsTrimmedSeparator G D := by
  apply Set.Subset.antisymm
  · exact G.essential_subset D
  · intro x hxD
    have hxC : x ∈ G.essential C := hC.symm ▸ hDC hxD
    rw [G.mem_essential_iff] at hxC ⊢
    refine ⟨hxD, ?_⟩
    intro hxRoof
    have hsub : D \ {x} ⊆ C \ {x} := by
      intro y hy
      exact ⟨hDC hy.1, hy.2⟩
    exact hxC.2 (G.roof_mono hsub hxRoof)

/-- In a normalized web every point of a trimmed set remains essential
after adjoining the source set.  Equivalently, it is exposed as a source
of the quotient.  No disjointness between the source and the trimmed set
is needed. -/
theorem trimmed_subset_quotient_source_of_normalized
    {G : DWeb V} (hNorm : G.IsNormalized) {C : Set V}
    (hC : IsTrimmedSeparator G C) :
    C ⊆ (G.quotient C).source := by
  intro x hxC
  rw [G.quotient_source, G.mem_essential_iff]
  refine ⟨Or.inr hxC, ?_⟩
  have hxEssential : x ∈ G.essential C := hC.symm ▸ hxC
  rw [G.mem_essential_iff] at hxEssential
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (G.not_mem_roof_iff (C \ {x}) x).1 hxEssential.2
  apply (G.not_mem_roof_iff ((G.source ∪ C) \ {x}) x).2
  refine ⟨p, hpTarget, ?_⟩
  apply Set.disjoint_left.2
  intro y hyp hy
  rcases hy.1 with hySource | hyC
  · exact hy.2 (hNorm.eq_start_of_mem_walk p.walk hyp hySource |>.trans
      hpTarget.1)
  · exact Set.disjoint_left.1 hpAvoid hyp ⟨hyC, hy.2⟩

theorem pendingPart_terminalFrontier_subset
    (G : DWeb V) (W : Set G.DPath) :
    G.terminalFrontier (pendingPart G W) ⊆
      G.terminalFrontier W \ G.target := by
  rintro b ⟨p, hpPending, hpb⟩
  refine ⟨⟨p, hpPending.1, hpb⟩, ?_⟩
  intro hbTarget
  exact hpPending.2 ⟨hpPending.1, b, hbTarget, hpb⟩

/-- In a normalized web every component witnessing `LinksToTarget` is in
the completed part.  Thus freezing all completed members preserves all
target links already established at the current row. -/
theorem linksToTarget_completedPart
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {A : Set V}
    (hlinks : LinksToTarget G W A) :
    LinksToTarget G (completedPart G W) A := by
  intro a ha
  obtain ⟨p, hpW, q, rfl, hpure, hsuffix⟩ := hlinks a ha
  obtain ⟨before, after, hsupport, b, hbTarget, hbAfter⟩ := hsuffix
  have hbSupport : b ∈ q.support := by
    change b ∈ q.walk.support
    rw [hsupport]
    exact List.mem_append_right before hbAfter
  have hterminal : G.terminal? (.inl q : G.DPath) = some b :=
    hNorm.terminal?_eq_of_mem_path (.inl q) hbSupport hbTarget
  exact ⟨.inl q, ⟨hpW, b, hbTarget, hterminal⟩,
    q, rfl, hpure, ⟨before, after, hsupport, b, hbTarget, hbAfter⟩⟩

/-- The pending frontier of a weak halfway stopover is itself trimmed.
This is one of the structural inputs to the checked pending-continuation
splice and follows without any false source-separation assumption. -/
theorem pendingPart_frontier_isTrimmed
    {G : DWeb V} {W : Set G.DPath} {C : Set V}
    (hstop : IsHalfwayStopover G W C) :
    IsTrimmedSeparator G (G.terminalFrontier (pendingPart G W)) := by
  apply isTrimmedSeparator_mono hstop.minimal
  exact (pendingPart_terminalFrontier_subset G W).trans
    (Set.sdiff_subset.trans hstop.linkage.terminalFrontier_subset)

/-- A warp is automatically terminal-clean at its own frontier: a point
which is a terminal of one member cannot lie on a distinct member. -/
theorem terminalCleanAt_terminalFrontier_of_isWarp
    {G : DWeb V} {W : Set G.DPath} (hW : G.IsWarp W) :
    SingularContinuation.TerminalCleanAt G W (G.terminalFrontier W) := by
  intro p hpW x hxp hxFrontier
  obtain ⟨q, hqW, hqx⟩ := hxFrontier
  have hpq : p = q := by
    by_contra hpq
    exact Set.disjoint_left.1 (hW hpW hqW hpq) hxp
      (G.terminal_mem_support hqx)
  subst q
  exact hqx

/-- The pending frontier is exposed by quotienting in the normalized web.
Together with `terminalCleanAt_terminalFrontier_of_isWarp` and hereditary
trimmedness, this discharges three of the four geometric premises of the
pending-continuation splice. -/
theorem pendingPart_frontier_subset_quotientSource
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C : Set V}
    (hstop : IsHalfwayStopover G W C) :
    G.terminalFrontier (pendingPart G W) ⊆
      (G.quotient (G.terminalFrontier (pendingPart G W))).source :=
  trimmed_subset_quotient_source_of_normalized hNorm
    (pendingPart_frontier_isTrimmed hstop)

/-- In a normalized web target links are monotone under finite-character
forward extension.  The old finite target point remains on the extending
component, and normalization prevents the extension from visiting a
second source vertex. -/
theorem linksToTarget_of_forwardExtension
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W W' : Set G.DPath} {A : Set V}
    (hA : A ⊆ G.source)
    (hlinks : LinksToTarget G W A)
    (hforward : G.ForwardExtension W W')
    (hfinite : G.HasFiniteCharacter W') :
    LinksToTarget G W' A := by
  intro a ha
  obtain ⟨p, hpW, q, hpq, hpure, before, after, hsupport,
    b, hbTarget, hbAfter⟩ := hlinks a ha
  obtain ⟨r, hrW', hpr⟩ := hforward.1 p hpW
  obtain ⟨f, hrf⟩ := hfinite hrW'
  subst r
  have hpq' : p = (.inl q : G.DPath) := hpq
  subst p
  have haSupport : a ∈ q.support := by
    change a ∈ q.walk.support
    rw [hsupport]
    exact List.mem_append_right before (by simp)
  have hqStart : q.start = a := by
    exact (hNorm.eq_initial_of_mem_path (.inl q) haSupport (hA ha)).symm
  have hfStart : f.start = a := by
    calc
      f.start = q.start := (G.extends_initial hpr).symm
      _ = a := hqStart
  have hfPure : f.support ∩ A = {a} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxStart : x = f.start :=
        hNorm.eq_initial_of_mem_path (.inl f) hx.1 (hA hx.2)
      exact Set.mem_singleton_iff.2 (hxStart.trans hfStart)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨by simpa only [hfStart] using f.start_mem_support, ha⟩
  have hbq : b ∈ q.support := by
    change b ∈ q.walk.support
    rw [hsupport]
    exact List.mem_append_right before hbAfter
  have hbf : b ∈ f.support := G.support_mono_of_extends hpr hbq
  have hterminal : G.terminal? (.inl f : G.DPath) = some b :=
    hNorm.terminal?_eq_of_mem_path (.inl f) hbf hbTarget
  have hfFinish : f.finish = b := Option.some.inj hterminal
  refine ⟨.inl f, hrW', f, rfl, hfPure, ?_⟩
  refine ⟨[], f.walk.support.tail, ?_, b, hbTarget, ?_⟩
  · simp only [List.nil_append]
    calc
      f.walk.support =
          f.walk.support.head f.walk.support_ne_nil ::
            f.walk.support.tail :=
        (f.walk.support.cons_head_tail f.walk.support_ne_nil).symm
      _ = a :: f.walk.support.tail := by
        exact congrArg (fun x ↦ x :: f.walk.support.tail)
          (f.walk.head_support.trans hfStart)
  · have hbFinish : b = f.finish := hfFinish.symm
    subst b
    have hcons : a :: f.walk.support.tail = f.walk.support := by
      calc
        a :: f.walk.support.tail =
            f.walk.support.head f.walk.support_ne_nil ::
              f.walk.support.tail := by
          exact congrArg (fun x ↦ x :: f.walk.support.tail)
            (hfStart.symm.trans f.walk.head_support.symm)
        _ = f.walk.support :=
          f.walk.support.cons_head_tail f.walk.support_ne_nil
    change f.finish ∈ a :: f.walk.support.tail
    rw [hcons]
    exact f.finish_mem_support

/-! ## Deleting an arbitrary set of sources

The singular successor freezes a (possibly infinite) collection of
components which have already reached the target.  In the quotient by the
current stop-over, every contact of those frozen components which survives
the strict-roof deletion is a source.  Thus the residual web is obtained by
deleting a set of sources, not merely one source.  The one-point version is
used in the safe-link construction; the following simultaneous version is
what the singular construction needs. -/

/-- Deleting any collection of source vertices from an unhindered web
preserves unhinderedness.  A hindrance after deletion lifts to the ambient
web, and adjoining the trivial paths at all deleted sources turns it into an
ambient hindrance. -/
theorem delete_sourceSet_isUnhindered
    (G : DWeb V) (hG : G.IsUnhindered) {Q : Set V}
    (hQ : Q ⊆ G.source) :
    (G.delete Q).IsUnhindered := by
  rw [(G.delete Q).isUnhindered_iff]
  intro W hW
  let L : Set G.DPath := G.liftDeleteFamily Q W
  let T : Set G.DPath := G.trivialPath '' Q
  let R : Set G.DPath := T ∪ L
  have hLavoid : Disjoint (G.vertexSet L) Q := by
    exact G.vertexSet_liftDeleteFamily_disjoint hW.2.1
  have hLwarp : G.IsWarp L := hW.1.liftDeleteFamily
  have hTwarp : G.IsWarp T := G.isWarp_trivialPaths Q
  have hcross : ∀ p ∈ T, ∀ q ∈ L, p ≠ q →
      Disjoint p.support q.support := by
    rintro p ⟨a, haQ, rfl⟩ q hqL _hpq
    rw [G.support_trivialPath]
    apply Set.disjoint_singleton_left.2
    intro haq
    exact Set.disjoint_left.1 hLavoid
      ⟨q, hqL, haq⟩ haQ
  have hRwarp : G.IsWarp R := by
    apply Set.PairwiseDisjoint.union hTwarp hLwarp
    exact hcross
  have hRinitial :
      G.initialSet R = Q ∪ (G.delete Q).initialSet W := by
    change G.initialSet (G.trivialPath '' Q ∪ L) = _
    rw [G.initialSet_union, G.initialSet_trivialPaths,
      G.initialSet_liftDeleteFamily]
  have hRstart : G.initialSet R ⊆ G.source := by
    rw [hRinitial]
    exact Set.union_subset hQ (hW.2.1.trans Set.sdiff_subset)
  have hQFrontier : Q ⊆ G.terminalFrontier R := by
    intro a haQ
    refine ⟨G.trivialPath a, Or.inl ⟨a, haQ, rfl⟩, ?_⟩
    exact G.terminal?_trivialPath a
  have hRseparates : G.source ⊆ G.roof (G.terminalFrontier R) := by
    intro b hb p hp
    by_cases hpmeets : (p.support ∩ Q).Nonempty
    · obtain ⟨x, hxp, hxQ⟩ := hpmeets
      exact ⟨x, hxp, hQFrontier hxQ⟩
    · have havoid : SafeLink.Walk.Avoids p.walk Q := by
        intro x hxp hxQ
        exact hpmeets ⟨x, hxp, hxQ⟩
      let q : DirectedPath.FinitePath (G.delete Q).graph :=
        SafeLink.FinitePath.toDelete G Q p havoid
      have hbDelete : b ∈ (G.delete Q).source := by
        exact ⟨hb, havoid b (hp.1 ▸ p.walk.start_mem_support)⟩
      have hpfinishDelete : p.finish ∈ (G.delete Q).target := by
        exact ⟨hp.2, havoid p.finish p.walk.end_mem_support⟩
      obtain ⟨x, hxq, hxFrontier⟩ :=
        hW.2.2 hbDelete q
          ⟨by simpa [q] using hp.1, by simpa [q] using hpfinishDelete⟩
      obtain ⟨r, hrW, hrterm⟩ := hxFrontier
      have hxSupport : x ∈ p.support := by
        simpa [q] using hxq
      have hxR : x ∈ G.terminalFrontier R := by
        refine ⟨G.liftDeletePath Q r, Or.inr ⟨r, hrW, rfl⟩, ?_⟩
        simpa using hrterm
      exact ⟨x, hxSupport, hxR⟩
  have hReq : G.initialSet R = G.source :=
    (G.isUnhindered_iff.mp hG) R ⟨hRwarp, hRstart, hRseparates⟩
  apply Set.Subset.antisymm hW.2.1
  intro x hx
  have hxNotQ : x ∉ Q := hx.2
  have hxR : x ∈ G.initialSet R := by
    rw [hReq]
    exact hx.1
  rw [hRinitial] at hxR
  exact hxR.resolve_left hxNotQ

/-- Quotienting a normalized web preserves normalization.  The quotient
edge relation explicitly forbids entry into the commitment set, while an
essential quotient source belongs to the old source or that commitment
set. -/
theorem DWeb.IsNormalized.quotient
    {G : DWeb V} (hG : G.IsNormalized) (C : Set V) :
    (G.quotient C).IsNormalized := by
  intro x y hxy
  refine ⟨?_, ?_⟩
  · intro hySource
    rcases hySource.1 with hyOld | hyC
    · exact (hG hxy.1).1 hyOld
    · exact hxy.2.2.2 hyC
  · intro hxTarget
    exact (hG hxy.1).2 hxTarget

/-- Vertex deletion also preserves normalization. -/
theorem DWeb.IsNormalized.delete
    {G : DWeb V} (hG : G.IsNormalized) (Q : Set V) :
    (G.delete Q).IsNormalized := by
  intro x y hxy
  exact ⟨fun hySource ↦ (hG hxy.1).1 hySource.1,
    fun hxTarget ↦ (hG hxy.1).2 hxTarget.1⟩

/-- Enlarge a small request to a prescribed infinite cardinal inside an
ambient set.  This is the padding operation used before invoking a lower
half-way clause, whose designated source cardinal is stated by equality. -/
theorem exists_enlargement_of_mk_le
    {A U : Set V} {rho : Cardinal.{u}}
    (hU : U ⊆ A) (hUcard : #U ≤ rho) (hrho : aleph0 ≤ rho)
    (hrhoA : rho ≤ #A) :
    ∃ U' : Set V, U ⊆ U' ∧ U' ⊆ A ∧ #U' = rho := by
  obtain ⟨C, hCA, hCcard⟩ :=
    Cardinal.le_mk_iff_exists_subset.mp hrhoA
  refine ⟨U ∪ C, Set.subset_union_left, Set.union_subset hU hCA, ?_⟩
  apply le_antisymm
  · exact (Cardinal.mk_union_le U C).trans
      (Cardinal.add_le_of_le hrho hUcard hCcard.le)
  · rw [← hCcard]
    exact Cardinal.mk_subtype_mono Set.subset_union_right

/-! ## Safe transport through a frozen deletion

The successor construction chooses the new quotient family only after the
already completed paths have been frozen and deleted.  Deletion followed by
quotient is not equal to quotient followed by deletion, but every edge in the
former is an edge in the latter.  The following explicit image construction
uses that one valid direction and then restores the deleted vertices.  Its
main point is the last theorem: the transported family still avoids the
frozen vertex set after it is lifted from the quotient to the ambient web. -/

/-- Regard a family in `(G - Q) / C` as a family in `G / C`, by first
transporting it to `(G / C) - Q` and then restoring the deleted vertices. -/
def deletedQuotientFamily (G : DWeb V) (C Q : Set V)
    (U : Set ((G.delete Q).quotient C).DPath) :
    Set (G.quotient C).DPath :=
  (G.quotient C).liftDeleteFamily Q
    (G.liftDeleteQuotientPathToQuotientDelete C Q '' U)

theorem isWarp_mapDeleteQuotientFamily
    {G : DWeb V} {C Q : Set V}
    {U : Set ((G.delete Q).quotient C).DPath}
    (hU : ((G.delete Q).quotient C).IsWarp U) :
    ((G.quotient C).delete Q).IsWarp
      (G.liftDeleteQuotientPathToQuotientDelete C Q '' U) := by
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  change Disjoint
    (G.liftDeleteQuotientPathToQuotientDelete C Q p₀).support
    (G.liftDeleteQuotientPathToQuotientDelete C Q q₀).support
  rw [G.support_liftDeleteQuotientPathToQuotientDelete,
    G.support_liftDeleteQuotientPathToQuotientDelete]
  apply hU hp₀ hq₀
  intro hp₀q₀
  subst q₀
  exact hpq rfl

theorem initialSet_mapDeleteQuotientFamily_subset
    {G : DWeb V} {C Q : Set V}
    {U : Set ((G.delete Q).quotient C).DPath}
    (hstart : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source) :
    ((G.quotient C).delete Q).initialSet
        (G.liftDeleteQuotientPathToQuotientDelete C Q '' U) ⊆
      ((G.quotient C).delete Q).source := by
  rintro x ⟨p, ⟨q, hqU, rfl⟩, hpx⟩
  apply G.deleteQuotient_source_subset_quotientDelete_source C Q
  apply hstart
  refine ⟨q, hqU, ?_⟩
  simpa using hpx

theorem deletedQuotientFamily_isWarp
    {G : DWeb V} {C Q : Set V}
    {U : Set ((G.delete Q).quotient C).DPath}
    (hU : ((G.delete Q).quotient C).IsWarp U) :
    (G.quotient C).IsWarp (deletedQuotientFamily G C Q U) := by
  exact (isWarp_mapDeleteQuotientFamily hU).liftDeleteFamily

theorem deletedQuotientFamily_hasFiniteCharacter
    {G : DWeb V} {C Q : Set V}
    {U : Set ((G.delete Q).quotient C).DPath}
    (hU : ((G.delete Q).quotient C).HasFiniteCharacter U) :
    (G.quotient C).HasFiniteCharacter (deletedQuotientFamily G C Q U) := by
  apply DWeb.fd_hasFiniteCharacter_liftDeleteFamily
  rintro _ ⟨p, hpU, rfl⟩
  obtain ⟨q, rfl⟩ := hU hpU
  exact ⟨q.lift (fun {_ _} e ↦
    G.deleteQuotient_adj_imp_quotientDelete C Q e), rfl⟩

theorem deletedQuotientFamily_initialSet
    (G : DWeb V) (C Q : Set V)
    (U : Set ((G.delete Q).quotient C).DPath) :
    (G.quotient C).initialSet (deletedQuotientFamily G C Q U) =
      ((G.delete Q).quotient C).initialSet U := by
  rw [deletedQuotientFamily, (G.quotient C).initialSet_liftDeleteFamily]
  ext x
  constructor
  · rintro ⟨p, ⟨q, hqU, rfl⟩, hpx⟩
    exact ⟨q, hqU, by simpa using hpx⟩
  · rintro ⟨q, hqU, hqx⟩
    exact ⟨G.liftDeleteQuotientPathToQuotientDelete C Q q,
      ⟨q, hqU, rfl⟩, by simpa using hqx⟩

/-- Transporting a family from deletion-then-quotient to the ordinary
quotient preserves every source-faithful target link.  Both path lifts keep
the underlying support list, while the deleted target is contained in the
ambient target. -/
theorem linksToTarget_deletedQuotientFamily
    {G : DWeb V} {C Q A : Set V}
    {U : Set ((G.delete Q).quotient C).DPath}
    (hU : LinksToTarget ((G.delete Q).quotient C) U A) :
    LinksToTarget (G.quotient C) (deletedQuotientFamily G C Q U) A := by
  intro a ha
  obtain ⟨p, hpU, q, hpq, hsource, before, after, hsupport,
      b, hbTarget, hbAfter⟩ := hU a ha
  subst p
  let q₁ : DirectedPath.FinitePath ((G.quotient C).delete Q).graph :=
    q.lift (fun {_ _} e ↦
      G.deleteQuotient_adj_imp_quotientDelete C Q e)
  let q₂ : DirectedPath.FinitePath (G.quotient C).graph :=
    q₁.lift (fun {_ _} e ↦ (G.quotient C).delete_adj_imp e)
  have hq₂mem : (.inl q₂ : (G.quotient C).DPath) ∈
      deletedQuotientFamily G C Q U := by
    refine ⟨(.inl q₁ : ((G.quotient C).delete Q).DPath), ?_, rfl⟩
    exact ⟨(.inl q : ((G.delete Q).quotient C).DPath), hpU, rfl⟩
  refine ⟨.inl q₂, hq₂mem, q₂, rfl, ?_,
    before, after, ?_, b, hbTarget.1, hbAfter⟩
  · simpa only [q₂, q₁, DirectedPath.FinitePath.support_lift] using hsource
  · simpa [q₂, q₁, DirectedPath.FinitePath.lift] using hsupport

theorem deletedQuotientFamily_vertexSet_disjoint
    {G : DWeb V} {C Q : Set V}
    {U : Set ((G.delete Q).quotient C).DPath}
    (hstart : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source) :
    Disjoint
      ((G.quotient C).vertexSet (deletedQuotientFamily G C Q U)) Q := by
  apply (G.quotient C).vertexSet_liftDeleteFamily_disjoint
  exact initialSet_mapDeleteQuotientFamily_subset hstart

/-- Restoring a deletion inside the quotient and then lifting the quotient
to `G` still cannot introduce a frozen vertex: both path transports preserve
support exactly. -/
theorem lift_deletedQuotientFamily_vertexSet_disjoint
    {G : DWeb V} {C Q : Set V}
    {U : Set ((G.delete Q).quotient C).DPath}
    (hstart : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source) :
    Disjoint
      (G.vertexSet
        (G.liftQuotientFamily C (deletedQuotientFamily G C Q U))) Q := by
  rw [Set.disjoint_left]
  intro x hx hxQ
  obtain ⟨p, ⟨q, hq, rfl⟩, hxp⟩ := hx
  exact Set.disjoint_left.1
    (deletedQuotientFamily_vertexSet_disjoint hstart)
    ⟨q, hq, by simpa using hxp⟩ hxQ

/-- The exact row data consumed by Assertion 9.18.  In particular, the
matrix-limit argument does not use the stop-over or altitude attached to a
half-way linkage: it uses only a full finite-character warp, one finite
target segment for every currently designated source, and forward
coherence down each column.  Keeping this smaller interface explicit makes
the remaining selection problem in Assertion 9.17 precise. -/
structure TargetRows (G : DWeb V) (fixed : Set G.DPath)
    (A₀ : Set V) (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hcard : #A₀ = kappa) where
  paths : Index kappa → ℕ → Set G.DPath
  isWarp : ∀ i n, G.IsWarp (paths i n)
  finiteCharacter : ∀ i n, G.HasFiniteCharacter (paths i n)
  initialSet : ∀ i n, G.initialSet (paths i n) = G.source
  targetSegment : ∀ i n a,
    a ∈ matrixSources G fixed paths
      (sourceLayer A₀ kappa hcard huncountable hsingular) i n →
    Nonempty (G.TargetSegment (paths i n)
      (matrixSources G fixed paths
        (sourceLayer A₀ kappa hcard huncountable hsingular) i n) a)
  forward : ∀ i n,
    G.ForwardExtension (paths i n) (paths i (n + 1))

/-- One simultaneous horizontal row before it is inserted into the
`Index kappa × omega` matrix. -/
structure TargetRowStage (G : DWeb V) (I : Type u) where
  sources : I → Set V
  paths : I → Set G.DPath
  isWarp : ∀ i, G.IsWarp (paths i)
  finiteCharacter : ∀ i, G.HasFiniteCharacter (paths i)
  initialSet : ∀ i, G.initialSet (paths i) = G.source
  links : ∀ i, LinksToTarget G (paths i) (sources i)

/-- The data furnished by the public (weak) half-way clause, with the
chosen stop-over retained.  This is useful bookkeeping, but is deliberately
*not* called a future-proof certificate: `IsHalfwayStopover` does not say
that its stop-over separates the current source, so it cannot justify the
quotient continuation in Assertion 9.17. -/
structure WeakHalfwayTargetRowStage (G : DWeb V) (I : Type u) where
  row : TargetRowStage G I
  stopover : I → Set V
  halfway : ∀ i, IsHalfwayStopover G (row.paths i) (stopover i)

/-- A simultaneous row carrying the strengthened singular certificate in
every column.  Forgetting it yields exactly the row consumed by the matrix. -/
structure CertifiedTargetRowStage (G : DWeb V) (I : Type u)
    (rho : I → Cardinal.{u}) where
  row : TargetRowStage G I
  stopover : I → Set V
  separating : ∀ i,
    IsSeparatingHalfwayStopover G (row.paths i) (stopover i)
  heightAtMost : ∀ i, HeightAtMost G (stopover i) (rho i)
  frontier_eq : ∀ i, G.terminalFrontier (row.paths i) = stopover i

/-- The source set required at the next horizontal row after closing under
all competitors in the fixed linkage and the current simultaneous row. -/
def nextTargetSources {I : Type u} (G : DWeb V) (fixed : Set G.DPath)
    (S : TargetRowStage G I) (i : I) : Set V :=
  G.competitorStep (fixed ∪ ⋃ j, S.paths j) (S.sources i)

/-- A strong uniform sufficient successor rule.  It asks for actual next
paths, not an abstract compatibility relation: every column is
forward-extended and links the competitor-closed next source set.  This
uniform form is intentionally stronger than the construction needs, since
arbitrary target rows need not be extendible.  `TargetRowMachine` below is
the exact future-proof, certificate-carrying interface. -/
def TargetRowSuccessorRule {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath) : Prop :=
  ∀ S : TargetRowStage G I,
    ∃ T : TargetRowStage G I,
      T.sources = nextTargetSources G fixed S ∧
      ∀ i, G.ForwardExtension (S.paths i) (T.paths i)

/-- Choose the concrete next simultaneous row supplied by a successor
rule. -/
noncomputable def nextTargetRowStage {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath)
    (hstep : TargetRowSuccessorRule (I := I) G fixed)
    (S : TargetRowStage G I) : TargetRowStage G I :=
  Classical.choose (hstep S)

theorem nextTargetRowStage_sources {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath)
    (hstep : TargetRowSuccessorRule (I := I) G fixed)
    (S : TargetRowStage G I) :
    (nextTargetRowStage G fixed hstep S).sources =
      nextTargetSources G fixed S :=
  (Classical.choose_spec (hstep S)).1

theorem forward_nextTargetRowStage {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath)
    (hstep : TargetRowSuccessorRule (I := I) G fixed)
    (S : TargetRowStage G I) (i : I) :
    G.ForwardExtension (S.paths i)
      ((nextTargetRowStage G fixed hstep S).paths i) :=
  (Classical.choose_spec (hstep S)).2 i

/-- Iterate the simultaneous successor rule through the inner omega
closing-up recursion. -/
noncomputable def targetRowStages {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath)
    (hstep : TargetRowSuccessorRule (I := I) G fixed)
    (S₀ : TargetRowStage G I) : ℕ → TargetRowStage G I
  | 0 => S₀
  | n + 1 => nextTargetRowStage G fixed hstep
      (targetRowStages G fixed hstep S₀ n)

@[simp] theorem targetRowStages_zero {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath)
    (hstep : TargetRowSuccessorRule (I := I) G fixed)
    (S₀ : TargetRowStage G I) :
    targetRowStages G fixed hstep S₀ 0 = S₀ := rfl

@[simp] theorem targetRowStages_succ {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath)
    (hstep : TargetRowSuccessorRule (I := I) G fixed)
    (S₀ : TargetRowStage G I) (n : ℕ) :
    targetRowStages G fixed hstep S₀ (n + 1) =
      nextTargetRowStage G fixed hstep
        (targetRowStages G fixed hstep S₀ n) := rfl

/-- A future-proof row state machine.  Its private state may carry all
roof, terminal-clean, quotient, safe-deletion, and frozen-path certificates
needed to build the next row.  Only the concrete row and the two transition
facts consumed by the singular matrix are exposed.  Unlike the uniform
successor rule above, no claim is made about arbitrary rows. -/
structure TargetRowMachine {I : Type u} (G : DWeb V)
    (fixed : Set G.DPath) (initialSources : I → Set V) where
  State : Type u
  row : State → TargetRowStage G I
  initial : State
  next : State → State
  sources_initial : (row initial).sources = initialSources
  sources_next : ∀ s,
    (row (next s)).sources = nextTargetSources G fixed (row s)
  forward_next : ∀ s i,
    G.ForwardExtension ((row s).paths i) ((row (next s)).paths i)

namespace TargetRowMachine

/-- The state reached after `n` genuine future-proof transitions. -/
def stateAt {I : Type u} {G : DWeb V} {fixed : Set G.DPath}
    {initialSources : I → Set V}
    (M : TargetRowMachine G fixed initialSources) : ℕ → M.State
  | 0 => M.initial
  | n + 1 => M.next (stateAt M n)

@[simp] theorem stateAt_zero {I : Type u} {G : DWeb V}
    {fixed : Set G.DPath} {initialSources : I → Set V}
    (M : TargetRowMachine G fixed initialSources) :
    stateAt M 0 = M.initial := rfl

@[simp] theorem stateAt_succ {I : Type u} {G : DWeb V}
    {fixed : Set G.DPath} {initialSources : I → Set V}
    (M : TargetRowMachine G fixed initialSources) (n : ℕ) :
    stateAt M (n + 1) = M.next (stateAt M n) := rfl

/-- The machine's concrete source rows agree with `matrixSources`. -/
theorem sources_eq_matrixSources
    {I : Type u} [Preorder I] {G : DWeb V} {fixed : Set G.DPath}
    {initialSources : I → Set V}
    (M : TargetRowMachine G fixed initialSources) (i : I) (n : ℕ) :
    (M.row (stateAt M n)).sources i =
      matrixSources G fixed
        (fun j m ↦ (M.row (stateAt M m)).paths j)
        initialSources i n := by
  induction n with
  | zero =>
      exact congrFun M.sources_initial i
  | succ n ih =>
      rw [stateAt_succ, M.sources_next]
      change G.competitorStep
          (fixed ∪ ⋃ j, (M.row (stateAt M n)).paths j)
          ((M.row (stateAt M n)).sources i) = _
      rw [matrixSources_succ, ih]
      rfl

/-- Forget the machine's private certificates after iterating it: the
displayed rows are exactly the target-row matrix required by Assertion
9.18.  This is the canonical consumer for a future-proof implementation of
Assertion 9.17. -/
noncomputable def toTargetRows
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (M : TargetRowMachine G fixed
      (sourceLayer A₀ kappa hcard huncountable hsingular)) :
    TargetRows G fixed A₀ kappa huncountable hsingular hcard where
  paths i n := (M.row (stateAt M n)).paths i
  isWarp i n := (M.row (stateAt M n)).isWarp i
  finiteCharacter i n := (M.row (stateAt M n)).finiteCharacter i
  initialSet i n := (M.row (stateAt M n)).initialSet i
  targetSegment i n a ha := by
    rw [← M.sources_eq_matrixSources i n] at ha ⊢
    exact targetSegment_of_linksToTarget
      ((M.row (stateAt M n)).links i) ha
  forward i n := M.forward_next (stateAt M n) i

end TargetRowMachine

/-- The zeroth singular row obtained from the public lower induction, with
its weak stop-over data retained.  It is a valid provisional matrix row,
but it is not by itself a sound input to the quotient successor: the public
clause supplies no source-separator certificate. -/
noncomputable def initialWeakHalfwayTargetRowStage
    {G : DWeb V}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hG : G.IsUnhindered) :
    WeakHalfwayTargetRowStage G (Index kappa) := by
  let A : Index kappa → Set V :=
    sourceLayer A₀ kappa hcard huncountable hsingular
  let rho : Index kappa → Cardinal.{u} :=
    scale kappa huncountable hsingular
  have hex : ∀ i, ∃ (W : Set G.DPath) (C : Set V),
      IsHalfwayLinkageOfAltitude G (A i) (rho i) W ∧
        IsHalfwayStopover G W C := by
    intro i
    have hbelow : rho i < kappa :=
      scale_below kappa huncountable hsingular i
    have hinfinite : aleph0 ≤ rho i :=
      scale_infinite kappa huncountable hsingular i
    have hAsub : A i ⊆ G.source :=
      (sourceLayer_subset A₀ kappa hcard huncountable hsingular i).trans
        hA₀
    have hAcard : #(A i) = rho i :=
      sourceLayer_card A₀ kappa hcard huncountable hsingular i
    obtain ⟨W, hW⟩ :=
      (hlower (rho i) hbelow G hG).halfway hinfinite (A i) hAsub hAcard
    obtain ⟨C, hC⟩ := hW.1
    exact ⟨W, C, hW, hC⟩
  let W : Index kappa → Set G.DPath := fun i ↦ Classical.choose (hex i)
  let C : Index kappa → Set V := fun i ↦
    Classical.choose (Classical.choose_spec (hex i))
  have hspec (i : Index kappa) :
      IsHalfwayLinkageOfAltitude G (A i) (rho i) (W i) ∧
        IsHalfwayStopover G (W i) (C i) :=
    Classical.choose_spec (Classical.choose_spec (hex i))
  refine
    { row :=
        { sources := A
          paths := W
          isWarp := ?_
          finiteCharacter := ?_
          initialSet := ?_
          links := ?_ }
      stopover := C
      halfway := ?_ }
  · intro i
    exact (hspec i).2.linkage.isWarp
  · intro i
    exact (hspec i).2.linkage.finiteCharacter
  · intro i
    exact (hspec i).2.linkage.initialSet_eq
  · intro i
    exact (hspec i).1.2.1
  · intro i
    exact (hspec i).2

/-- The genuinely future-proof zeroth row obtained from the corrected
strong lower interface.  Unlike `initialWeakHalfwayTargetRowStage`, this
retains the separator and height witnesses needed by the singular
successor. -/
noncomputable def initialCertifiedTargetRowStage
    {G : DWeb V}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hG : G.IsUnhindered) :
    CertifiedTargetRowStage G (Index kappa)
      (scale kappa huncountable hsingular) := by
  let A : Index kappa → Set V :=
    sourceLayer A₀ kappa hcard huncountable hsingular
  let rho : Index kappa → Cardinal.{u} :=
    scale kappa huncountable hsingular
  have hex : ∀ i, ∃ (W : Set G.DPath) (C : Set V),
      IsSeparatingHalfwayStopover G W C ∧
        LinksToTarget G W (A i) ∧ HeightAtMost G C (rho i) ∧
        G.terminalFrontier W = C := by
    intro i
    have hbelow : rho i < kappa :=
      scale_below kappa huncountable hsingular i
    have hinfinite : aleph0 ≤ rho i :=
      scale_infinite kappa huncountable hsingular i
    have hAsub : A i ⊆ G.source :=
      (sourceLayer_subset A₀ kappa hcard huncountable hsingular i).trans
        hA₀
    have hAcard : #(A i) = rho i :=
      sourceLayer_card A₀ kappa hcard huncountable hsingular i
    exact (hlower (rho i) hbelow G hG).separatingHalfway hinfinite
      (A i) hAsub hAcard
  let W : Index kappa → Set G.DPath := fun i ↦ Classical.choose (hex i)
  let C : Index kappa → Set V := fun i ↦
    Classical.choose (Classical.choose_spec (hex i))
  have hspec (i : Index kappa) :
      IsSeparatingHalfwayStopover G (W i) (C i) ∧
        LinksToTarget G (W i) (A i) ∧
        HeightAtMost G (C i) (rho i) ∧
        G.terminalFrontier (W i) = C i :=
    Classical.choose_spec (Classical.choose_spec (hex i))
  refine
    { row :=
        { sources := A
          paths := W
          isWarp := ?_
          finiteCharacter := ?_
          initialSet := ?_
          links := ?_ }
      stopover := C
      separating := ?_
      heightAtMost := ?_
      frontier_eq := ?_ }
  · intro i
    exact (hspec i).1.stopover.linkage.isWarp
  · intro i
    exact (hspec i).1.stopover.linkage.finiteCharacter
  · intro i
    exact (hspec i).1.stopover.linkage.initialSet_eq
  · intro i
    exact (hspec i).2.1
  · intro i
    exact (hspec i).1
  · intro i
    exact (hspec i).2.2.1
  · intro i
    exact (hspec i).2.2.2

@[simp] theorem initialCertifiedTargetRowStage_sources
    {G : DWeb V}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hG : G.IsUnhindered) :
    (initialCertifiedTargetRowStage hA₀ hcard huncountable hsingular
      hlower hG).row.sources =
      sourceLayer A₀ kappa hcard huncountable hsingular := by
  rfl

/-- The canonical provisional zeroth row, constructed columnwise from the
lower induction hypothesis. -/
noncomputable def initialTargetRowStage
    {G : DWeb V}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hG : G.IsUnhindered) (_hNorm : G.IsNormalized) :
    TargetRowStage G (Index kappa) :=
  (initialWeakHalfwayTargetRowStage hA₀ hcard huncountable hsingular
    hlower hG).row

/-- The recursively stored source component is definitionally the same
competitor recursion used by `matrixSources`. -/
theorem targetRowStages_sources_eq_matrixSources
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    (hstep : TargetRowSuccessorRule (I := Index kappa) G fixed)
    (i : Index kappa) (n : ℕ) :
    let S₀ := initialTargetRowStage hA₀ hcard huncountable hsingular
      hlower hG hNorm
    let stages := targetRowStages G fixed hstep S₀
    (stages n).sources i =
      matrixSources G fixed (fun j m ↦ (stages m).paths j)
        (sourceLayer A₀ kappa hcard huncountable hsingular) i n := by
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [targetRowStages_succ,
        nextTargetRowStage_sources G fixed hstep]
      change G.competitorStep
          (fixed ∪ ⋃ j,
            (targetRowStages G fixed hstep
              (initialTargetRowStage hA₀ hcard huncountable hsingular
                hlower hG hNorm) n).paths j)
          ((targetRowStages G fixed hstep
            (initialTargetRowStage hA₀ hcard huncountable hsingular
              hlower hG hNorm) n).sources i) = _
      rw [matrixSources_succ, ih]
      rfl

/-- Iterating one genuine simultaneous successor rule produces the exact
coherent target rows consumed by the singular matrix. -/
noncomputable def targetRows_of_successorRule
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    (hA₀ : A₀ ⊆ G.source) (hcard : #A₀ = kappa)
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    (hstep : TargetRowSuccessorRule (I := Index kappa) G fixed) :
    TargetRows G fixed A₀ kappa huncountable hsingular hcard := by
  let S₀ := initialTargetRowStage hA₀ hcard huncountable hsingular
    hlower hG hNorm
  let stages := targetRowStages G fixed hstep S₀
  refine
    { paths := fun i n ↦ (stages n).paths i
      isWarp := ?_
      finiteCharacter := ?_
      initialSet := ?_
      targetSegment := ?_
      forward := ?_ }
  · intro i n
    exact (stages n).isWarp i
  · intro i n
    exact (stages n).finiteCharacter i
  · intro i n
    exact (stages n).initialSet i
  · intro i n a ha
    have hsources := targetRowStages_sources_eq_matrixSources
      hA₀ hcard huncountable hsingular hlower hG hNorm hstep i n
    rw [← hsources] at ha ⊢
    exact targetSegment_of_linksToTarget ((stages n).links i) ha
  · intro i n
    exact forward_nextTargetRowStage G fixed hstep (stages n) i

/-- The coherent path-row output of Assertion 9.17, separated from its
already-formalized cardinal bookkeeping. -/
structure SingularRows (G : DWeb V) (fixed : Set G.DPath)
    (A₀ : Set V) (kappa : Cardinal.{u})
    (huncountable : aleph0 < kappa) (hsingular : kappa.IsSingular)
    (hcard : #A₀ = kappa) where
  paths : Index kappa → ℕ → Set G.DPath
  isWarp : ∀ i n, G.IsWarp (paths i n)
  finiteCharacter : ∀ i n, G.HasFiniteCharacter (paths i n)
  initialSet : ∀ i n, G.initialSet (paths i n) = G.source
  qualified : ∀ i n,
    IsHalfwayLinkageOfAltitude G
      (matrixSources G fixed paths
        (sourceLayer A₀ kappa hcard huncountable hsingular) i n)
      (scale kappa huncountable hsingular i) (paths i n)
  forward : ∀ i n,
    G.ForwardExtension (paths i n) (paths i (n + 1))

/-- Forget the half-way certificate after extracting the concrete finite
target segments which are the only part used by the singular limit. -/
noncomputable def SingularRows.toTargetRows
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (R : SingularRows G fixed A₀ kappa huncountable hsingular hcard) :
    TargetRows G fixed A₀ kappa huncountable hsingular hcard where
  paths := R.paths
  isWarp := R.isWarp
  finiteCharacter := R.finiteCharacter
  initialSet := R.initialSet
  targetSegment := fun i n _a ha ↦
    targetSegment_of_linksToTarget (R.qualified i n).2.1 ha
  forward := R.forward

/-- The concrete competitor matrix attached to the minimal target-row
certificate.  The abstract `Qualified` field is instantiated by `True`;
all substantive target information is supplied through `targetSegment`. -/
noncomputable def TargetRows.matrix
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (R : TargetRows G fixed A₀ kappa huncountable hsingular hcard)
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    SingularCardinal.CompetitorMatrix (I := Index kappa) G
      (scale kappa huncountable hsingular) A₀
      (fun _ _ _ ↦ True) := by
  apply competitorMatrixOfPaths G fixed R.paths
    (sourceLayer A₀ kappa hcard huncountable hsingular)
    (scale kappa huncountable hsingular) A₀
    (fun _ _ _ ↦ True)
  · exact hfixed.isWarp
  · exact hfixed.finiteCharacter
  · exact hfixed.initialSet_eq
  · exact hfixed.terminalFrontier_subset
  · intro i
    exact (sourceLayer_subset A₀ kappa hcard huncountable hsingular i).trans
      hA₀
  · exact sourceLayer_card A₀ kappa hcard huncountable hsingular
  · exact sourceLayer_mono A₀ kappa hcard huncountable hsingular
  · exact sourceLayer_cover A₀ kappa hcard huncountable hsingular
  · exact scale_infinite kappa huncountable hsingular
  · exact scale_index_le kappa huncountable hsingular
  · exact R.isWarp
  · exact R.finiteCharacter
  · exact R.initialSet
  · simp
  · exact R.targetSegment
  · exact R.forward

/-- The concrete competitor matrix attached to coherent singular rows. -/
noncomputable def SingularRows.matrix
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (R : SingularRows G fixed A₀ kappa huncountable hsingular hcard)
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    SingularCardinal.CompetitorMatrix (I := Index kappa) G
      (scale kappa huncountable hsingular) A₀
      (fun A rho W => IsHalfwayLinkageOfAltitude G A rho W) := by
  apply competitorMatrixOfPaths G fixed R.paths
    (sourceLayer A₀ kappa hcard huncountable hsingular)
    (scale kappa huncountable hsingular) A₀
    (fun A rho W => IsHalfwayLinkageOfAltitude G A rho W)
  · exact hfixed.isWarp
  · exact hfixed.finiteCharacter
  · exact hfixed.initialSet_eq
  · exact hfixed.terminalFrontier_subset
  · intro i
    exact (sourceLayer_subset A₀ kappa hcard huncountable hsingular i).trans
      hA₀
  · exact sourceLayer_card A₀ kappa hcard huncountable hsingular
  · exact sourceLayer_mono A₀ kappa hcard huncountable hsingular
  · exact sourceLayer_cover A₀ kappa hcard huncountable hsingular
  · exact scale_infinite kappa huncountable hsingular
  · exact scale_index_le kappa huncountable hsingular
  · exact R.isWarp
  · exact R.finiteCharacter
  · exact R.initialSet
  · exact R.qualified
  · intro i n a ha
    exact targetSegment_of_linksToTarget (R.qualified i n).2.1 ha
  · exact R.forward

/-- Assertion 9.18 and the least-column construction consume the row
certificate without any further set-theoretic assumptions. -/
theorem isLinkable_of_singularRows
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (R : SingularRows G fixed A₀ kappa huncountable hsingular hcard)
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    IsLinkable G := by
  exact SingularLeast.isLinkable_of_competitorMatrix
    (R.matrix hA₀ hfixed) hfixed

/-- Assertion 9.18 needs no half-way structure beyond the target segments
recorded in `TargetRows`. -/
theorem isLinkable_of_targetRows
    {G : DWeb V} {fixed : Set G.DPath}
    {A₀ : Set V} {kappa : Cardinal.{u}}
    {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
    {hcard : #A₀ = kappa}
    (R : TargetRows G fixed A₀ kappa huncountable hsingular hcard)
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    IsLinkable G := by
  exact SingularLeast.isLinkable_of_competitorMatrix
    (R.matrix hA₀ hfixed) hfixed

end SingularExtension

/-- Exact reduction of the singular extension clause to the coherent-row
selection theorem of Assertion 9.17.  This is intentionally phrased with
`TargetRows`, the minimal concrete output consumed by Assertion 9.18, so a
future-proof half-way construction need not preserve unused altitude data
at every continuation stage. -/
theorem singularExtensionClauseAt_of_targetRows
    (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V)
    (hrows : ∀ (A₀ : Set V), A₀ ⊆ Gamma.source → (hcard : #A₀ = kappa) →
      ∀ fixed : Set Gamma.DPath,
        IsLinkageBetween Gamma (Gamma.source \ A₀) Gamma.target fixed →
        SingularExtension.TargetRows Gamma fixed A₀ kappa
          hkappa hsingular hcard) :
    ExtensionClauseAt Gamma kappa := by
  intro A₀ hA₀ hcard hfixed
  obtain ⟨fixed, hfixed⟩ := hfixed
  exact SingularExtension.isLinkable_of_targetRows
    (hrows A₀ hA₀ hcard fixed hfixed) hA₀ hfixed

/-- Normalized local-successor reduction in the exact form needed by the
eventual public singular theorem.  Normalization, the provisional zeroth
row, the omega recursion, and the final competitor-matrix assembly are all
discharged here; only the genuine future-proof successor construction is
an input. -/
theorem singularExtensionClauseAt_of_normalizedSuccessorRule
    (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hstep : ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      (hcard : #A₀ = kappa) →
      ∀ fixed : Set Gamma.normalized.DPath,
        IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target fixed →
        SingularExtension.TargetRowSuccessorRule
          (I := SingularMatrix.Index kappa) Gamma.normalized fixed) :
    ExtensionClauseAt Gamma kappa := by
  apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
  intro A₀ hA₀ hcard hfixed
  obtain ⟨fixed, hfixed⟩ := hfixed
  let R := SingularExtension.targetRows_of_successorRule
    hA₀ hcard hkappa hsingular hlower hGamma.normalized
      Gamma.normalized_isNormalized
      (hstep A₀ hA₀ hcard fixed hfixed)
  exact SingularExtension.isLinkable_of_targetRows R hA₀ hfixed

/-- Exact normalized reduction to a future-proof row machine.  The
machine's private state may depend on the particular initial source layers
and frozen linkage, which is essential for the safe-deletion and quotient
compatibility certificates in Assertion 9.17. -/
theorem singularExtensionClauseAt_of_normalizedTargetRowMachine
    (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (Gamma : DWeb V)
    (hmachine : ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      (hcard : #A₀ = kappa) →
      ∀ fixed : Set Gamma.normalized.DPath,
        IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target fixed →
        SingularExtension.TargetRowMachine Gamma.normalized fixed
          (SingularMatrix.sourceLayer A₀ kappa hcard hkappa hsingular)) :
    ExtensionClauseAt Gamma kappa := by
  apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
  intro A₀ hA₀ hcard hfixed
  obtain ⟨fixed, hfixed⟩ := hfixed
  let M := hmachine A₀ hA₀ hcard fixed hfixed
  exact SingularExtension.isLinkable_of_targetRows M.toTargetRows hA₀ hfixed

/-- Corrected induction-facing singular interface.  The row-machine
constructor receives the strengthened zeroth row produced by the strong
lower half-way clause.  This makes the separator needed for quotient
continuation available without claiming that it follows from the public
weak `HalfwayClauseAt`.

The strengthened `CardinalInductionAt` now retains this data, so its ordinary
lower-induction package supplies the certified initial row directly. -/
theorem singularExtensionClauseAt_of_normalizedCertifiedTargetRowMachine
    (kappa : Cardinal.{u})
    (hkappa : aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hmachine : ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      (hcard : #A₀ = kappa) →
      ∀ fixed : Set Gamma.normalized.DPath,
        IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target fixed →
        SingularExtension.CertifiedTargetRowStage Gamma.normalized
          (SingularMatrix.Index kappa)
          (SingularMatrix.scale kappa hkappa hsingular) →
        SingularExtension.TargetRowMachine Gamma.normalized fixed
          (SingularMatrix.sourceLayer A₀ kappa hcard hkappa hsingular)) :
    ExtensionClauseAt Gamma kappa := by
  apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
  intro A₀ hA₀ hcard hfixed
  obtain ⟨fixed, hfixed⟩ := hfixed
  let S₀ := SingularExtension.initialCertifiedTargetRowStage
    hA₀ hcard hkappa hsingular hlower hGamma.normalized
  let M := hmachine A₀ hA₀ hcard fixed hfixed S₀
  exact SingularExtension.isLinkable_of_targetRows M.toTargetRows hA₀ hfixed

end CardinalInduction
end Erdos599
