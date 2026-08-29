/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate

/-!
# Clean rows and later-boundary selection for regular slices

There are two logically separate boundary issues in Assertion 9.10.

* A half-way linkage may be cut at its first visit to its stop-over.  This
  always gives a terminal-clean source--stop-over linkage.  It continues to
  link a designated set to the original target provided the designated
  sources which are not already targets avoid the stop-over.
* A small set of vertices in the limit *strict* roof can be put strictly
  behind one later member of any club.  The later frontier is then disjoint
  from that set by strict frontier chronology.

Both side conditions are necessary.  In particular, mere membership in the
limit roof is not enough for the second assertion: a vertex in the boundary
of the limit roof may persist on every later frontier.  Likewise
`SingularInitialTightObstruction.disjoint_designated_nonTarget_of_terminalClean`
shows that the avoidance premise in the first assertion is forced by its
conclusion in a normalized web.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace RegularBetaSelection

open DirectedPath
open SliceCandidate

universe u

variable {V : Type u}

/-- Every walk ending in `T` meets `T`, independently of its initial set. -/
theorem separates_right_boundary (Q : DWeb V) (A T : Set V) :
    RelationalRoof.Separates Q.graph.Adj A T T := by
  intro _ t p _ ht
  exact ⟨t, p.end_mem_support, ht⟩

/-- Cut every member of a linkage at its first visit to the right boundary. -/
def targetFirstHitFamily
    {Q : DWeb V} {A T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y) : Set Q.DPath :=
  firstHitPrefixFamily hY (separates_right_boundary Q A T)

/-- Target-first-hit truncation remains a linkage with the same two
boundaries. -/
theorem targetFirstHitFamily_isLinkageBetween
    {Q : DWeb V} {A T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y) :
    IsLinkageBetween Q A T (targetFirstHitFamily hY) :=
  firstHitPrefixFamily_isLinkageBetween hY
    (separates_right_boundary Q A T)

/-- Target-first-hit truncation is automatically right-tight, including
the case in which a source already belongs to the right boundary (when the
corresponding prefix is trivial). -/
theorem targetFirstHitFamily_meetsOnlyAtTerminal
    {Q : DWeb V} {A T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y) :
    SliceSpliceSource.MeetsOnlyAtTerminal Q
      (targetFirstHitFamily hY) T := by
  let hsep : RelationalRoof.Separates Q.graph.Adj A T T :=
    separates_right_boundary Q A T
  rintro _ ⟨a, rfl⟩ x hx hxT
  have hx' : x ∈ (linkageFirstHitAt hY hsep a).support ∩ T :=
    ⟨hx, hxT⟩
  rw [linkageFirstHitAt_targetPure hY hsep a] at hx'
  have hxeq : x = (linkageFirstHitAt hY hsep a).finish :=
    Set.mem_singleton_iff.mp hx'
  exact congrArg some hxeq.symm

/-- The first-hit family is a componentwise prefix of the original
linkage. -/
theorem targetFirstHitFamily_forwardExtension
    {Q : DWeb V} {A T : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A T Y) :
    Q.ForwardExtension (targetFirstHitFamily hY) Y := by
  let hsep : RelationalRoof.Separates Q.graph.Adj A T T :=
    separates_right_boundary Q A T
  constructor
  · rintro p ⟨a, rfl⟩
    refine ⟨(linkageMemberAt hY a).1, (linkageMemberAt hY a).2, ?_⟩
    rw [linkageMemberAt_eq_finite]
    exact (linkageFiniteAt hY a).walk.firstHit T
      (linkageFiniteAt_meets hY hsep a) |>.support_prefix
  · intro q hqY
    have hqA : q.initial ∈ A := by
      rw [← hY.initialSet_eq]
      exact ⟨q, hqY, rfl⟩
    let a : A := ⟨q.initial, hqA⟩
    have hmember : (linkageMemberAt hY a).1 = q := by
      by_contra hne
      have hdisjoint := hY.isWarp (linkageMemberAt hY a).2 hqY hne
      have hinitial : (linkageMemberAt hY a).1.initial = q.initial := by
        simpa only [a] using linkageMemberAt_initial hY a
      exact Set.disjoint_left.1 hdisjoint
        (linkageMemberAt hY a).1.initial_mem_support (by
          rw [hinitial]
          exact q.initial_mem_support)
    refine ⟨(Sum.inl (linkageFirstHitAt hY hsep a) : Q.DPath),
      ⟨a, rfl⟩, ?_⟩
    rw [← hmember, linkageMemberAt_eq_finite]
    exact (linkageFiniteAt hY a).walk.firstHit T
      (linkageFiniteAt_meets hY hsep a) |>.support_prefix

/-- First-hit normalization of a normalized half-way row preserves its
target links when the designated non-target starts avoid the stop-over.

The source inclusion matters: `LinksToTarget` allows a designated vertex to
occur internally in general, whereas here endpoint purity identifies it with
the initial vertex of its selected member. -/
theorem targetFirstHitFamily_linksToTarget_of_subsource
    {Q : DWeb V} (hNorm : Q.IsNormalized)
    {A C U : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q A C Y)
    (hUA : U ⊆ A)
    (hlinks : LinksToTarget Q Y U)
    (havoid : Disjoint (U \ Q.target) C) :
    LinksToTarget Q (targetFirstHitFamily hY) U := by
  let hsep : RelationalRoof.Separates Q.graph.Adj A C C :=
    separates_right_boundary Q A C
  intro a haU
  obtain ⟨p, hpY, q, rfl, hpure, before, after, hsupport,
    b, hbTarget, hbAfter⟩ := hlinks a haU
  have haSupport : a ∈ q.support := by
    have haInter : a ∈ q.support ∩ U := by
      rw [hpure]
      exact Set.mem_singleton a
    exact haInter.1
  have haStart : q.start = a := by
    obtain ⟨f, hfq, _hends, hsource⟩ :=
      hY.endpointPure (Sum.inl q : Q.DPath) hpY
    have hf : f = q := Sum.inl.inj hfq.symm
    subst f
    have haA : a ∈ q.support ∩ A := ⟨haSupport, hUA haU⟩
    rw [hsource] at haA
    exact (Set.mem_singleton_iff.mp haA).symm
  let as : A := ⟨a, hUA haU⟩
  have hmember : (linkageMemberAt hY as).1 =
      (Sum.inl q : Q.DPath) := by
    by_contra hne
    have hdisjoint := hY.isWarp (linkageMemberAt hY as).2 hpY hne
    have hinitial : (linkageMemberAt hY as).1.initial = q.start := by
      rw [linkageMemberAt_initial hY as, haStart]
    exact Set.disjoint_left.1 hdisjoint
      (linkageMemberAt hY as).1.initial_mem_support (by
        rw [hinitial]
        exact q.start_mem_support)
  have hfinite : linkageFiniteAt hY as = q := by
    have hm := linkageMemberAt_eq_finite hY as
    rw [hmember] at hm
    exact Sum.inl.inj hm.symm
  let f := linkageFirstHitAt hY hsep as
  have hfFinish : f.finish = q.finish := by
    have hfFinishC : f.finish ∈ C := linkageFirstHitAt_finish_mem hY hsep as
    have hfFinishQ : f.finish ∈ q.support := by
      rw [← hfinite]
      exact linkageFirstHitAt_support_subset hY hsep as
        f.finish_mem_support
    obtain ⟨q', hq', hends, _hsource⟩ :=
      hY.endpointPure (Sum.inl q : Q.DPath) hpY
    have hq'eq : q' = q := Sum.inl.inj hq'.symm
    subst q'
    have hfEnds : f.finish ∈ ({q.start, q.finish} : Set V) := by
      rw [← hends]
      exact ⟨hfFinishQ, Or.inr hfFinishC⟩
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hfEnds
    rcases hfEnds with hfStart | hfFinish
    · by_cases haTarget : a ∈ Q.target
      · have hterminalA : Q.terminal? (Sum.inl q : Q.DPath) = some a :=
          hNorm.terminal?_eq_of_mem_path (.inl q) haSupport haTarget
        change some q.finish = some a at hterminalA
        exact calc
          f.finish = q.start := hfStart
          _ = a := haStart
          _ = q.finish := (Option.some.inj hterminalA).symm
      · exact False.elim (Set.disjoint_left.1 havoid
          ⟨haU, haTarget⟩ (haStart ▸ hfStart ▸ hfFinishC))
    · exact hfFinish
  have hfTarget : f.finish ∈ Q.target := by
    have hbSupport : b ∈ q.support := by
      change b ∈ q.walk.support
      rw [hsupport]
      exact List.mem_append_right before hbAfter
    have hterminalB : Q.terminal? (Sum.inl q : Q.DPath) = some b :=
      hNorm.terminal?_eq_of_mem_path (.inl q) hbSupport hbTarget
    change some q.finish = some b at hterminalB
    have hqFinishTarget : q.finish ∈ Q.target :=
      Option.some.inj hterminalB ▸ hbTarget
    exact hfFinish.symm ▸ hqFinishTarget
  refine ⟨(Sum.inl f : Q.DPath), ⟨as, rfl⟩, f, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxU⟩
      have hxq : x ∈ q.support := by
        rw [← hfinite]
        exact linkageFirstHitAt_support_subset hY hsep as hxf
      have hx : x ∈ ({a} : Set V) := by
        rw [← hpure]
        exact ⟨hxq, hxU⟩
      exact hx
    · rintro x hx
      have hxa : x = a := Set.mem_singleton_iff.mp hx
      subst x
      have hfStartA : f.start = a := by
        exact (linkageFirstHitAt_start hY hsep as).trans rfl
      exact ⟨hfStartA ▸ f.start_mem_support, haU⟩
  · have hlist : f.walk.support = f.start :: f.walk.support.tail := by
      have h := (List.cons_head_tail f.walk.support_ne_nil).symm
      simpa [f.walk.head_support] using h
    have hfStartA : f.start = a := by
      exact (linkageFirstHitAt_start hY hsep as).trans rfl
    have hcons : f.start :: f.walk.support.tail =
        a :: f.walk.support.tail :=
      congrArg (fun z => z :: f.walk.support.tail) hfStartA
    refine ⟨[], f.walk.support.tail, ?_, f.finish, hfTarget, ?_⟩
    · simpa using hlist.trans hcons
    · have hfinish : f.finish ∈ f.start :: f.walk.support.tail := by
        rw [← hlist]
        exact f.finish_mem_support
      exact hcons ▸ hfinish

theorem targetFirstHitFamily_linksToTarget
    {Q : DWeb V} (hNorm : Q.IsNormalized)
    {C U : Set V} {Y : Set Q.DPath}
    (hY : IsLinkageBetween Q Q.source C Y)
    (hUsource : U ⊆ Q.source)
    (hlinks : LinksToTarget Q Y U)
    (havoid : Disjoint (U \ Q.target) C) :
    LinksToTarget Q (targetFirstHitFamily hY) U := by
  exact targetFirstHitFamily_linksToTarget_of_subsource hNorm hY
    hUsource hlinks havoid

/-- A checked clean-row package.  It replaces an arbitrary normalized
source--`C` linkage by a terminal-clean prefix linkage while retaining the
same stop-over, quotient, and height data. -/
theorem exists_clean_firstHitPayload
    {Q : DWeb V} (hNorm : Q.IsNormalized)
    {C U : Set V} {W : Set Q.DPath}
    (hW : IsLinkageBetween Q Q.source C W)
    (hUsource : U ⊆ Q.source)
    (hlinks : LinksToTarget Q W U)
    (havoid : Disjoint (U \ Q.target) C) :
    ∃ W' : Set Q.DPath,
      IsLinkageBetween Q Q.source C W' ∧
        LinksToTarget Q W' U ∧
        SliceSpliceSource.MeetsOnlyAtTerminal Q W' C ∧
        Q.ForwardExtension W' W := by
  refine ⟨targetFirstHitFamily hW,
    targetFirstHitFamily_isLinkageBetween hW,
    targetFirstHitFamily_linksToTarget hNorm hW hUsource hlinks havoid,
    targetFirstHitFamily_meetsOnlyAtTerminal hW,
    targetFirstHitFamily_forwardExtension hW⟩

/-- A small subset of the limit strict roof is disjoint from some strictly
later member of any prescribed club. -/
theorem exists_later_club_disjoint_frontier_of_small_limitStrictRoof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    {S : Set V} (hSstrict : S ⊆ L.limitStrictRoof)
    (hSsmall : #S < kappa) (delta : Ladder.Stage kappa) :
    ∃ beta ∈ Sigma, delta < beta ∧ Disjoint S (L.frontier beta) := by
  let witness : ∀ x : S, ∃ a : Ladder.Stage kappa,
      x.1 ∈ Gamma.strictRoof (L.frontier a) := fun x ↦ by
    exact Set.mem_iUnion.mp (hSstrict x.2)
  let bound : S → Ladder.Stage kappa := fun x ↦
    Classical.choose (witness x)
  have hbound : ∀ x : S, (bound x).1 < kappa.ord := fun x ↦
    (bound x).2
  let o : Ordinal.{u} := iSup (fun x : S ↦ (bound x).1 + 1)
  have ho : o < kappa.ord :=
    Stationary.iSup_add_one_lt_ord_of_lt hL.regular hSsmall hbound
  let beta := RegularCardinal.aboveInClub hL.regular Sigma hSigma delta
    (⟨o, ho⟩ : Ladder.Stage kappa)
  refine ⟨beta,
    RegularCardinal.aboveInClub_mem hL.regular Sigma hSigma delta ⟨o, ho⟩,
    RegularCardinal.left_lt_aboveInClub hL.regular Sigma hSigma delta ⟨o, ho⟩,
    ?_⟩
  apply Set.disjoint_left.2
  intro x hxS hxFrontier
  let xs : S := ⟨x, hxS⟩
  have hboundO : (bound xs).1 < o :=
    (Order.lt_succ (bound xs).1).trans_le
      (Ordinal.le_iSup (fun y : S ↦ (bound y).1 + 1) xs)
  have hboundBeta : bound xs < beta :=
    lt_of_lt_of_le hboundO
      (RegularCardinal.right_lt_aboveInClub hL.regular Sigma hSigma
        delta ⟨o, ho⟩).le
  exact Set.disjoint_left.1 (hL.strictFrontierChronology hboundBeta)
    (Classical.choose_spec (witness xs)) hxFrontier

/-- A small set of persistent boundary points is contained in every
sufficiently late frontier, with the threshold chosen inside a prescribed
club.  This is the complementary half of the regular request split: points
in the limit roof but outside the limit strict roof cannot be made disjoint
from later frontiers. -/
theorem exists_later_club_eventually_contains_of_small_persistent
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    {S : Set V} (hSpersistent : S ⊆ L.limitRoof \ L.limitStrictRoof)
    (hSsmall : #S < kappa) (delta : Ladder.Stage kappa) :
    ∃ beta ∈ Sigma, delta < beta ∧
      ∀ gamma : Ladder.Stage kappa, beta ≤ gamma →
        S ⊆ L.frontier gamma := by
  let witness : ∀ x : S, ∃ a : Ladder.Stage kappa,
      ∀ b : Ladder.Stage kappa, a ≤ b → x.1 ∈ L.frontier b := fun x ↦ by
    exact (hL.mem_limitRoof_diff_limitStrictRoof_iff_eventually_frontier
      x.1).1 (hSpersistent x.2)
  let bound : S → Ladder.Stage kappa := fun x ↦
    Classical.choose (witness x)
  have hbound : ∀ x : S, (bound x).1 < kappa.ord := fun x ↦
    (bound x).2
  let o : Ordinal.{u} := iSup (fun x : S ↦ (bound x).1 + 1)
  have ho : o < kappa.ord :=
    Stationary.iSup_add_one_lt_ord_of_lt hL.regular hSsmall hbound
  let beta := RegularCardinal.aboveInClub hL.regular Sigma hSigma delta
    (⟨o, ho⟩ : Ladder.Stage kappa)
  refine ⟨beta,
    RegularCardinal.aboveInClub_mem hL.regular Sigma hSigma delta ⟨o, ho⟩,
    RegularCardinal.left_lt_aboveInClub hL.regular Sigma hSigma delta
      ⟨o, ho⟩, ?_⟩
  intro gamma hbetaGamma x hxS
  let xs : S := ⟨x, hxS⟩
  have hboundO : (bound xs).1 < o :=
    (Order.lt_succ (bound xs).1).trans_le
      (Ordinal.le_iSup (fun y : S ↦ (bound y).1 + 1) xs)
  have hboundBeta : bound xs < beta :=
    lt_of_lt_of_le hboundO
      (RegularCardinal.right_lt_aboveInClub hL.regular Sigma hSigma
        delta ⟨o, ho⟩).le
  exact Classical.choose_spec (witness xs) gamma
    (hboundBeta.le.trans hbetaGamma)

/-- The form consumed by a right-tight slice constructor: all designated
non-target starts can be kept off a later club frontier, provided they are
already in the limit strict roof. -/
theorem exists_later_club_disjoint_nonTarget_frontier
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    {U : Set V} (hUstrict : U \ Gamma.target ⊆ L.limitStrictRoof)
    (hUsmall : #U < kappa) (delta : Ladder.Stage kappa) :
    ∃ beta ∈ Sigma, delta < beta ∧
      Disjoint (U \ Gamma.target) (L.frontier beta) := by
  exact exists_later_club_disjoint_frontier_of_small_limitStrictRoof
    hL hSigma hUstrict
      ((Cardinal.mk_subtype_mono Set.sdiff_subset).trans_lt hUsmall) delta

/-- Source-faithful eventual tightening.  If a weak annular linkage can be
constructed at every sufficiently late club frontier, regularity lets us
first choose a frontier avoiding the small set of designated non-target
sources and only then cut the linkage at its first visit to that frontier.
The cut remains target-linking and becomes right-tight.

This is the sound regular replacement for permanently deleting completed
paths: the right boundary is selected after the request is known. -/
theorem exists_later_club_targetFirstHit_tight_linkage
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.IsSplitLegal)
    {Sigma : Set (Ladder.Stage kappa)}
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    {Q : DWeb V} (hNorm : Q.IsNormalized)
    (hTarget : Q.target = Gamma.target)
    {U : Set V} (hUsource : U ⊆ Q.source)
    (hUstrict : U \ Gamma.target ⊆ L.limitStrictRoof)
    (hUsmall : #U < kappa) (delta : Ladder.Stage kappa)
    (hweak : ∀ beta ∈ Sigma, delta < beta →
      ∃ W : Set Q.DPath,
        IsLinkageBetween Q Q.source (L.frontier beta) W ∧
          LinksToTarget Q W U) :
    ∃ beta ∈ Sigma, delta < beta ∧
      ∃ W W' : Set Q.DPath,
        IsLinkageBetween Q Q.source (L.frontier beta) W ∧
          LinksToTarget Q W U ∧
          IsLinkageBetween Q Q.source (L.frontier beta) W' ∧
          LinksToTarget Q W' U ∧
          SliceSpliceSource.MeetsOnlyAtTerminal Q W' (L.frontier beta) ∧
          Q.ForwardExtension W' W := by
  obtain ⟨beta, hbeta, hdeltaBeta, havoid⟩ :=
    exists_later_club_disjoint_nonTarget_frontier hL hSigma hUstrict
      hUsmall delta
  obtain ⟨W, hW, hlinks⟩ := hweak beta hbeta hdeltaBeta
  obtain ⟨W', hW', hlinks', htight, hforward⟩ :=
    exists_clean_firstHitPayload hNorm hW hUsource hlinks (by
      simpa [hTarget] using havoid)
  exact ⟨beta, hbeta, hdeltaBeta, W, W', hW, hlinks, hW', hlinks',
    htight, hforward⟩

end RegularBetaSelection
end CardinalInduction
end Erdos599
