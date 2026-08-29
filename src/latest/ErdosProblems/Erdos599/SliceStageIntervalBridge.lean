/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalOrdinaryIntervals
import ErdosProblems.Erdos599.LadderExhaustionLoose
import ErdosProblems.Erdos599.HeightRoofBridge
import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.SliceSuffixFromAux

/-!
# Retyping ordinary ladder intervals in the old stage web

The component exchange in Assertion 9.10 is performed in the essential
quotient at the left endpoint of the interval.  This file proves that the
literal stage intervals constructed in `SliceCandidate` are honest paths
in that web; it does not replace them by merely equisupported paths.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

open DirectedPath

universe u
variable {V : Type u}

/-! ## Exact inverses for the two stage restrictions -/

theorem lift_restrictWalkGraphOnSupport
    {D E : Digraph V} {a b : V} (p : DirectedPath.Walk D a b)
    (h : ∀ {x y : V}, D.Adj x y → x ∈ p.support → y ∈ p.support →
      E.Adj x y)
    (hED : ∀ {x y : V}, E.Adj x y → D.Adj x y) :
    (p.restrictGraphOnSupport h).lift hED = p := by
  induction p with
  | nil => rfl
  | @cons x y z e p ih =>
      simp only [DirectedPath.Walk.restrictGraphOnSupport,
        DirectedPath.Walk.lift]
      congr
      apply ih
      intro u v huv hu hv
      apply h huv
      · simp only [DirectedPath.Walk.support_cons, List.mem_cons]
        exact Or.inr hu
      · simp only [DirectedPath.Walk.support_cons, List.mem_cons]
        exact Or.inr hv

theorem lift_restrictFiniteGraphOnSupport
    {D E : Digraph V} (p : DirectedPath.FinitePath D)
    (h : ∀ {x y : V}, D.Adj x y → x ∈ p.support → y ∈ p.support →
      E.Adj x y)
    (hED : ∀ {x y : V}, E.Adj x y → D.Adj x y) :
    (p.restrictGraphOnSupport h).lift hED = p := by
  cases p with
  | mk start finish walk isPath =>
      rw [DirectedPath.FinitePath.mk.injEq]
      exact ⟨rfl, rfl, heq_of_eq
        (lift_restrictWalkGraphOnSupport walk
          (fun e hx hy ↦ h e hx hy) hED)⟩

theorem lift_restrictPathGraphOnSupport
    {D E : Digraph V} (p : DirectedPath.Path D)
    (h : ∀ {x y : V}, D.Adj x y → x ∈ p.support → y ∈ p.support →
      E.Adj x y)
    (hED : ∀ {x y : V}, E.Adj x y → D.Adj x y) :
    (p.restrictGraphOnSupport h).lift hED = p := by
  rcases p with p | r
  · exact congrArg Sum.inl
      (lift_restrictFiniteGraphOnSupport p h hED)
  · apply congrArg Sum.inr
    apply DirectedPath.Ray.ext
    rfl

/-- The traversed-edge quotient restriction does not change the walk when
it is lifted back to the ambient graph.  This exact equality, rather than
only equality of supports, is what ultimately identifies the lifted stage
interval with the literal ladder interval. -/
theorem lift_restrictWalkToQuotient
    (G : DWeb V) (T : Set V) {a b : V}
    (p : DirectedPath.Walk G.graph a b)
    (hstrict : ∀ {x}, x ∈ p.support → x ∉ G.strictRoof T)
    (hcommit : ∀ {x}, x ∈ p.support.tail → x ∉ T) :
    (G.restrictWalkToQuotient T p hstrict hcommit).lift
        (fun {_ _} e ↦ G.quotient_adj_imp e) = p := by
  induction p with
  | nil => rfl
  | @cons u v w e p ih =>
      let hs : ∀ {x}, x ∈ p.support → x ∉ G.strictRoof T :=
        fun {_} hx hbad ↦ hstrict (by simp [hx]) hbad
      let hc : ∀ {x}, x ∈ p.support.tail → x ∉ T :=
        fun {_} hx hbad ↦ hcommit (List.mem_of_mem_tail hx) hbad
      change DirectedPath.Walk.cons _
          ((G.restrictWalkToQuotient T p hs hc).lift _) =
        DirectedPath.Walk.cons e p
      congr
      exact ih hs hc

/-- Finite-path form of `lift_restrictWalkToQuotient`. -/
theorem lift_restrictFinitePathToQuotient
    (G : DWeb V) (T : Set V)
    (p : DirectedPath.FinitePath G.graph)
    (hstrict : ∀ {x}, x ∈ p.walk.support → x ∉ G.strictRoof T)
    (hcommit : ∀ {x}, x ∈ p.walk.support.tail → x ∉ T) :
    (G.restrictFinitePathToQuotient T p hstrict hcommit).lift
        (fun {_ _} e ↦ G.quotient_adj_imp e) = p := by
  cases p with
  | mk start finish walk isPath =>
      rw [DirectedPath.FinitePath.mk.injEq]
      exact ⟨rfl, rfl, heq_of_eq
        (lift_restrictWalkToQuotient G T walk hstrict hcommit)⟩

/-- Restricting to the essential part and then forgetting that restriction
is exactly the identity on paths. -/
theorem liftEssentialPartPath_restrictEssentialPartPath
    (G : DWeb V) (p : G.DPath)
    (hreach : p.support ⊆ G.reachableToTarget) :
    G.liftEssentialPartPath (G.restrictEssentialPartPath p hreach) = p := by
  unfold DWeb.liftEssentialPartPath DWeb.restrictEssentialPartPath
  exact @lift_restrictPathGraphOnSupport
    V G.graph G.essentialPart.graph p
    (fun e hx hy ↦ ⟨e, hreach hx, hreach hy⟩)
    (fun e ↦ G.essentialPart_adj_imp e)

/-- A finite path which meets `T` only at its initial vertex, starts at an
essential point of `T`, and has terminal outside the strict roof survives
the quotient by `T`.  The noninitial tail avoids the whole roof: its
terminal is outside `T`, hence outside the roof, and the standard
finite-path roof lemma applies to that tail. -/
theorem finitePath_pathQuotientAdmissible_of_sourcePure
    (G : DWeb V) {T : Set V} (p : DirectedPath.FinitePath G.graph)
    (hpure : p.support ∩ T = {p.start})
    (hstart : p.start ∈ G.essential T)
    (hfinish : p.finish ∉ G.strictRoof T) :
    G.PathQuotientAdmissible T (Sum.inl p) := by
  rcases p with ⟨a, b, w, hw⟩
  cases w with
  | nil =>
      constructor
      · intro x hx
        simp only [DirectedPath.Walk.support_nil, List.mem_singleton] at hx
        subst x
        exact fun hxStrict ↦ Set.disjoint_left.1
          (G.disjoint_strictRoof_essential T) hxStrict hstart
      · simp
  | @cons _ c _ e q =>
      have hnodup : (a :: q.support).Nodup := hw
      have haNotTail : a ∉ q.support := (List.nodup_cons.mp hnodup).1
      have hqPath : q.IsPath := (List.nodup_cons.mp hnodup).2
      let tail : DirectedPath.FinitePath G.graph :=
        { start := c, finish := b, walk := q, isPath := hqPath }
      have htailT : Disjoint tail.support T := by
        apply Set.disjoint_left.2
        intro z hzq hzT
        have hzSupport : z ∈
            ({z | z ∈ a :: q.support} : Set V) := by
          exact List.mem_cons_of_mem a hzq
        have hzEq : z = a := by
          apply Set.mem_singleton_iff.mp
          rw [← hpure]
          exact ⟨hzSupport, hzT⟩
        exact haNotTail (hzEq ▸ hzq)
      have hbNotT : b ∉ T := by
        intro hbT
        have hbSupport : b ∈
            ({z | z ∈ a :: q.support} : Set V) := by
          exact List.mem_cons_of_mem a q.end_mem_support
        have hbEq : b = a := by
          apply Set.mem_singleton_iff.mp
          rw [← hpure]
          exact ⟨hbSupport, hbT⟩
        exact haNotTail (hbEq ▸ q.end_mem_support)
      have hbNotRoof : b ∉ G.roof T := by
        intro hbRoof
        apply hfinish
        refine ⟨hbRoof, ?_⟩
        intro hbEssential
        exact hbNotT (G.essential_subset T hbEssential)
      have htailRoof : Disjoint tail.support (G.roof T) :=
        G.finitePath_support_disjoint_roof_of_finish_not_roof
          T tail htailT hbNotRoof
      constructor
      · intro x hx
        change x ∈ a :: q.support at hx
        rcases List.mem_cons.mp hx with rfl | hxq
        · exact fun hxStrict ↦ Set.disjoint_left.1
            (G.disjoint_strictRoof_essential T) hxStrict hstart
        · exact fun hxStrict ↦ Set.disjoint_left.1 htailRoof hxq hxStrict.1
      · intro x hx
        change x ∈ q.support at hx
        exact Set.disjoint_left.1 htailT hx

/-- The raw strict roof deleted at stage `delta` is disjoint from every
later frontier. -/
theorem rawStrictRoof_disjoint_laterFrontier
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    Disjoint
      (Gamma.strictRoof (Gamma.terminalFrontier (L.warpAt delta)))
      (L.frontier beta) := by
  have heq : Gamma.strictRoof
        (Gamma.terminalFrontier (L.warpAt delta)) =
      Gamma.strictRoof (L.frontier delta) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages delta, Gamma.strictRoof_essential]
  rw [heq]
  rcases hdeltaBeta.lt_or_eq with hlt | rfl
  · exact hL.strictFrontierChronology hlt
  · have h := Gamma.disjoint_strictRoof_essential (L.frontier delta)
    rwa [hL.frontiersEssential delta] at h

/-- A vertex outside the raw accumulated roof survives in the old
essential quotient stage and is target-reachable there. -/
theorem mem_stageWeb_reachable_of_not_mem_rawRoof
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (L : Gamma.KappaLadder kappa) (delta : Ladder.Stage kappa) {x : V}
    (hx : x ∉ Gamma.roof
      (Gamma.terminalFrontier (L.warpAt delta))) :
    x ∈ (L.stageWeb delta).reachableToTarget := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (Gamma.not_mem_roof_iff T x).1 hx
  have hdisjoint := Set.disjoint_left.1 hpAvoid
  have hstrict : ∀ {y}, y ∈ p.walk.support →
      y ∉ Gamma.strictRoof T := by
    intro y hy hyStrict
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      Gamma.graph.Adj p.walk).1 hy with hyeq | hytail
    · have hyx : y = x := hyeq.trans hpTarget.1
      exact hx (hyx ▸ hyStrict.1)
    · have hyne : y ≠ p.start := by
        intro h
        exact p.isPath.rel_head_tail hytail
          (p.walk.head_support.trans h.symm)
      have hpAvoid' : RelationalRoof.Avoids Gamma.graph.Adj
          p (T \ {p.start}) := by
        intro z hz hzT
        exact hdisjoint hz hzT.1
      have hyNotRoof :=
        RelationalRoof.not_mem_roof_of_later_mem_targetPath
          Gamma.graph.Adj Gamma.target p hpTarget hpAvoid' hy hyne
      exact hyNotRoof hyStrict.1
  have hcommit : ∀ {y}, y ∈ p.walk.support.tail → y ∉ T := by
    intro y hy hyT
    exact hdisjoint (List.mem_of_mem_tail hy) hyT
  let q := Gamma.restrictFinitePathToQuotient T p hstrict hcommit
  have hqReach : x ∈ (Gamma.quotient T).reachableToTarget := by
    refine ⟨q, ?_, ?_⟩
    · change p.start = x
      exact hpTarget.1
    · change p.finish ∈ Gamma.target
      exact hpTarget.2
  exact (Gamma.quotient T).mem_essentialPart_reachableToTarget_of_mem'
    hqReach

/-- A literal stage interval meets the raw terminal frontier of the old
accumulated warp only at its first vertex.  The point is that an arbitrary
raw-frontier member has a later extension; if that extension meets the
chosen later component, warp disjointness identifies both the later and
the earlier components. -/
theorem StageIntervalRealization.segment_rawSource_pure
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) (x : S) :
    (R.toSegmentRealization.segment x).support ∩
        Gamma.terminalFrontier (L.warpAt delta) =
      {(R.toSegmentRealization.segment x).start} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hySegment, hyFrontier⟩
    obtain ⟨p, hpDelta, hpy⟩ := hyFrontier
    obtain ⟨q, hqBeta, hpq⟩ :=
      hL.grows hdeltaBeta p hpDelta
    let hstart : DirectedPath.Path.initial
        (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) =
          (R.leftPrefix x).finish := by
      change (R.toSegmentRealization.segment x).start =
        (R.leftPrefix x).finish
      exact R.toSegmentRealization.segment_start x |>.trans
        (R.left_finish x).symm
    let hinter : (R.leftPrefix x).support ∩
        DirectedPath.Path.support
          (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) ⊆
          {(R.leftPrefix x).finish} := by
      change (R.leftPrefix x).support ∩
        (R.toSegmentRealization.segment x).support ⊆
          {(R.leftPrefix x).finish}
      exact (R.prefix_inter x).subset
    let appended : Gamma.DPath :=
      DirectedPath.Path.appendFinite (R.leftPrefix x)
        (.inl (R.toSegmentRealization.segment x)) hstart
        hinter
    have happended : appended =
        (Sum.inl (R.rightPrefix x) : Gamma.DPath) := by
      simpa only [appended] using R.append_eq x
    have hyRight : y ∈ (R.rightPrefix x).support := by
      have hyAppend : y ∈ appended.support := by
        dsimp only [appended]
        rw [DirectedPath.Path.support_appendFinite]
        exact Or.inr hySegment
      rw [happended] at hyAppend
      exact hyAppend
    have hyQ : y ∈ q.support :=
      Gamma.support_mono_of_extends hpq
        (Gamma.terminal_mem_support hpy)
    have hqRight : q = (Sum.inl (R.rightPrefix x) : Gamma.DPath) := by
      by_contra hne
      exact Set.disjoint_left.1
        (hL.warpStages (Ladder.Stage.toExtended beta)
          hqBeta (R.right_mem x).1 hne) hyQ hyRight
    have hpInitial : p.initial = (R.leftPrefix x).start := by
      calc
        p.initial = q.initial := Gamma.extends_initial hpq
        _ = (R.rightPrefix x).start :=
          congrArg DirectedPath.Path.initial hqRight
        _ = (R.leftPrefix x).start := by
          calc
            (R.rightPrefix x).start = appended.initial :=
              congrArg DirectedPath.Path.initial happended.symm
            _ = (R.leftPrefix x).start :=
              DirectedPath.Path.initial_appendFinite _ _ _ _
    have hpLeft : p =
        (Sum.inl (R.leftPrefix x) : Gamma.DPath) := by
      apply DWeb.IsWarp.eq_of_initial_eq Gamma
        (hL.warpStages (Ladder.Stage.toExtended delta))
        hpDelta (R.left_mem x).1
      exact hpInitial
    apply Set.mem_singleton_iff.mpr
    calc
      y = (R.leftPrefix x).finish := by
        have h := hpy
        rw [hpLeft] at h
        exact Option.some.inj h |>.symm
      _ = x.1 := R.left_finish x
      _ = (R.toSegmentRealization.segment x).start :=
        (R.toSegmentRealization.segment_start x).symm
  · intro y hy
    have hyStart : y = (R.toSegmentRealization.segment x).start :=
      Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨(R.toSegmentRealization.segment x).start_mem_support, ?_⟩
    rw [R.toSegmentRealization.segment_start x, ← R.left_finish x]
    exact ⟨Sum.inl (R.leftPrefix x), (R.left_mem x).1, rfl⟩

/-- The terminal of a stage interval is reachable in the old stage web.
If it is still on the raw old frontier, raw-source purity identifies it
with the initial vertex; otherwise avoidance of the raw strict roof
upgrades it to avoidance of the whole raw roof. -/
theorem StageIntervalRealization.segment_finish_stageReachable
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) (x : S) :
    (R.toSegmentRealization.segment x).finish ∈
      (L.stageWeb delta).reachableToTarget := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  let p := R.toSegmentRealization.segment x
  have hpure : p.support ∩ T = {p.start} :=
    R.segment_rawSource_pure hL hdeltaBeta x
  have hstartFrontier : p.start ∈ L.frontier delta := by
    rw [R.toSegmentRealization.segment_start x]
    exact R.toSegmentRealization.source_subset x.2
  have hfinishFrontier : p.finish ∈ L.frontier beta :=
    R.toSegmentRealization.segment_finish_mem x
  have hfinishNotStrict : p.finish ∉ Gamma.strictRoof T :=
    fun h ↦ Set.disjoint_left.1
      (rawStrictRoof_disjoint_laterFrontier hL hdeltaBeta)
      h hfinishFrontier
  by_cases hfinishT : p.finish ∈ T
  · have hfinishEq : p.finish = p.start := by
      apply Set.mem_singleton_iff.mp
      rw [← hpure]
      exact ⟨p.finish_mem_support, hfinishT⟩
    rw [hfinishEq]
    exact (Gamma.quotient T).mem_essentialPart_reachableToTarget_of_mem'
      hstartFrontier.2
  · have hfinishNotRoof : p.finish ∉ Gamma.roof T := by
      intro hroof
      apply hfinishNotStrict
      refine ⟨hroof, ?_⟩
      exact fun hessential ↦ hfinishT
        (Gamma.essential_subset T hessential)
    exact mem_stageWeb_reachable_of_not_mem_rawRoof L delta hfinishNotRoof

/-- Forgetting the induced essential-part restriction preserves finite
target reachability. -/
theorem reachableToTarget_essentialPart_subset (G : DWeb V) :
    G.essentialPart.reachableToTarget ⊆ G.reachableToTarget := by
  rintro x ⟨p, hpStart, hpFinish⟩
  let q : DirectedPath.FinitePath G.graph :=
    p.lift fun {_ _} e ↦ G.essentialPart_adj_imp e
  exact ⟨q, by
    constructor
    · change p.start = x
      exact hpStart
    · change p.finish ∈ G.target
      exact hpFinish⟩

/-- Quotient admissibility of one literal interval, exposed independently
of the retyping definition so later support calculations can reuse the
same proof. -/
theorem StageIntervalRealization.stageSegment_admissible
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) (x : S) :
    Gamma.PathQuotientAdmissible
      (Gamma.terminalFrontier (L.warpAt delta))
      (Sum.inl (R.toSegmentRealization.segment x)) := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  let p := R.toSegmentRealization.segment x
  have hpure : p.support ∩ T = {p.start} :=
    R.segment_rawSource_pure hL hdeltaBeta x
  have hstartFrontier : p.start ∈ L.frontier delta := by
    rw [R.toSegmentRealization.segment_start x]
    exact R.toSegmentRealization.source_subset x.2
  have hstartEssential : p.start ∈ Gamma.essential T := by
    rw [← L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages delta]
    exact hstartFrontier
  have hfinishFrontier : p.finish ∈ L.frontier beta :=
    R.toSegmentRealization.segment_finish_mem x
  have hfinishNotStrict : p.finish ∉ Gamma.strictRoof T :=
    fun h ↦ Set.disjoint_left.1
      (rawStrictRoof_disjoint_laterFrontier hL hdeltaBeta)
      h hfinishFrontier
  exact finitePath_pathQuotientAdmissible_of_sourcePure Gamma p
    hpure hstartEssential hfinishNotStrict

/-- Retype one literal interval in the old essential quotient stage. -/
noncomputable def StageIntervalRealization.stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) (x : S) :
    (L.stageWeb delta).DPath := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  let p := R.toSegmentRealization.segment x
  let hadm : Gamma.PathQuotientAdmissible T (Sum.inl p) :=
    R.stageSegment_admissible hL hdeltaBeta x
  let q : DirectedPath.FinitePath (Gamma.quotient T).graph :=
    Gamma.restrictFinitePathToQuotient T p hadm.1 hadm.2
  have hfinishReach : q.finish ∈
      (Gamma.quotient T).reachableToTarget := by
    change p.finish ∈ (Gamma.quotient T).reachableToTarget
    exact reachableToTarget_essentialPart_subset (Gamma.quotient T)
      (R.segment_finish_stageReachable hL hdeltaBeta x)
  have hreach : DirectedPath.Path.support
      (Sum.inl q : (Gamma.quotient T).DPath) ⊆
      (Gamma.quotient T).reachableToTarget := by
    change q.support ⊆ (Gamma.quotient T).reachableToTarget
    exact finitePath_support_subset_reachable_of_finish
      (Gamma.quotient T) q hfinishReach
  exact (Gamma.quotient T).restrictEssentialPartPath (.inl q) hreach

/-- Lifting a retyped stage interval through the essential part and the
quotient recovers the literal ambient ladder interval, with its original
walk and edge order. -/
@[simp] theorem StageIntervalRealization.liftStagePath_stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) (x : S) :
    L.liftStagePath delta (R.stageSegment hL hdeltaBeta x) =
      (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  let p := R.toSegmentRealization.segment x
  let hadm : Gamma.PathQuotientAdmissible T (Sum.inl p) :=
    R.stageSegment_admissible hL hdeltaBeta x
  let q : DirectedPath.FinitePath (Gamma.quotient T).graph :=
    Gamma.restrictFinitePathToQuotient T p hadm.1 hadm.2
  have hfinishReach : q.finish ∈
      (Gamma.quotient T).reachableToTarget := by
    change p.finish ∈ (Gamma.quotient T).reachableToTarget
    exact reachableToTarget_essentialPart_subset (Gamma.quotient T)
      (R.segment_finish_stageReachable hL hdeltaBeta x)
  have hreach : DirectedPath.Path.support
      (Sum.inl q : (Gamma.quotient T).DPath) ⊆
      (Gamma.quotient T).reachableToTarget := by
    change q.support ⊆ (Gamma.quotient T).reachableToTarget
    exact finitePath_support_subset_reachable_of_finish
      (Gamma.quotient T) q hfinishReach
  change Gamma.liftQuotientPath T
      ((Gamma.quotient T).liftEssentialPartPath
        ((Gamma.quotient T).restrictEssentialPartPath (.inl q) hreach)) =
    (Sum.inl p : Gamma.DPath)
  rw [liftEssentialPartPath_restrictEssentialPartPath]
  unfold DWeb.liftQuotientPath
  apply congrArg Sum.inl
  exact lift_restrictFinitePathToQuotient Gamma T p hadm.1 hadm.2

@[simp] theorem StageIntervalRealization.support_stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) (x : S) :
    (R.stageSegment hL hdeltaBeta x).support =
      (R.toSegmentRealization.segment x).support := by
  simp only [stageSegment, DWeb.KappaLadder.stageWeb, DWeb.stageWebOf,
    DWeb.support_restrictEssentialPartPath]
  change (Gamma.restrictFinitePathToQuotient _
    (R.toSegmentRealization.segment x) _ _).support =
      (R.toSegmentRealization.segment x).support
  exact Gamma.support_restrictFinitePathToQuotient _ _
    (R.stageSegment_admissible hL hdeltaBeta x).1
    (R.stageSegment_admissible hL hdeltaBeta x).2

@[simp] theorem StageIntervalRealization.initial_stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) (x : S) :
    (R.stageSegment hL hdeltaBeta x).initial = x.1 := by
  simp only [stageSegment, DWeb.KappaLadder.stageWeb, DWeb.stageWebOf,
    initial_restrictEssentialPartPath]
  exact R.toSegmentRealization.segment_start x

@[simp] theorem StageIntervalRealization.terminal_stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) (x : S) :
    (L.stageWeb delta).terminal? (R.stageSegment hL hdeltaBeta x) =
      some (R.toSegmentRealization.segment x).finish := by
  simp only [stageSegment, DWeb.KappaLadder.stageWeb, DWeb.stageWebOf,
    terminal_restrictEssentialPartPath]
  rfl

/-- The family of all intervals, now typed in the old stage web. -/
noncomputable def StageIntervalRealization.stageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) :
    Set (L.stageWeb delta).DPath :=
  Set.range fun x : S ↦ R.stageSegment hL hdeltaBeta x

/-- Family-level exactness: lifting all retyped stage intervals gives the
literal segment family of the ambient stage realization. -/
@[simp] theorem StageIntervalRealization.liftStageFamily_stageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) :
    SliceSegmentCore.liftStageFamily L delta
        (R.stageFamily hL hdeltaBeta) =
      SliceSegmentCore.segmentFamily R.toSegmentRealization := by
  ext p
  constructor
  · rintro ⟨q, ⟨x, rfl⟩, rfl⟩
    rw [R.liftStagePath_stageSegment hL hdeltaBeta x]
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨R.stageSegment hL hdeltaBeta x, ⟨x, rfl⟩, ?_⟩
    exact R.liftStagePath_stageSegment hL hdeltaBeta x

theorem StageIntervalRealization.stageSegment_injective
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) :
    Function.Injective (fun x : S ↦ R.stageSegment hL hdeltaBeta x) := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg DirectedPath.Path.initial hxy
  simpa only [R.initial_stageSegment] using h

theorem StageIntervalRealization.stageSegment_finite
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) (x : S) :
    ∃ q : DirectedPath.FinitePath (L.stageWeb delta).graph,
      R.stageSegment hL hdeltaBeta x = Sum.inl q := by
  unfold stageSegment
  refine ⟨_, rfl⟩

/-- The retyped intervals form the exact source-faithful linkage required
by the whole-family component exchange. -/
theorem StageIntervalRealization.stageFamily_isLinkageBetween
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : L.SliceGeometry) (hdeltaBeta : delta ≤ beta) :
    IsLinkageBetween (L.stageWeb delta) S (L.frontier beta)
      (R.stageFamily hL hdeltaBeta) := by
  let F := R.stageFamily hL hdeltaBeta
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨x, rfl⟩ q ⟨y, rfl⟩ hpq
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hpq rfl
    have hambient := SliceSegmentCore.segmentFamily_isWarp
      (hL.warpStages (Ladder.Stage.toExtended beta))
      R.toSegmentRealization
    have hdis := hambient
      (show (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) ∈
          SliceSegmentCore.segmentFamily R.toSegmentRealization from
        ⟨x, rfl⟩)
      (show (Sum.inl (R.toSegmentRealization.segment y) : Gamma.DPath) ∈
          SliceSegmentCore.segmentFamily R.toSegmentRealization from
        ⟨y, rfl⟩)
      (by
        intro h
        apply hxy
        apply Subtype.ext
        have hi := congrArg DirectedPath.Path.initial h
        exact (R.toSegmentRealization.segment_start x).symm.trans
          (hi.trans (R.toSegmentRealization.segment_start y)))
    change Disjoint
      (R.stageSegment hL hdeltaBeta x).support
      (R.stageSegment hL hdeltaBeta y).support
    rw [R.support_stageSegment, R.support_stageSegment]
    exact hdis
  · rintro p ⟨x, rfl⟩
    exact R.stageSegment_finite hL hdeltaBeta x
  · ext v
    constructor
    · rintro ⟨p, ⟨x, rfl⟩, hp⟩
      rw [R.initial_stageSegment] at hp
      exact hp ▸ x.2
    · intro hv
      let x : S := ⟨v, hv⟩
      exact ⟨R.stageSegment hL hdeltaBeta x, ⟨x, rfl⟩,
        R.initial_stageSegment hL hdeltaBeta x⟩
  · rintro v ⟨p, ⟨x, rfl⟩, hp⟩
    rw [R.terminal_stageSegment] at hp
    exact Option.some.inj hp ▸
      R.toSegmentRealization.segment_finish_mem x
  · rintro p ⟨x, rfl⟩
    obtain ⟨q, hq⟩ := R.stageSegment_finite hL hdeltaBeta x
    have hsupport : q.support =
        (R.toSegmentRealization.segment x).support := by
      calc
        q.support = DirectedPath.Path.support
            (Sum.inl q : (L.stageWeb delta).DPath) := rfl
        _ = (R.stageSegment hL hdeltaBeta x).support :=
          congrArg DirectedPath.Path.support hq.symm
        _ = _ := R.support_stageSegment hL hdeltaBeta x
    have hstart : q.start = (R.toSegmentRealization.segment x).start := by
      calc
        q.start = DirectedPath.Path.initial
            (Sum.inl q : (L.stageWeb delta).DPath) := rfl
        _ = (R.stageSegment hL hdeltaBeta x).initial :=
          congrArg DirectedPath.Path.initial hq.symm
        _ = x.1 := R.initial_stageSegment hL hdeltaBeta x
        _ = (R.toSegmentRealization.segment x).start :=
          (R.toSegmentRealization.segment_start x).symm
    have hfinish : q.finish =
        (R.toSegmentRealization.segment x).finish := by
      apply Option.some.inj
      calc
        some q.finish = (L.stageWeb delta).terminal?
            (Sum.inl q : (L.stageWeb delta).DPath) := rfl
        _ = (L.stageWeb delta).terminal?
            (R.stageSegment hL hdeltaBeta x) :=
          congrArg (L.stageWeb delta).terminal? hq.symm
        _ = _ := R.terminal_stageSegment hL hdeltaBeta x
    refine ⟨q, hq, ?_, ?_⟩
    · rw [hsupport, hstart, hfinish]
      ext v
      constructor
      · rintro ⟨hvSupport, hv⟩
        have hv' : v ∈ (R.toSegmentRealization.segment x).support ∩
            (L.frontier delta ∪ L.frontier beta) :=
          ⟨hvSupport, hv.elim
            (fun h ↦ Or.inl (R.toSegmentRealization.source_subset h))
            Or.inr⟩
        rw [R.toSegmentRealization.segment_endpoints x] at hv'
        exact hv'
      · intro hv
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact ⟨(R.toSegmentRealization.segment x).start_mem_support,
            Or.inl (R.toSegmentRealization.segment_start x ▸ x.2)⟩
        · exact ⟨(R.toSegmentRealization.segment x).finish_mem_support,
            Or.inr (R.toSegmentRealization.segment_finish_mem x)⟩
    · rw [hsupport, hstart]
      ext v
      constructor
      · rintro ⟨hvSupport, hvS⟩
        have hv' : v ∈ (R.toSegmentRealization.segment x).support ∩
            L.frontier delta :=
          ⟨hvSupport, R.toSegmentRealization.source_subset hvS⟩
        rw [R.toSegmentRealization.segment_source x] at hv'
        exact hv'
      · intro hv
        have hvstart : v = (R.toSegmentRealization.segment x).start := by
          simpa only [Set.mem_singleton_iff] using hv
        subst v
        exact ⟨(R.toSegmentRealization.segment x).start_mem_support,
          R.toSegmentRealization.segment_start x ▸ x.2⟩

/-- The concrete old-stage family used by Assertion 9.10.  Its omitted
sources are precisely those whose later accumulated extension became
inessential. -/
theorem ordinaryStageIntervalRealization_segment_target_pure
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta)
    (x : ↑(L.frontier delta \
      inessentialExtensionSources hL hdeltaBeta)) :
    ((ordinaryStageIntervalRealization hL hdeltaBeta).toSegmentRealization.segment
        x).support ∩ L.frontier beta =
      {((ordinaryStageIntervalRealization hL hdeltaBeta).toSegmentRealization.segment
        x).finish} := by
  exact ordinaryStageIntervalRealization_segment_target_pure_ambient
    hL hdeltaBeta x

noncomputable def ordinaryStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    Set (L.stageWeb delta).DPath :=
  (ordinaryStageIntervalRealization hL hdeltaBeta).stageFamily
    hL hdeltaBeta

theorem ordinaryStageFamily_isLinkageBetween
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    IsLinkageBetween (L.stageWeb delta)
      (L.frontier delta \
        inessentialExtensionSources hL hdeltaBeta)
      (L.frontier beta) (ordinaryStageFamily hL hdeltaBeta) := by
  exact (ordinaryStageIntervalRealization hL hdeltaBeta)
    |>.stageFamily_isLinkageBetween hL hdeltaBeta

/-- The ordinary retyped interval family meets the later frontier only at
its terminal. -/
theorem ordinaryStageFamily_meetsOnlyAtTerminal
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    SliceSpliceSource.MeetsOnlyAtTerminal (L.stageWeb delta)
      (ordinaryStageFamily hL hdeltaBeta) (L.frontier beta) := by
  intro p hp x hxp hxBeta
  obtain ⟨s, rfl⟩ := hp
  have hxAmbient : x ∈
      ((ordinaryStageIntervalRealization hL hdeltaBeta).toSegmentRealization.segment
        s).support := by
    simpa only [StageIntervalRealization.support_stageSegment] using hxp
  have hxFinish : x =
      ((ordinaryStageIntervalRealization hL hdeltaBeta).toSegmentRealization.segment
        s).finish := by
    apply Set.mem_singleton_iff.mp
    rw [← ordinaryStageIntervalRealization_segment_target_pure
      hL hdeltaBeta s]
    exact ⟨hxAmbient, hxBeta⟩
  change (L.stageWeb delta).terminal?
      ((ordinaryStageIntervalRealization hL hdeltaBeta).stageSegment
        hL hdeltaBeta s) = some x
  rw [StageIntervalRealization.terminal_stageSegment]
  exact congrArg some hxFinish.symm

/-! ## Stage provenance for arbitrary completed linkages -/

/-- Two finite intervals of one finite simple path with the same ordered
endpoints are the same literal finite path. -/
theorem finitePath_eq_of_isSubpathOf_of_start_finish_eq
    {D : Digraph V} (owner p q : DirectedPath.FinitePath D)
    (hp : p.IsSubpathOf (Sum.inl owner))
    (hq : q.IsSubpathOf (Sum.inl owner))
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish) :
    p = q := by
  classical
  apply DirectedPath.FinitePath.eq_of_start_finish_edgeSet_eq
  · exact hstart
  · exact hfinish
  · rw [Alternating.FinitePath.edgeSet_eq_position_interval owner p hp,
      Alternating.FinitePath.edgeSet_eq_position_interval owner q hq,
      hstart, hfinish]

/-- Any member of a frontier-to-frontier linkage which is a fragment of
the later ladder warp is the literal interval between the corresponding
essential components at the two stages.  This applies in particular to
the arbitrary exceptional completions returned by the lower-cardinal
extension clause. -/
theorem isStageInterval_of_linkage_ladderFragment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta)
    {T : Set Gamma.DPath}
    (hT : IsLinkageBetween Gamma (L.frontier delta) (L.frontier beta) T)
    {p : Gamma.DPath} (hpT : p ∈ T)
    (hpFragment : ControlledSlices.IsLadderFragment
      Gamma (L.warpAt beta) p) :
    IsStageInterval Gamma L delta beta p := by
  obtain ⟨f, rfl, _hends, _hsource⟩ := hT.endpointPure p hpT
  have hfStart : f.start ∈ L.frontier delta := by
    rw [← hT.initialSet_eq]
    exact ⟨Sum.inl f, hpT, rfl⟩
  have hfFinish : f.finish ∈ L.frontier beta := by
    exact hT.terminalFrontier_subset ⟨Sum.inl f, hpT, rfl⟩
  obtain ⟨owner, hownerBeta, hfOwner⟩ := hpFragment
  obtain ⟨r, hrEssential, hrTerminal⟩ :=
    Gamma.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      (hL.roofsSourceAtStages (Ladder.Stage.toExtended beta)) hfFinish
  rcases r with right | ray
  · have hrightFinish : right.finish = f.finish :=
      Option.some.inj hrTerminal
    have hownerEq : owner = (Sum.inl right : Gamma.DPath) := by
      by_contra hne
      exact Set.disjoint_left.1
        (hL.warpStages (Ladder.Stage.toExtended beta)
          hownerBeta hrEssential.1 hne)
        (hfOwner.1 f.finish_mem_support)
        (hrightFinish ▸ right.finish_mem_support)
    have hfRight : f.IsSubpathOf (Sum.inl right : Gamma.DPath) := by
      rw [← hownerEq]
      exact hfOwner
    obtain ⟨l, hlEssential, hlTerminal⟩ :=
      Gamma.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
        (hL.roofsSourceAtStages (Ladder.Stage.toExtended delta)) hfStart
    rcases l with left | ray
    · have hleftFinish : left.finish = f.start :=
        Option.some.inj hlTerminal
      obtain ⟨q, hqBeta, hleftq⟩ :=
        hL.grows hdeltaBeta
          (Sum.inl left : Gamma.DPath) hlEssential.1
      have hqStart : f.start ∈ q.support := by
        apply Gamma.support_mono_of_extends hleftq
        rw [← hleftFinish]
        exact left.finish_mem_support
      have hrightStart : f.start ∈ right.support :=
        hfRight.1 f.start_mem_support
      have hqEq : q = (Sum.inl right : Gamma.DPath) := by
        by_contra hne
        exact Set.disjoint_left.1
          (hL.warpStages (Ladder.Stage.toExtended beta)
            hqBeta hrEssential.1 hne) hqStart hrightStart
      have hprefix : left.IsPrefixOf right := by
        rw [hqEq] at hleftq
        exact hleftq
      let hleftInRight : left.finish ∈ right.support :=
        hprefix.support_subset left.finish_mem_support
      let segment := right.suffixFromAux left.finish hleftInRight
      have hsegmentRight : segment.IsSubpathOf
          (Sum.inl right : Gamma.DPath) :=
        suffixFromAux_isSubpathOf_stage right left.finish hleftInRight
      have hsegmentStart : segment.start = f.start := by
        exact (right.suffixFromAux_start left.finish hleftInRight).trans
          hleftFinish
      have hsegmentFinish : segment.finish = f.finish := by
        exact (right.suffixFromAux_finish left.finish hleftInRight).trans
          hrightFinish
      have hfSegment : f = segment := by
        apply finitePath_eq_of_isSubpathOf_of_start_finish_eq right f segment
          hfRight hsegmentRight
        · exact hsegmentStart.symm
        · exact hsegmentFinish.symm
      subst f
      obtain ⟨hstart, hinter, hinterEq, happend⟩ :=
        appendFinite_suffixFromAux_eq_of_prefix hprefix
      change segment.start = left.finish at hstart
      change left.support ∩ segment.support ⊆ {left.finish} at hinter
      change left.support ∩ segment.support = {left.finish} at hinterEq
      change left.appendFinite segment hstart hinter = right at happend
      refine ⟨left, right, segment, rfl, hlEssential, hrEssential,
        ?_, ?_, hstart, hinter, hinterEq, ?_⟩
      · rw [hleftFinish]
        exact hfStart
      · rw [hrightFinish]
        exact hfFinish
      · exact congrArg Sum.inl happend
    · change (none : Option V) = some f.start at hlTerminal
      simp at hlTerminal
  · change (none : Option V) = some f.finish at hrTerminal
    simp at hrTerminal

/-- Every ordinary member of an arbitrary final frontier linkage has the
stage-local interval provenance required by the candidate table. -/
theorem linkage_hasStageIntervalSegments
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta)
    {T : Set Gamma.DPath}
    (hT : IsLinkageBetween Gamma (L.frontier delta) (L.frontier beta) T) :
    HasStageIntervalSegments Gamma L T delta beta := by
  intro p hpT hpFragment
  exact isStageInterval_of_linkage_ladderFragment
    hL hdeltaBeta hT hpT hpFragment

/-- The concrete ordinary stage family lifts to the exact ambient family
of literal intervals between the two accumulated ladder stages. -/
@[simp] theorem liftStageFamily_ordinaryStageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : L.SliceGeometry)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    SliceSegmentCore.liftStageFamily L delta
        (ordinaryStageFamily hL hdeltaBeta) =
      SliceSegmentCore.segmentFamily
        (ordinaryStageIntervalRealization hL hdeltaBeta).toSegmentRealization :=
  (ordinaryStageIntervalRealization hL hdeltaBeta)
    |>.liftStageFamily_stageFamily hL hdeltaBeta

end SliceCandidate
end CardinalInduction
end Erdos599
