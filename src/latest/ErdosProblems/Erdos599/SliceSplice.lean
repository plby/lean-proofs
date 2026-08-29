/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction
import ErdosProblems.Erdos599.ControlledSlices
import ErdosProblems.Erdos599.Ladder

/-!
# Transfinite splicing of controlled slices

This file isolates the direct-limit argument in Aharoni--Berger,
Assertion 9.11.  Successive controlled slices are spliced into finite
partial paths.  At limit stages one must take the direct limit of each
extension thread; taking a set-theoretic union of path records would lose
threads which are extended cofinally often.

The graph-specific successor construction has two invariants.  Every
partial family is a warp, and every designated source has a target-ending
member cofinally in its thread once that source is scheduled.  The latter
invariant is precisely what rules out a ray at the direct limit.  The
proof below turns these local invariants into an honest linkage and also
retains the closing-up set used in the regular-cardinal argument.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceSplice

open DirectedPath

universe u v

variable {V : Type u}

/-- If a terminal occurs cofinally in a path-extension chain, any member
of the chain with that terminal already has exactly the support of the
direct limit.  This is the bounded-thread part of Assertion 9.11. -/
theorem support_chainLimit_eq_of_terminalCofinal_of_mem
    {D : Digraph V} {C : Set (DirectedPath.Path D)}
    (hCne : C.Nonempty) (hC : IsChain DirectedPath.Path.Extends C)
    {b : V} (hb : DirectedPath.Path.TerminalCofinal C b)
    {q : DirectedPath.FinitePath D}
    (hqC : (Sum.inl q : DirectedPath.Path D) ∈ C)
    (hqfinish : q.finish = b) :
    (DirectedPath.Path.chainLimit C hCne hC).support = q.support := by
  rw [DirectedPath.Path.support_chainLimit C hCne hC]
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨p, hpC, hxp⟩ := hx
    obtain ⟨r, hrC, hpr, hrterm⟩ := hb p hpC
    rcases r with r | r
    · have hrfinish : r.finish = b := Option.some.inj hrterm
      have hrsupport : r.walk.support = q.walk.support :=
        DirectedPath.Path.finite_support_eq_of_chain_terminal_eq hC
          hrC hqC (hrfinish.trans hqfinish.symm)
      have hxr : x ∈ DirectedPath.Path.support
          (Sum.inl r : DirectedPath.Path D) :=
        DirectedPath.Path.support_mono_of_extends hpr hxp
      simpa only [DirectedPath.Path.support, DirectedPath.FinitePath.support,
        hrsupport] using hxr
    · simp at hrterm
  · intro x hx
    exact Set.mem_iUnion.2 ⟨Sum.inl q, Set.mem_iUnion.2 ⟨hqC, hx⟩⟩

/-- The local data retained by the transfinite slice recursion.

`spliceChain` is the chain of already-spliced families.  `targetCofinal` is
the exact scheduling conclusion: after the source belonging to a thread
is put into one of the sets `U_α`, paths ending at one fixed target
vertex occur above every earlier member of that thread.  The
`targetPathPure` field is local to finite successor stages; no property of
the proposed direct limit is assumed.

The controlled-slice witnesses themselves are kept in the structure so a
consumer cannot instantiate this interface with an unrelated chain.  The
successor replacement lemma proves `spliceChain.grows`, `targetCofinal`, and
`targetPathPure` from these witnesses. -/
structure ControlledSpliceChain {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (Sigma : Set (Ladder.Stage kappa)) (Z A : Set V) where
  /-- Club stage used at each recursion index. -/
  stageIndex : Ladder.Stage kappa → Ladder.Stage kappa
  stageIndex_mem : ∀ i, stageIndex i ∈ Sigma
  /-- The vertices scheduled at a successor step. -/
  scheduled : Ladder.Stage kappa → Set V
  scheduled_subset : ∀ i, scheduled i ⊆ L.frontier (stageIndex i) ∩ Z
  scheduled_small : ∀ i, #(scheduled i) < kappa
  /-- Later stage and controlled linkage returned by Assertion 9.15. -/
  nextIndex : Ladder.Stage kappa → Ladder.Stage kappa
  slice : Ladder.Stage kappa → Set Gamma.DPath
  next_mem : ∀ i, nextIndex i ∈ Sigma
  index_lt_next : ∀ i, stageIndex i < nextIndex i
  sliceControlled : ∀ i,
    RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z
      (stageIndex i) (nextIndex i) (scheduled i) (slice i)
  /-- Partial splices obtained by the successor replacement construction
  and by direct limits at limit indices. -/
  spliceChain : Gamma.GrowingWarpChain (Ladder.Stage kappa)
  initialUnion_eq : spliceChain.initialUnion = A
  vertices_closed : ∀ i, Gamma.vertexSet (spliceChain.stage i) ⊆ Z
  /-- A partial path which has reached the original target already has the
  endpoint-purity required of the final linkage. -/
  targetPathPure : ∀ i p, p ∈ spliceChain.stage i →
    ∀ b ∈ Gamma.target, p.terminal? = some b →
      IsPathBetween Gamma A Gamma.target p
  /-- Every source thread is eventually, and thereafter cofinally,
  represented by a path ending at one fixed original target vertex. -/
  targetCofinal : ∀ a : spliceChain.initialUnion,
    ∃ b ∈ Gamma.target,
      DirectedPath.Path.TerminalCofinal
        (spliceChain.thread Gamma a.1) b

namespace ControlledSpliceChain

variable {kappa : Cardinal.{u}} {Gamma : DWeb V}
variable {L : Gamma.KappaLadder kappa}
variable {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}

/-- Every direct-limit thread of a controlled splice is finite and ends in
the original target. -/
theorem threadLimit_finite_target
    (C : ControlledSpliceChain Gamma L Sigma Z A)
    (a : C.spliceChain.initialUnion) :
    ∃ q : DirectedPath.FinitePath Gamma.graph,
      C.spliceChain.threadLimit Gamma a = Sum.inl q ∧ q.finish ∈ Gamma.target := by
  obtain ⟨b, hbTarget, hb⟩ := C.targetCofinal a
  have hterminal :
      (C.spliceChain.threadLimit Gamma a).terminal? = some b :=
    DirectedPath.Path.terminal_chainLimit_of_cofinal
      (C.spliceChain.thread Gamma a.1)
      (C.spliceChain.thread_nonempty Gamma a)
      (C.spliceChain.thread_isChain Gamma a.1) hb
  generalize hq : C.spliceChain.threadLimit Gamma a = p at hterminal ⊢
  rcases p with q | r
  · have hqb : q.finish = b := Option.some.inj (by simpa using hterminal)
    exact ⟨q, rfl, hqb ▸ hbTarget⟩
  · simp at hterminal

/-- The limit of a controlled splice has no vertices outside the regular
closing-up set. -/
theorem vertexSet_limitPaths_subset
    (C : ControlledSpliceChain Gamma L Sigma Z A) :
    Gamma.vertexSet (C.spliceChain.limitPaths Gamma) ⊆ Z := by
  rintro x ⟨p, ⟨a, rfl⟩, hxp⟩
  obtain ⟨i, q, hqi, _hqa, hxq⟩ :=
    (C.spliceChain.mem_support_threadLimit_iff Gamma a x).1 hxp
  exact C.vertices_closed i ⟨q, hqi, hxq⟩

/-- Source Assertion 9.11: transfinite splicing of the controlled slices
produces an `A`--target linkage. -/
theorem isLinkageBetween_limitPaths
    (C : ControlledSpliceChain Gamma L Sigma Z A) :
    IsLinkageBetween Gamma A Gamma.target
      (C.spliceChain.limitPaths Gamma) := by
  refine ⟨C.spliceChain.isWarp_limitPaths Gamma, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨q, hq, _⟩ := C.threadLimit_finite_target a
    exact ⟨q, hq⟩
  · exact (C.spliceChain.initialSet_limitPaths Gamma).trans C.initialUnion_eq
  · rintro b ⟨p, ⟨a, hpa⟩, hpterm⟩
    subst p
    obtain ⟨c, hcTarget, hc⟩ := C.targetCofinal a
    have hterminal :
        (C.spliceChain.threadLimit Gamma a).terminal? = some c :=
      DirectedPath.Path.terminal_chainLimit_of_cofinal
        (C.spliceChain.thread Gamma a.1)
        (C.spliceChain.thread_nonempty Gamma a)
        (C.spliceChain.thread_isChain Gamma a.1) hc
    exact (Option.some.inj (hpterm.symm.trans hterminal)) ▸ hcTarget
  · intro p hp
    obtain ⟨a, hpa⟩ := hp
    subst p
    obtain ⟨b, hbTarget, hb⟩ := C.targetCofinal a
    obtain ⟨q, hqThread, hqfinish⟩ :=
      DirectedPath.Path.exists_finite_of_terminalCofinal
        (C.spliceChain.thread_nonempty Gamma a) hb
    have hqThread' := hqThread
    obtain ⟨i, hqi, hqinitial⟩ := hqThread
    have hqPure : IsPathBetween Gamma A Gamma.target (Sum.inl q) :=
      C.targetPathPure i (Sum.inl q) hqi b hbTarget (by simpa using hqfinish)
    obtain ⟨r, hr, hrEnds, hrSource⟩ := hqPure
    have hrq : r = q := Sum.inl.inj hr.symm
    subst r
    have hsupport :
        (C.spliceChain.threadLimit Gamma a).support = q.support :=
      support_chainLimit_eq_of_terminalCofinal_of_mem
        (C.spliceChain.thread_nonempty Gamma a)
        (C.spliceChain.thread_isChain Gamma a.1) hb hqThread'
        hqfinish
    have hterminal :
        (C.spliceChain.threadLimit Gamma a).terminal? = some b :=
      DirectedPath.Path.terminal_chainLimit_of_cofinal
        (C.spliceChain.thread Gamma a.1)
        (C.spliceChain.thread_nonempty Gamma a)
        (C.spliceChain.thread_isChain Gamma a.1) hb
    generalize hlimit : C.spliceChain.threadLimit Gamma a = limit
      at hsupport hterminal ⊢
    rcases limit with t | ray
    · have hsupport' : t.support = q.support := by
        change t.support = q.support at hsupport
        exact hsupport
      have htstart : t.start = q.start := by
        calc
          t.start = a.1 := by
            have hi := C.spliceChain.threadLimit_initial Gamma a
            rw [hlimit] at hi
            change t.start = a.1 at hi
            exact hi
          _ = q.start := hqinitial.symm
      have htfinish : t.finish = q.finish := by
        have htb : t.finish = b := Option.some.inj (by simpa using hterminal)
        exact htb.trans hqfinish.symm
      refine ⟨t, rfl, ?_, ?_⟩
      · simpa only [hsupport', htstart, htfinish] using hrEnds
      · simpa only [hsupport', htstart] using hrSource
    · simp at hterminal

/-- The form consumed by the regular extension step: the splice linkage
and its carrier bound are returned together. -/
theorem exists_internal_linkage
    (C : ControlledSpliceChain Gamma L Sigma Z A) :
    ∃ P : Set Gamma.DPath,
      IsLinkageBetween Gamma A Gamma.target P ∧
        Gamma.vertexSet P ⊆ Z := by
  exact ⟨C.spliceChain.limitPaths Gamma,
    C.isLinkageBetween_limitPaths,
    C.vertexSet_limitPaths_subset⟩

end ControlledSpliceChain

/-! ## Construction from a local successor/limit splicing operation -/

/-- The data returned at one stage by the exact slice-splicing operation.
It contains the controlled slice actually used at that stage and the new
partial family, but no global coherence claims. -/
structure StagePayload {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (Sigma : Set (Ladder.Stage kappa)) (Z : Set V) where
  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  scheduled : Set V
  scheduled_subset : scheduled ⊆ L.frontier stageIndex ∩ Z
  scheduled_small : #scheduled < kappa
  nextIndex : Ladder.Stage kappa
  next_mem : nextIndex ∈ Sigma
  index_lt_next : stageIndex < nextIndex
  slice : Set Gamma.DPath
  sliceControlled :
    RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z
      stageIndex nextIndex scheduled slice
  /-- The paths which cease to be literal components of the ladder at this
  stage form a small pending family.  Its terminals are inserted into the
  scheduled set at the next recursive step. -/
  stageMavericks_small :
    #(ControlledSlices.sliceMavericks Gamma (L.warpAt nextIndex) slice) < kappa
  /-- All vertices of the pending family lie in the closing-up set. -/
  stageMavericks_closed :
    Gamma.vertexSet
      (ControlledSlices.sliceMavericks Gamma (L.warpAt nextIndex) slice) ⊆ Z
  family : Set Gamma.DPath

namespace StagePayload

variable {kappa : Cardinal.{u}} {Gamma : DWeb V}
variable {L : Gamma.KappaLadder kappa}
variable {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}

/-- The controlled-slice part of a stage payload is chosen canonically from
`HasControlledSlices`.  The partial family is deliberately a separate
argument: the controlled-slice assertion chooses a slice, but says nothing
about how that slice is spliced onto an earlier family. -/
noncomputable def ofHasControlledSlices
    (hslice : RegularCardinal.HasControlledSlices Sigma L.frontier Z
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support))
    (alpha : Ladder.Stage kappa) (halpha : alpha ∈ Sigma)
    (U : Set V) (hUsub : U ⊆ L.frontier alpha ∩ Z)
    (hU : #U < kappa) (family : Set Gamma.DPath)
    (hstageSmall :
      #(ControlledSlices.sliceMavericks Gamma
        (L.warpAt (RegularCardinal.controlledNext
          hslice alpha halpha U hUsub hU))
        (RegularCardinal.controlledLink
          hslice alpha halpha U hUsub hU)) < kappa)
    (hstageClosed : Gamma.vertexSet
      (ControlledSlices.sliceMavericks Gamma
        (L.warpAt (RegularCardinal.controlledNext
          hslice alpha halpha U hUsub hU))
        (RegularCardinal.controlledLink
          hslice alpha halpha U hUsub hU)) ⊆ Z) :
    StagePayload Gamma L Sigma Z where
  stageIndex := alpha
  stageIndex_mem := halpha
  scheduled := U
  scheduled_subset := hUsub
  scheduled_small := hU
  nextIndex := RegularCardinal.controlledNext
    hslice alpha halpha U hUsub hU
  next_mem := RegularCardinal.controlledNext_mem
    hslice alpha halpha U hUsub hU
  index_lt_next := RegularCardinal.lt_controlledNext
    hslice alpha halpha U hUsub hU
  slice := RegularCardinal.controlledLink
    hslice alpha halpha U hUsub hU
  sliceControlled := RegularCardinal.controlledLink_spec
    hslice alpha halpha U hUsub hU
  stageMavericks_small := hstageSmall
  stageMavericks_closed := hstageClosed
  family := family

end StagePayload

/-- A path is a literal essential finite prefix of the accumulated ladder
warp at `alpha`.  This is the ordinary branch of the Section 9.11 splice
invariant. -/
def StagePrefix {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (alpha : Ladder.Stage kappa) (p : Gamma.DPath) : Prop :=
  ∃ f : DirectedPath.FinitePath Gamma.graph,
    p = .inl f ∧
      (Sum.inl f : Gamma.DPath) ∈
        Gamma.essentialWarpPart (L.warpAt alpha) ∧
      f.finish ∈ L.frontier alpha

/-- Terminals of the stage-relative exceptional paths of one slice. -/
def stageMaverickTerminals {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (beta : Ladder.Stage kappa) (T : Set Gamma.DPath) : Set V :=
  Gamma.terminalFrontier
    (ControlledSlices.sliceMavericks Gamma (L.warpAt beta) T)

/-- The unresolved terminals carried by a payload into the next recursive
step. -/
def StagePayload.pendingTerminals {kappa : Cardinal.{u}}
    {Gamma : DWeb V} {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z : Set V}
    (P : StagePayload Gamma L Sigma Z) : Set V :=
  stageMaverickTerminals Gamma L P.nextIndex P.slice

/-! ### The missing structural condition for successor splicing -/

/-- A slice occupies the ladder annulus from `alpha` to `beta`.

`SliceGood` alone only records endpoint purity.  It does not say that the
interior of the slice has left the strict roof of the old frontier, which is
the condition needed to concatenate it with a partial linkage below that
frontier. -/
def IsAnnularSlice {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (T : Set Gamma.DPath) (alpha beta : Ladder.Stage kappa)
    (U : Set V) : Prop :=
  ControlledSlices.SliceGood Gamma L T alpha beta U ∧
    Gamma.vertexSet T ⊆ L.lowerRegion alpha ∩ L.upperRegion beta

/-- Strengthened form of Assertion 9.15 carrying the geometric fact needed
by the `star`/arrow composition in Assertion 9.11.  This is intentionally a
strengthening of the `Good` predicate, not an assumed completed splice. -/
def HasAnnularControlledSlices {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (Sigma : Set (Ladder.Stage kappa)) (Z : Set V) : Prop :=
  RegularCardinal.HasControlledSlices Sigma L.frontier Z
    (IsAnnularSlice Gamma L)
    (ControlledSlices.sliceMavericks Gamma L.limitWarp)
    (fun p : Gamma.DPath ↦ p.support)

theorem controlledSlice_of_annularControlledSlice
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hT : RegularCardinal.IsControlledSlice
      (IsAnnularSlice Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T) :
    RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T :=
  ⟨hT.1.1, hT.2⟩

/-- Annularity gives exactly the cross-family intersection condition in
Notation 2.5: a family already lying in the old roof can meet the new slice
only on the old frontier. -/
theorem vertexSet_inter_subset_frontier_of_annular
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {U T : Set Gamma.DPath}
    {alpha beta : Ladder.Stage kappa} {S : Set V}
    (hessential : Gamma.essential (L.frontier alpha) = L.frontier alpha)
    (hUroof : Gamma.vertexSet U ⊆ Gamma.roof (L.frontier alpha))
    (hT : IsAnnularSlice Gamma L T alpha beta S) :
    Gamma.vertexSet U ∩ Gamma.vertexSet T ⊆ L.frontier alpha := by
  rintro x ⟨hxU, hxT⟩
  have hxRoof : x ∈ Gamma.roof (L.frontier alpha) := hUroof hxU
  have hxNotStrict : x ∉ Gamma.strictRoof (L.frontier alpha) :=
    hT.2 hxT |>.1
  have hxEssential : x ∈ Gamma.essential (L.frontier alpha) := by
    by_contra hx
    exact hxNotStrict ⟨hxRoof, hx⟩
  exact hessential ▸ hxEssential

/-- Closing under members of the limiting ladder warp.  This is the exact
closure property used for ordinary (non-maverick) slice components. -/
def IsLimitWarpClosed {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa) (Z : Set V) : Prop :=
  ∀ p ∈ L.limitWarp, (p.support ∩ Z).Nonempty → p.support ⊆ Z

/-- Every controlled-slice component which meets the closing set is wholly
inside it: mavericks are registered directly, while an ordinary component
is a fragment of a limiting-ladder path and uses ladder closure. -/
theorem controlledSlice_path_support_subset
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {alpha beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hclosed : IsLimitWarpClosed Gamma L Z)
    (hT : RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta U T)
    {p : Gamma.DPath} (hpT : p ∈ T)
    (hpZ : (p.support ∩ Z).Nonempty) :
    p.support ⊆ Z := by
  by_cases hpM : p ∈
      ControlledSlices.sliceMavericks Gamma L.limitWarp T
  · intro x hxp
    exact hT.2.2 (Set.mem_iUnion.2 ⟨p,
      Set.mem_iUnion.2 ⟨hpM, hxp⟩⟩)
  · have hpOrdinary :
        ControlledSlices.IsLadderFragment Gamma L.limitWarp p := by
      by_contra hp
      exact hpM ⟨hpT, hp⟩
    obtain ⟨q, hqY, hpq⟩ := hpOrdinary
    obtain ⟨x, hxp, hxZ⟩ := hpZ
    exact hpq.1.trans (hclosed q hqY ⟨x, hpq.1 hxp, hxZ⟩)

/-- The concrete arrow operation introduces no vertex outside `Z` when
the old family lies in `Z` and every used controlled-slice component is
closed there.  No global splice family is assumed. -/
theorem vertexSet_arrow_subset_of_controlledSlice
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z Ureq : Set V}
    {alpha beta : Ladder.Stage kappa} {old T : Set Gamma.DPath}
    (hclosed : IsLimitWarpClosed Gamma L Z)
    (hold : Gamma.vertexSet old ⊆ Z)
    (hT : RegularCardinal.IsControlledSlice
      (ControlledSlices.SliceGood Gamma L)
      (ControlledSlices.sliceMavericks Gamma L.limitWarp)
      (fun p : Gamma.DPath ↦ p.support) Z alpha beta Ureq T) :
    Gamma.vertexSet (Gamma.arrow old T) ⊆ Z := by
  rintro x ⟨q, ⟨p, rfl⟩, hxq⟩
  rcases hp : p.1 with f | r
  · have hf : (Sum.inl f : Gamma.DPath) ∈ old := by
      simpa [hp] using p.2
    have peq : p = ⟨Sum.inl f, hf⟩ := Subtype.ext hp
    subst p
    rcases Gamma.arrowPath_finite_cases old T f hf with heq | ⟨c, heq⟩
    · apply hold
      exact ⟨Sum.inl f, hf, by simpa [heq] using hxq⟩
    · rw [heq, DirectedPath.Path.support_appendAt] at hxq
      rcases hxq with hxf | hxs
      · exact hold ⟨Sum.inl f, hf, hxf⟩
      · have hfinishZ : f.finish ∈ Z :=
          hold ⟨Sum.inl f, hf, f.finish_mem_support⟩
        have hcZ : (c.path.support ∩ Z).Nonempty :=
          ⟨f.finish, c.finish_mem, hfinishZ⟩
        exact controlledSlice_path_support_subset hclosed hT
          c.mem_path hcZ
          (c.path.support_suffixFrom_subset f.finish c.finish_mem hxs)
  · have hr : (Sum.inr r : Gamma.DPath) ∈ old := by
      simpa [hp] using p.2
    have peq : p = ⟨Sum.inr r, hr⟩ := Subtype.ext hp
    subst p
    apply hold
    exact ⟨Sum.inr r, hr, by
      simpa [Gamma.arrowPath_ray old T r hr] using hxq⟩

/-- Local proof obligations on the value returned by one invocation of
the splice operation.  `previous` contains only values at strictly earlier
indices.  Thus these are genuine induction-step obligations, rather than
properties postulated of a completed transfinite chain. -/
structure IsValidStage {kappa : Cardinal.{u}}
    {Gamma : DWeb V} {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      StagePayload Gamma L Sigma Z)
    (current : StagePayload Gamma L Sigma Z) : Prop where
  /-- The recursive family is genuinely a partial source--frontier
  linkage at the frontier recorded by this payload.  This field is not
  redundant with `isWarp`: successor compatibility and the direct-limit
  construction need its finite-character and endpoint information. -/
  linkage :
    IsLinkageBetween Gamma A (L.frontier current.nextIndex) current.family
  /-- No member visits its current right frontier before its terminal. -/
  meets_frontier_only_at_terminal : ∀ p ∈ current.family,
    ∀ x ∈ p.support, x ∈ L.frontier current.nextIndex →
      Gamma.terminal? p = some x
  /-- Every current path lies below the frontier to which it is linked.
  This is the compatibility invariant consumed by the next annular star. -/
  vertices_roof : Gamma.vertexSet current.family ⊆
    Gamma.roof (L.frontier current.nextIndex)
  isWarp : Gamma.IsWarp current.family
  initial_subset : Gamma.initialSet current.family ⊆ A
  vertices_closed : Gamma.vertexSet current.family ⊆ Z
  targetPathPure : ∀ p ∈ current.family,
    ∀ b ∈ Gamma.target, p.terminal? = some b →
      IsPathBetween Gamma A Gamma.target p
  /-- Stage coordinates advance beyond every earlier right frontier.  At a
  successor this is equality with the greatest predecessor followed by the
  new controlled slice; at a limit it is the supremum of all earlier right
  frontiers. -/
  previous_index_le : ∀ j (hji : j < i),
    (previous j hji).nextIndex ≤ current.stageIndex
  /-- Every active component is either already completed, is the literal
  ladder prefix at the current right frontier, or is one of the newly
  generated pending mavericks. -/
  path_status : ∀ p ∈ current.family,
    (∃ b ∈ Gamma.target, Gamma.terminal? p = some b) ∨
      StagePrefix Gamma L current.nextIndex p ∨
      ∃ x ∈ current.pendingTerminals, Gamma.terminal? p = some x
  extends_previous : ∀ j (hji : j < i),
    ∀ p ∈ (previous j hji).family,
      ∃ q ∈ current.family, Gamma.Extends p q
  preserves_completed : ∀ j (hji : j < i),
    ∀ p ∈ (previous j hji).family,
      (∃ b ∈ Gamma.target, p.terminal? = some b) →
        p ∈ current.family
  /-- Every pending path from an earlier payload has acquired a
  target-ending extension by the current stage. -/
  resolves_previous_pending : ∀ j (hji : j < i),
    ∀ p ∈ (previous j hji).family,
      (∃ x ∈ (previous j hji).pendingTerminals,
        Gamma.terminal? p = some x) →
      ∃ q ∈ current.family, Gamma.Extends p q ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? q = some b
  realizes_request : ∀ a : A, request i = some a →
    ∃ p ∈ current.family, p.initial = a.1 ∧
      ∃ b ∈ Gamma.target, p.terminal? = some b

/-- An exact local splicing operation.  At a stage it may inspect all
strictly earlier payloads.  Its verification is required only for histories
whose earlier entries already satisfy the same local laws.  Quantifying over
arbitrary histories here would be inconsistent with successor splicing: two
unrelated earlier payloads can contain intersecting paths which no warp can
simultaneously extend.

This is the interface still needed from the component-replacement part of
Assertion 9.11. -/
structure LocalSpliceOperation {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (Sigma : Set (Ladder.Stage kappa)) (Z A : Set V)
    (request : Ladder.Stage kappa → Option A) where
  build : ∀ i : Ladder.Stage kappa,
    (∀ j : Ladder.Stage kappa, j < i →
      StagePayload Gamma L Sigma Z) →
      StagePayload Gamma L Sigma Z
  valid : ∀ i previous,
    (∀ j (hji : j < i),
      IsValidStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) →
      IsValidStage request i previous (build i previous)

namespace LocalSpliceOperation

variable {kappa : Cardinal.{u}} {Gamma : DWeb V}
variable {L : Gamma.KappaLadder kappa}
variable {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
variable {request : Ladder.Stage kappa → Option A}

/-- The payload sequence obtained by well-founded recursion on the stage
ordinal. -/
noncomputable def payload
    (R : LocalSpliceOperation Gamma L Sigma Z A request)
    (i : Ladder.Stage kappa) : StagePayload Gamma L Sigma Z :=
  WellFounded.fix wellFounded_lt
    (fun i previous ↦ R.build i previous) i

theorem payload_eq
    (R : LocalSpliceOperation Gamma L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    R.payload i = R.build i (fun j _hji ↦ R.payload j) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun i previous ↦ R.build i previous) i

theorem payload_valid
    (R : LocalSpliceOperation Gamma L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    IsValidStage request i (fun j _hji ↦ R.payload j) (R.payload i) := by
  rw [R.payload_eq i]
  apply R.valid
  intro j hji
  simpa only using R.payload_valid j
termination_by i.1
decreasing_by exact hji

/-- The recursively constructed partial families, packaged as the growing
chain used by the direct-limit theorem. -/
noncomputable def growingChain
    (R : LocalSpliceOperation Gamma L Sigma Z A request) :
    Gamma.GrowingWarpChain (Ladder.Stage kappa) where
  stage i := (R.payload i).family
  isWarp i := (R.payload_valid i).isWarp
  grows := by
    intro i j hij p hp
    rcases hij.lt_or_eq with hij | rfl
    · exact (R.payload_valid j).extends_previous i hij p hp
    · exact ⟨p, hp, Gamma.extends_refl p⟩

@[simp]
theorem growingChain_stage
    (R : LocalSpliceOperation Gamma L Sigma Z A request)
    (i : Ladder.Stage kappa) :
    (R.growingChain.stage i) = (R.payload i).family :=
  rfl

/-- A covering request enumeration makes the union of the recursively
constructed initial sets exactly `A`. -/
theorem initialUnion_growingChain
    (R : LocalSpliceOperation Gamma L Sigma Z A request)
    (hrequest : ∀ a : A, ∃ i, request i = some a) :
    R.growingChain.initialUnion = A := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact (R.payload_valid i).initial_subset hxi
  · intro x hx
    let a : A := ⟨x, hx⟩
    obtain ⟨i, hi⟩ := hrequest a
    obtain ⟨p, hp, hpinitial, _⟩ :=
      (R.payload_valid i).realizes_request a hi
    exact Set.mem_iUnion.2 ⟨i, p, hp, hpinitial⟩

/-- The local preservation law implies target cofinality of every source
thread.  A common later club point compares an arbitrary thread member with
the completed member introduced when that source was requested. -/
theorem targetCofinal_growingChain
    (R : LocalSpliceOperation Gamma L Sigma Z A request)
    (hkappa : kappa.IsRegular)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hrequest : ∀ a : A, ∃ i, request i = some a)
    (a : R.growingChain.initialUnion) :
    ∃ b ∈ Gamma.target,
      DirectedPath.Path.TerminalCofinal
        (R.growingChain.thread Gamma a.1) b := by
  have haA : a.1 ∈ A := by
    simpa only [R.initialUnion_growingChain hrequest] using a.2
  let aA : A := ⟨a.1, haA⟩
  obtain ⟨i, hi⟩ := hrequest aA
  obtain ⟨p, hp, hpinitial, b, hbTarget, hpterm⟩ :=
    (R.payload_valid i).realizes_request aA hi
  refine ⟨b, hbTarget, ?_⟩
  intro q hqThread
  obtain ⟨j, hqj, hqinitial⟩ := hqThread
  let k := RegularCardinal.aboveInClub hkappa Sigma hSigma i j
  have hik : i < k :=
    RegularCardinal.left_lt_aboveInClub hkappa Sigma hSigma i j
  have hjk : j < k :=
    RegularCardinal.right_lt_aboveInClub hkappa Sigma hSigma i j
  have hpk : p ∈ (R.payload k).family :=
    (R.payload_valid k).preserves_completed i hik p hp
      ⟨b, hbTarget, hpterm⟩
  obtain ⟨r, hrk, hqr⟩ :=
    (R.payload_valid k).extends_previous j hjk q hqj
  have hrinitial : r.initial = a.1 :=
    (Gamma.extends_initial hqr).symm.trans hqinitial
  have hrp : r = p :=
    DWeb.IsWarp.eq_of_initial_eq Gamma (R.payload_valid k).isWarp
      hrk hpk (hrinitial.trans hpinitial.symm)
  refine ⟨p, ⟨k, hpk, hpinitial⟩, ?_, hpterm⟩
  exact hrp ▸ hqr

/-- A verified local splicing operation constructs the full global
`ControlledSpliceChain`; neither a global chain nor target cofinality is a
premise. -/
noncomputable def toControlledSpliceChain
    (R : LocalSpliceOperation Gamma L Sigma Z A request)
    (hkappa : kappa.IsRegular)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hrequest : ∀ a : A, ∃ i, request i = some a) :
    ControlledSpliceChain Gamma L Sigma Z A where
  stageIndex i := (R.payload i).stageIndex
  stageIndex_mem i := (R.payload i).stageIndex_mem
  scheduled i := (R.payload i).scheduled
  scheduled_subset i := (R.payload i).scheduled_subset
  scheduled_small i := (R.payload i).scheduled_small
  nextIndex i := (R.payload i).nextIndex
  slice i := (R.payload i).slice
  next_mem i := (R.payload i).next_mem
  index_lt_next i := (R.payload i).index_lt_next
  sliceControlled i := (R.payload i).sliceControlled
  spliceChain := R.growingChain
  initialUnion_eq := R.initialUnion_growingChain hrequest
  vertices_closed i := (R.payload_valid i).vertices_closed
  targetPathPure i := (R.payload_valid i).targetPathPure
  targetCofinal := R.targetCofinal_growingChain hkappa hSigma hrequest

/-- Constructor form of Assertion 9.11 from the exact local splicing
operation. -/
theorem exists_internal_linkage_of_localSpliceOperation
    (R : LocalSpliceOperation Gamma L Sigma Z A request)
    (hkappa : kappa.IsRegular)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hrequest : ∀ a : A, ∃ i, request i = some a) :
    ∃ P : Set Gamma.DPath,
      IsLinkageBetween Gamma A Gamma.target P ∧
        Gamma.vertexSet P ⊆ Z := by
  exact (R.toControlledSpliceChain hkappa hSigma hrequest).exists_internal_linkage

end LocalSpliceOperation

end SliceSplice
end CardinalInduction
end Erdos599
