/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.PopularAuxiliary
import ErdosProblems.Erdos599.PopularLayers
import ErdosProblems.Erdos599.RelationalRoof
import ErdosProblems.Erdos599.LambdaAlternating

/-!
# The switching controls in the popular-separator argument

This file contains the representation-independent parts of Aharoni--Berger,
Assertions 8.18--8.22.  There are three points at which the printed proof
uses more than informal path notation:

* a stationary in-fan cannot be distributed among earlier countable ladder
  paths (Assertion 8.19);
* if every member of an in-fan reaches the popular cut, cutting at its first
  visit produces an honest disjoint warp (the selection step in Assertion
  8.20);
* an avoiding path from the source cannot end at a vertex from which the
  target is still reachable while avoiding the separator (the path-splicing
  core of Assertion 8.21).

The final section packages the pruning step of Assertion 8.22: a finite
source--cut warp covering a separating cut is a wave in the original web.
The Lambda-to-alternating decoder supplies the hypotheses of these lemmas in
the Section 8 application.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace PopularSwitching

open DirectedPath Stationary

universe u

variable {V : Type u}

/-! ## Countable traces of ladder paths in `Lambda` -/

/-- All auxiliary gadgets belonging to one original ladder path: its old
vertices and the vertices representing its directed edges.  This is the
countable collision set used when pressing down in Assertion 8.19. -/
def ladderTrace {I : Type*} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I) (p : Gamma.DPath) :
    Set (PopularAuxiliary.Input.LambdaVertex V I) :=
  PopularAuxiliary.Input.LambdaVertex.old '' p.support ∪
    (fun e : V × V ↦
      PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2) '' p.edgeSet

/-- Every admitted ladder path is finite or a ray, hence its full gadget
trace in `Lambda` is countable.  This is the corrected countable (rather
than finite) estimate in Assertion 8.19. -/
theorem ladderTrace_countable {I : Type*} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I) (p : Gamma.DPath) :
    (ladderTrace L p).Countable := by
  have hsupport : p.support.Countable := p.support_countable
  have hedge : p.edgeSet.Countable :=
    (hsupport.prod hsupport).mono p.edgeSet_subset_support_prod
  exact (hsupport.image _).union (hedge.image _)

@[simp]
theorem old_mem_ladderTrace_iff {I : Type u} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I) (p : Gamma.DPath) (x : V) :
    PopularAuxiliary.Input.LambdaVertex.old x ∈ ladderTrace L p ↔
      x ∈ p.support := by
  simp [ladderTrace]

@[simp]
theorem edge_mem_ladderTrace_iff {I : Type u} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I) (p : Gamma.DPath) (x y : V) :
    PopularAuxiliary.Input.LambdaVertex.edge x y ∈ ladderTrace L p ↔
      (x, y) ∈ p.edgeSet := by
  simp [ladderTrace]

@[simp]
theorem proxy_not_mem_ladderTrace {I : Type u} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I) (p : Gamma.DPath) (i : I) :
    PopularAuxiliary.Input.LambdaVertex.proxy i ∉ ladderTrace L p := by
  simp [ladderTrace]

/-- Distinct members of the reference warp have disjoint auxiliary traces.
This is the tagged-vertex form of the fact that ladder components are
vertex-disjoint. -/
theorem ladderTrace_disjoint {I : Type u} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I) {p q : Gamma.DPath}
    (hp : p ∈ L.ladder.paths) (hq : q ∈ L.ladder.paths) (hpq : p ≠ q) :
    Disjoint (ladderTrace L p) (ladderTrace L q) := by
  rw [Set.disjoint_left]
  intro a hap haq
  cases a with
  | old x =>
      exact hpq (_root_.Erdos599.Alternating.DWeb.IsWarp.eq_of_mem_support
        L.ladder.disjoint hp hq
        ((old_mem_ladderTrace_iff L p x).1 hap)
        ((old_mem_ladderTrace_iff L q x).1 haq))
  | edge x y =>
      have hep := (edge_mem_ladderTrace_iff L p x y).1 hap
      have heq := (edge_mem_ladderTrace_iff L q x y).1 haq
      exact hpq (_root_.Erdos599.Alternating.DWeb.IsWarp.eq_of_mem_support
        L.ladder.disjoint hp hq
        (p.edgeSet_subset_support_prod hep).1
        (q.edgeSet_subset_support_prod heq).1)
  | proxy i => exact (proxy_not_mem_ladderTrace L p i) hap

/-- Reference-warp components whose auxiliary traces are touched by `Q`. -/
def ladderPathsMetBy {I : Type u} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I)
    (Q : FinitePath L.lambda.graph) : Set Gamma.DPath :=
  {p | p ∈ L.ladder.paths ∧ (Q.support ∩ ladderTrace L p).Nonempty}

/-- A finite auxiliary path meets only finitely many pairwise-disjoint
reference-warp components. -/
theorem ladderPathsMetBy_finite {I : Type u} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I)
    (Q : FinitePath L.lambda.graph) :
    (ladderPathsMetBy L Q).Finite := by
  apply FamilyTools.finite_of_pairwiseDisjoint_of_meets
    (I := ladderPathsMetBy L Q)
    (F := fun p : Gamma.DPath ↦ ladderTrace L p) (S := Q.support)
  · intro p hp q hq hpq
    exact ladderTrace_disjoint L hp.1 hq.1 hpq
  · exact Q.support_finite
  · intro p hp
    obtain ⟨x, hxQ, hxp⟩ := hp.2
    exact ⟨x, hxQ, hxp⟩

/-- The complete auxiliary trace of all ladder components touched by `Q`.
This is the recursive forbidden set in condition (a) of Assertion 8.22. -/
def metLadderTrace {I : Type u} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I)
    (Q : FinitePath L.lambda.graph) :
    Set (PopularAuxiliary.Input.LambdaVertex V I) :=
  ⋃ p ∈ ladderPathsMetBy L Q, ladderTrace L p

theorem metLadderTrace_countable {I : Type u} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I)
    (Q : FinitePath L.lambda.graph) :
    (metLadderTrace L Q).Countable := by
  exact (ladderPathsMetBy_finite L Q).countable.biUnion fun p _ ↦
    ladderTrace_countable L p

theorem ladderTrace_subset_metLadderTrace_of_meets
    {I : Type u} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I)
    (Q : FinitePath L.lambda.graph) {p : Gamma.DPath}
    (hp : p ∈ L.ladder.paths)
    (hmeet : (Q.support ∩ ladderTrace L p).Nonempty) :
    ladderTrace L p ⊆ metLadderTrace L Q := by
  intro x hx
  simp only [metLadderTrace, Set.mem_iUnion]
  exact ⟨p, ⟨hp, hmeet⟩, hx⟩

/-! ## Restricting joined families -/

/-- Restrict a joined family to an arbitrary subfamily. -/
def restrictPaths {Gamma : DWeb V} {S : Set V}
    (F : Popular.JoinedFamily Gamma S) (P : Set (FinitePath Gamma.graph)) :
    Popular.JoinedFamily Gamma S where
  paths := F.paths ∩ P
  starts_in_source hp := F.starts_in_source hp.1
  ends_in_join hp := F.ends_in_join hp.1
  join_only_at_end hp := F.join_only_at_end hp.1
  joined := by
    intro p hp q hq hpq
    exact F.joined hp.1 hq.1 hpq

@[simp]
theorem mem_restrictPaths
    {Gamma : DWeb V} {S : Set V} (F : Popular.JoinedFamily Gamma S)
    (P : Set (FinitePath Gamma.graph)) (p : FinitePath Gamma.graph) :
    p ∈ (restrictPaths F P).paths ↔ p ∈ F.paths ∧ p ∈ P :=
  Iff.rfl

/-! ## Assertion 8.18: refining an already separating frontier -/

/-- If `T` separates the source from the target, and `B` meets every
source--`T` path, then `B` is itself a source--target separator.

This is the formal reduction at the start of Assertion 8.18.  In the
Section 8 application `T` is the terminal frontier of the essential limit
warp and `B = C_V ∪ BL`; the alternating escape argument establishes the
second premise. -/
theorem isSeparator_of_meets_paths_to_separator
    {Gamma : DWeb V} {T B : Set V}
    (hT : Popular.IsSeparator Gamma T)
    (hB : ∀ p : FinitePath Gamma.graph,
      p.start ∈ Gamma.source → p.finish ∈ T → Gamma.Meets p B) :
    Popular.IsSeparator Gamma B := by
  intro p hstart hfinish
  have hmeetT : p.walk.Meets T := hT p hstart hfinish
  let q := p.firstHit T hmeetT
  obtain ⟨x, hxq, hxB⟩ := hB q hstart (p.firstHit_finish_mem T hmeetT)
  exact ⟨x, p.firstHit_support_subset T hmeetT hxq, hxB⟩

/-! ## Assertion 8.19: regressive countable collisions -/

/-- The abstract form of Assertion 8.19.

For every path of the in-fan, `rank` records the earlier obstruction stage
of a hanging ladder path which it meets, and `collision i` is the support of
the ladder path at stage `i`.  Pressing down makes `rank` constant on a
stationary set.  The resulting subfamily meets one fixed countable set away
from its join set, contradicting joinedness.

Stating the rank on initial indices, rather than on paths, makes explicit the
well-definedness supplied in the application by injectivity of the auxiliary
source chronology. -/
theorem initialIndices_nonstationary_of_regressive_countable_collisions
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed Gamma kappa) {S : Set V}
    (F : Popular.JoinedFamily Gamma S)
    (rank : Below kappa → Below kappa)
    (collision : Below kappa → Set V)
    (hrank : IsRegressiveOn
      (Popular.initialIndicesOf U F.paths F.starts_in_source) rank)
    (hcountable : ∀ i, (collision i).Countable)
    (hdisjoint : ∀ i, Disjoint (collision i) S)
    (hmeet : ∀ p (hp : p ∈ F.paths),
      ∃ x ∈ collision (rank (U.f ⟨p.start, F.starts_in_source hp⟩)),
        x ∈ p.support) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U F.paths F.starts_in_source) := by
  intro hstationary
  obtain ⟨i, hi⟩ := pressingDown U.uncountable U.regular hstationary hrank
  let P : Set (FinitePath Gamma.graph) :=
    {p | ∃ hp : p ∈ F.paths,
      rank (U.f ⟨p.start, F.starts_in_source hp⟩) = i}
  let Fi : Popular.JoinedFamily Gamma S := restrictPaths F P
  have hmeet_i : ∀ p ∈ Fi.paths, ∃ x ∈ collision i, x ∈ p.support := by
    intro p hp
    obtain ⟨hpF, hpP⟩ := hp
    obtain ⟨hpF', hrankp⟩ := hpP
    obtain ⟨x, hxc, hxp⟩ := hmeet p hpF
    have hsource :
        (⟨p.start, F.starts_in_source hpF⟩ : Gamma.source) =
          ⟨p.start, F.starts_in_source hpF'⟩ := Subtype.ext rfl
    refine ⟨x, ?_, hxp⟩
    simpa only [hsource, hrankp] using hxc
  have hnonstationary :
      ¬ IsStationaryBelow kappa
        (Popular.initialIndicesOf U Fi.paths Fi.starts_in_source) :=
    PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
      U Fi (hcountable i) (hdisjoint i) hmeet_i
  apply hnonstationary
  apply hi.mono
  rintro a ⟨ha, hra⟩
  obtain ⟨p, hp, hpa⟩ := ha
  have hpP : p ∈ P := by
    refine ⟨hp, ?_⟩
    exact (congrArg rank hpa).trans hra
  refine ⟨p, ⟨hp, hpP⟩, ?_⟩
  have hsource :
      (⟨p.start, Fi.starts_in_source ⟨hp, hpP⟩⟩ : Gamma.source) =
        ⟨p.start, F.starts_in_source hp⟩ := Subtype.ext rfl
  exact (congrArg U.f hsource).trans hpa

/-! ## Assertion 8.20: first-hit selection at the popular cut -/

/-- A first-hit prefix of a normalized joined path does not meet the old
join set when the new cut is disjoint from that join set. -/
theorem firstHit_support_disjoint_join
    {Gamma : DWeb V} {S C : Set V}
    (F : Popular.JoinedFamily Gamma S) (hCS : Disjoint C S)
    {p : FinitePath Gamma.graph} (hp : p ∈ F.paths)
    (hmeet : p.walk.Meets C) :
    Disjoint (p.firstHit C hmeet).support S := by
  rw [Set.disjoint_left]
  intro x hxq hxS
  have hxfinish : x = p.finish :=
    Set.mem_singleton_iff.1 (F.join_only_at_end hp ⟨
      p.firstHit_support_subset C hmeet hxq, hxS⟩)
  have hpfinish :
      p.walk.support.getLast p.walk.support_ne_nil = p.finish :=
    p.walk.getLast_support
  have hprefix :
      (p.firstHit C hmeet).walk.support <+: p.walk.support :=
    (p.walk.firstHit C hmeet).support_prefix
  have hwhole : (p.firstHit C hmeet).walk.support = p.walk.support := by
    apply List.Nodup.eq_of_getLast_mem_of_prefix hprefix
    · rw [hpfinish]
      exact hxfinish ▸ hxq
    · exact p.isPath
  have hnewFinish : (p.firstHit C hmeet).finish = p.finish := by
    have hqfinish :
        (p.firstHit C hmeet).walk.support.getLast
            (p.firstHit C hmeet).walk.support_ne_nil =
          (p.firstHit C hmeet).finish :=
      (p.firstHit C hmeet).walk.getLast_support
    calc
      (p.firstHit C hmeet).finish =
          (p.firstHit C hmeet).walk.support.getLast
            (p.firstHit C hmeet).walk.support_ne_nil := hqfinish.symm
      _ = p.walk.support.getLast p.walk.support_ne_nil :=
        List.getLast_congr _ _ hwhole
      _ = p.finish := hpfinish
  exact Set.disjoint_left.1 hCS
    (p.firstHit_finish_mem C hmeet) (hnewFinish ▸ F.ends_in_join hp)

/-- Cut every member of a joined family at its first visit to `C`.
Because `C` misses the join set, the resulting prefixes are genuinely
vertex-disjoint. -/
def firstHitWarp
    {Gamma : DWeb V} {S C : Set V}
    (F : Popular.JoinedFamily Gamma S)
    (hCS : Disjoint C S)
    (hmeet : ∀ p, p ∈ F.paths → p.walk.Meets C) :
    Popular.XSWarp Gamma C where
  paths := Set.range fun p : F.paths ↦ p.1.firstHit C (hmeet p.1 p.2)
  disjoint := by
    rintro q ⟨p, rfl⟩ r ⟨p', rfl⟩ hqr
    change Disjoint
      (p.1.firstHit C (hmeet p.1 p.2)).support
      (p'.1.firstHit C (hmeet p'.1 p'.2)).support
    rw [Set.disjoint_left]
    intro x hxq hxr
    have hpp' : p.1 ≠ p'.1 := by
      intro hpp
      apply hqr
      exact congrArg
        (fun z : F.paths ↦ z.1.firstHit C (hmeet z.1 z.2))
        (Subtype.ext hpp)
    have hxS : x ∈ S := F.joined p.2 p'.2 hpp' ⟨
      p.1.firstHit_support_subset C (hmeet p.1 p.2) hxq,
      p'.1.firstHit_support_subset C (hmeet p'.1 p'.2) hxr⟩
    exact Set.disjoint_left.1
      (firstHit_support_disjoint_join F hCS p.2 (hmeet p.1 p.2)) hxq hxS
  starts_in_source := by
    rintro q ⟨p, rfl⟩
    change p.1.start ∈ Gamma.source
    exact F.starts_in_source p.2
  ends_in_target := by
    rintro q ⟨p, rfl⟩
    exact p.1.firstHit_finish_mem C (hmeet p.1 p.2)

/-- Cutting at the first visit to `C` retains every initial ordinal index. -/
theorem initialIndices_subset_firstHitWarp
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed Gamma kappa) {S C : Set V}
    (F : Popular.JoinedFamily Gamma S)
    (hCS : Disjoint C S)
    (hmeet : ∀ p, p ∈ F.paths → p.walk.Meets C) :
    Popular.initialIndicesOf U F.paths F.starts_in_source ⊆
      Popular.initialIndicesOf U (firstHitWarp F hCS hmeet).paths
        (firstHitWarp F hCS hmeet).starts_in_source := by
  rintro a ⟨p, hp, hpa⟩
  let q := p.firstHit C (hmeet p hp)
  have hq : q ∈ (firstHitWarp F hCS hmeet).paths := ⟨⟨p, hp⟩, rfl⟩
  refine ⟨q, hq, ?_⟩
  have hsource :
      (⟨q.start, (firstHitWarp F hCS hmeet).starts_in_source hq⟩ :
          Gamma.source) =
        ⟨p.start, F.starts_in_source hp⟩ := Subtype.ext rfl
  exact (congrArg U.f hsource).trans hpa

/-- Assertion 8.20 in its cut-selection form.  If every path of an in-fan
meets a cut disjoint from the apex, then stationarity would make that cut
strongly popular. -/
theorem initialIndices_nonstationary_of_all_meet_notStronglyPopular
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed Gamma kappa) {S C : Set V}
    (F : Popular.JoinedFamily Gamma S)
    (hCS : Disjoint C S)
    (hmeet : ∀ p, p ∈ F.paths → p.walk.Meets C)
    (hC : ¬ Popular.IsStronglyPopular U C) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U F.paths F.starts_in_source) := by
  intro hF
  apply hC
  exact ⟨firstHitWarp F hCS hmeet,
    hF.mono (initialIndices_subset_firstHitWarp U F hCS hmeet)⟩

/-- The selected auxiliary paths in Assertion 8.22 form a warp to a subset
of the popular separator.  Non-strong-popularity therefore makes their
initial-index set nonstationary. -/
theorem initialIndices_nonstationary_of_warp_to_subset
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed Gamma kappa) {T C : Set V}
    (P : Popular.XSWarp Gamma T) (hTC : T ⊆ C)
    (hC : ¬ Popular.IsStronglyPopular U C) :
    ¬ IsStationaryBelow kappa
      (Popular.initialIndicesOf U P.paths P.starts_in_source) := by
  intro hP
  exact hC ⟨P.mono hTC, hP⟩

/-! ## Assertion 8.21: splicing an avoiding prefix to an escape -/

/-- Concatenating two avoiding paths and erasing loops produces an avoiding
path with the same outer endpoints. -/
theorem exists_avoiding_path_of_avoiding_paths
    {Gamma : DWeb V} {C : Set V}
    (p q : FinitePath Gamma.graph) (hpq : p.finish = q.start)
    (hp : Gamma.Avoids p C) (hq : Gamma.Avoids q C) :
    ∃ r : FinitePath Gamma.graph,
      r.start = p.start ∧ r.finish = q.finish ∧ Gamma.Avoids r C := by
  let qwalk : Walk Gamma.graph p.finish q.finish :=
    RelationalRoof.castStart Gamma.graph.Adj hpq.symm q.walk
  let w : Walk Gamma.graph p.start q.finish := p.walk.append qwalk
  obtain ⟨r, hr⟩ :=
    RelationalRoof.exists_pathTo_support_subset (R := Gamma.graph.Adj) w
  let r' : FinitePath Gamma.graph :=
    { start := p.start
      finish := q.finish
      walk := r.1
      isPath := r.2 }
  refine ⟨r', rfl, rfl, ?_⟩
  change Disjoint r'.support C
  rw [Set.disjoint_left]
  intro x hxr hxC
  have hxw : x ∈ w.support := hr hxr
  have hxappend : x ∈ p.walk.support ++ qwalk.support.tail := by
    simpa [w, Walk.support_append] using hxw
  rcases List.mem_append.mp hxappend with hxp | hxq
  · exact Set.disjoint_left.1 hp hxp hxC
  · have hxq' : x ∈ q.support := by
      change x ∈ q.walk.support
      simpa [qwalk] using List.mem_of_mem_tail hxq
    exact Set.disjoint_left.1 hq hxq' hxC

/-- A separator forbids a `C`-avoiding source prefix from ending in the
escape region.  This is precisely the shortcutting argument used in
Assertion 8.21, isolated from the order notation on ladder fragments. -/
theorem separator_forbids_avoiding_prefix_to_escape
    {Gamma : DWeb V} {C : Set V}
    (hC : Popular.IsSeparator Gamma C)
    (p : FinitePath Gamma.graph) (hstart : p.start ∈ Gamma.source)
    (hav : Gamma.Avoids p C) :
    p.finish ∉ {v | Gamma.CanReachTargetAvoiding C v} := by
  rintro ⟨q, hqtarget, hqavoid⟩
  obtain ⟨r, hrstart, hrfinish, hravoid⟩ :=
    exists_avoiding_path_of_avoiding_paths p q hqtarget.1.symm hav hqavoid
  have hmeet := hC r (hrstart ▸ hstart) (hrfinish ▸ hqtarget.2)
  exact (Gamma.avoids_iff_not_meets r C).1 hravoid hmeet

/-- Literal `Lambda` specialization of Assertion 8.21: the old endpoint of
a cut-avoiding auxiliary path from `X` is not in `RR`. -/
theorem lambda_old_finish_not_mem_ordinaryEscapeRegion
    {I : Type*} {Gamma : DWeb V}
    (L : PopularAuxiliary.Input Gamma I)
    (C : Set (PopularAuxiliary.Input.LambdaVertex V I))
    (hC : Popular.IsSeparator L.lambda C)
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (hav : L.lambda.Avoids p C) {v : V}
    (hfinish : p.finish = .old v) :
    v ∉ {v | L.lambda.CanReachTargetAvoiding C (.old v)} := by
  intro hv
  apply separator_forbids_avoiding_prefix_to_escape hC p hstart hav
  change L.lambda.CanReachTargetAvoiding C p.finish
  change L.lambda.CanReachTargetAvoiding C (.old v) at hv
  simpa only [hfinish] using hv

/-- Removing a nonstationary set from a stationary set leaves a stationary
set below a regular uncountable cardinal.  This is the stationary-ideal
calculation at the end of Assertion 8.22. -/
theorem stationary_diff_of_stationary_of_nonstationary
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) {S N : Set (Below kappa)}
    (hS : IsStationaryBelow kappa S)
    (hN : ¬ IsStationaryBelow kappa N) :
    IsStationaryBelow kappa (S \ N) := by
  by_contra hdiff
  let F : Bool → Set (Below kappa)
    | false => N
    | true => S \ N
  have hF : ∀ b, ¬ IsStationaryBelow kappa (F b) := by
    intro b
    cases b
    · exact hN
    · exact hdiff
  have hunion : ¬ IsStationaryBelow kappa (⋃ b, F b) :=
    not_isStationaryBelow_iUnion_of_countable hregular huncountable hF
  apply hunion
  apply hS.mono
  intro x hxS
  by_cases hxN : x ∈ N
  · exact Set.mem_iUnion.2 ⟨false, hxN⟩
  · exact Set.mem_iUnion.2 ⟨true, ⟨hxS, hxN⟩⟩

/-! ## Assertion 8.22: pruning to a separating frontier -/

/-- Regard a finite warp as a family of finite-or-infinite paths. -/
def pathFamily {Gamma : DWeb V} {S : Set V}
    (P : Popular.XSWarp Gamma S) : Set Gamma.DPath :=
  Sum.inl '' P.paths

theorem pathFamily_isWarp
    {Gamma : DWeb V} {S : Set V} (P : Popular.XSWarp Gamma S) :
    Gamma.IsWarp (pathFamily P) := by
  rintro p ⟨q, hq, rfl⟩ r ⟨s, hs, rfl⟩ hne
  exact P.disjoint hq hs (fun hqs ↦ hne (congrArg Sum.inl hqs))

theorem pathFamily_initialSet_subset
    {Gamma : DWeb V} {S : Set V} (P : Popular.XSWarp Gamma S) :
    Gamma.initialSet (pathFamily P) ⊆ Gamma.source := by
  rintro x ⟨p, ⟨q, hq, hpq⟩, hpx⟩
  cases hpq
  exact hpx ▸ P.starts_in_source hq

theorem pathFamily_terminalFrontier_subset
    {Gamma : DWeb V} {S : Set V} (P : Popular.XSWarp Gamma S) :
    Gamma.terminalFrontier (pathFamily P) ⊆ S := by
  rintro x ⟨p, ⟨q, hq, hpq⟩, hpx⟩
  cases hpq
  exact Option.some.inj hpx ▸ P.ends_in_target hq

theorem pathFamily_terminalFrontier_eq
    {Gamma : DWeb V} {S : Set V} (P : Popular.XSWarp Gamma S)
    (hcovers : ∀ s ∈ S, ∃ p ∈ P.paths, p.finish = s) :
    Gamma.terminalFrontier (pathFamily P) = S := by
  apply Set.Subset.antisymm (pathFamily_terminalFrontier_subset P)
  intro s hs
  obtain ⟨p, hp, hps⟩ := hcovers s hs
  exact ⟨.inl p, ⟨p, hp, rfl⟩, congrArg some hps⟩

/-- A finite source--`S` warp covering a separating set `S` is the pruned
wave produced in Assertion 8.22. -/
theorem pathFamily_isWave
    {Gamma : DWeb V} {S : Set V} (P : Popular.XSWarp Gamma S)
    (hcovers : ∀ s ∈ S, ∃ p ∈ P.paths, p.finish = s)
    (hseparator : Popular.IsSeparator Gamma S) :
    Gamma.IsWave (pathFamily P) := by
  refine ⟨pathFamily_isWarp P, pathFamily_initialSet_subset P, ?_⟩
  intro a ha p hp
  have hmeet : (p.support ∩ S).Nonempty :=
    hseparator p (hp.1 ▸ ha) hp.2
  rw [pathFamily_terminalFrontier_eq P hcovers]
  exact hmeet

end PopularSwitching
end Erdos599
