/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GlobalBlueprintReplacement
import ErdosProblems.Erdos599.HalfwayInitialBlueprint
import ErdosProblems.Erdos599.HalfwayFrontierHeight
import ErdosProblems.Erdos599.HeightRoofBridge

/-!
# The terminal scheduler and its final certificate

There are two sound ways to finish the blueprint construction in Section 9.

* A literal-path recursion may use Assertion 9.33 through
  `stableLimitConclusion_limit_of_monotone`.  Literal monotonicity is an
  essential hypothesis of this representation: pairwise `RealExtends` alone
  does not rule out a reverse ray at a countable limit.
* A simultaneous construction may instead build one well-founded forward
  orientation and use its root-orbit decomposition.  This is the global
  replacement lane and does not pass through a liminf.

This file packages both lanes and, in each case, exports the same concrete
`GloballyResolvedBlueprintCertificate`.  In particular, the common terminal
frontier, quotient-unhinderedness, and the height witness are retained all
the way to `HalfwayClauseAt`; none of them is hidden in a proposed linkage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace HalfwayScheduler

open DirectedPath
open Blueprint
open Blueprint.LinkageBlueprint
open Alternating
open Alternating.RelationDecomposition

universe u v

variable {V : Type u}

/-! ## The literal-path 9.33 lane -/

/-- A fair terminal run to which the concrete liminf theorem for Assertion
9.33 applies.  The run records only construction invariants.  In particular,
it does not contain a half-way linkage or a globally resolved certificate.

`paths_monotone` is deliberately explicit.  The weaker condition that the
stages pairwise `RealExtends` one another is not sufficient for the concrete
`limit` representation: at countable cofinality, completed finite paths may
grow backwards and form a reverse ray in the union. -/
structure LiteralFairStableRun (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (kappa : Cardinal.{u}) (T Z persistent B : Set V) (I : Type v)
    [Preorder I] [Nonempty I] [IsDirectedOrder I] where
  stage : I → LinkageBlueprint Gamma Y kappa
  scheduled : I → V
  paths_monotone : Monotone fun i ↦ (stage i).paths
  union_card : #(⋃ i, (stage i).paths) ≤ kappa
  reference_isWarp : Gamma.IsWarp Y
  isBlueprint : ∀ i, (stage i).IsLinkageBlueprint T Z persistent
  stable : ∀ i, (stage i).Stable T persistent
  fair : ∀ x ∈ (LinkageBlueprint.limit stage).realPart.terminals,
    x ∉ B → ∃ i, scheduled i = x
  resolved : ∀ i, (stage i).RealLinksTo (scheduled i) B
  final_edges_real :
    (LinkageBlueprint.limit stage).familyGraph.edges ⊆
      {e | Gamma.graph.Adj e.1 e.2}

variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {T Z persistent B : Set V}
variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- Assertion 9.33 for a literal fair run. -/
theorem LiteralFairStableRun.stableLimit
    (R : LiteralFairStableRun Gamma Y kappa T Z persistent B I) :
    StableLimitConclusion R.stage (LinkageBlueprint.limit R.stage)
      T Z persistent B :=
  stableLimitConclusion_limit_of_monotone R.stage T Z persistent B
    R.paths_monotone R.union_card R.reference_isWarp R.isBlueprint R.stable

/-- The literal fair run supplies the exact terminal-chain interface used by
the final conversion theorem. -/
def LiteralFairStableRun.terminalScheduledChain
    (R : LiteralFairStableRun Gamma Y kappa T Z persistent B I) :
    TerminalScheduledChain I R.stage (LinkageBlueprint.limit R.stage) B where
  scheduled := R.scheduled
  absorbed := fun i ↦ (R.stableLimit.2.2 i).realPart_extends
  fair := R.fair
  resolved := R.resolved
  real_limit := R.final_edges_real

/-- The remaining geometric information at the end of the scheduler.  The
source-cover equality is not a field: it is derived from the final blueprint
condition and endpoint purity. -/
structure LiteralFinalGeometry
    (R : LiteralFairStableRun Gamma Y kappa T Z persistent Gamma.target I)
    (A0 : Set V) where
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  designated_source : A0 ⊆ Gamma.source
  designated_initial :
    A0 ⊆ (LinkageBlueprint.limit R.stage).initialSet
  terminal_frontier :
    (LinkageBlueprint.limit R.stage).terminalSet ∪
      Gamma.terminalFrontier
        ((LinkageBlueprint.limit R.stage).referenceRemainder T) =
      stopover
  blueprint_endpointPure :
    ∀ p ∈ (LinkageBlueprint.limit R.stage).paths,
      (LinkageBlueprint.limit R.stage).IsPathBetween
        Gamma.source stopover p
  reference_endpointPure :
    ∀ p ∈ (LinkageBlueprint.limit R.stage).referenceRemainder T,
      CardinalInduction.IsPathBetween Gamma Gamma.source stopover p
  stopover_separator : IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave :
    (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

/-- A fair literal scheduler plus its final frontier/height geometry gives
the common globally resolved construction certificate. -/
def LiteralFinalGeometry.certificate
    {R : LiteralFairStableRun Gamma Y kappa T Z persistent Gamma.target I}
    {A0 : Set V} (F : LiteralFinalGeometry R A0) :
    GloballyResolvedBlueprintCertificate Gamma A0 kappa where
  reference := Y
  blueprint := LinkageBlueprint.limit R.stage
  slice := T
  stopover := F.stopover
  heightDelete := F.heightDelete
  heightWave := F.heightWave
  reference_isWarp := R.reference_isWarp
  edge_real := R.final_edges_real
  real_terminals_target := R.terminalScheduledChain.final_terminals_subset
  designated_source := F.designated_source
  designated_initial := F.designated_initial
  source_cover :=
    (LinkageBlueprint.limit R.stage).initialSet_union_referenceRemainder_eq_source
      T R.stableLimit.1.covers_source F.blueprint_endpointPure
        F.reference_endpointPure
  terminal_frontier := F.terminal_frontier
  blueprint_endpointPure := F.blueprint_endpointPure
  reference_endpointPure := F.reference_endpointPure
  stopover_separator := F.stopover_separator
  stopover_trimmed := F.stopover_trimmed
  quotient_unhindered := F.quotient_unhindered
  heightDelete_nonSource := F.heightDelete_nonSource
  heightWave_isWave := F.heightWave_isWave
  stopover_roofed := F.stopover_roofed
  heightDelete_card := F.heightDelete_card

/-- The literal scheduler lane, already in the exact existential form used
by the half-way clause. -/
theorem LiteralFinalGeometry.exists_halfwayLinkage
    {R : LiteralFairStableRun Gamma Y kappa T Z persistent Gamma.target I}
    {A0 : Set V} (F : LiteralFinalGeometry R A0) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W :=
  F.certificate.exists_halfwayLinkage

/-! ## The one-relation fair scheduler

The following is the sound relation-level content of Assertion 9.33.  All
transactions have already been closed and combined into one relation.  Thus
there is one rank, rather than one unrelated rank at every successor stage.
Fairness is used only to prove that a sink outside the target cannot survive:
the target path scheduled for that sink supplies its outgoing relation edge.
-/

/-- A finite nontrivial walk has an edge leaving its first vertex. -/
private theorem walk_exists_edge_from_start {D : Digraph V} :
    ∀ {a b : V} (p : DirectedPath.Walk D a b), a ≠ b →
      ∃ c, (a, c) ∈ p.edgeSet
  | _, _, .nil, hab => (hab rfl).elim
  | _, _, @DirectedPath.Walk.cons _ _ _ c _ h p, _ =>
      ⟨c, by simp⟩

/-- A finite path with distinct endpoints has an edge leaving its start. -/
private theorem finitePath_exists_edge_from_start
    {D : Digraph V} (p : FinitePath D) (h : p.start ≠ p.finish) :
    ∃ c, (p.start, c) ∈ p.edgeSet := by
  exact walk_exists_edge_from_start p.walk h

/-- The construction invariants for the global version of the terminal
scheduler.  The relation is the union of *all* closed inside fragments and
finite compressed assignments.  `rank_step` is deliberately global; a
family of request-local ranks would not rule out a reverse ray in the
eventual union.

The scheduled target paths are original-web paths and their edges occur in
the same relation.  The relation need not be supplied with an orientation:
`exists_forwardOrientation` constructs it below. -/
structure RankedFairGlobalRelation (Gamma : DWeb V)
    (reference : Set Gamma.DPath) (kappa : Cardinal.{u})
    (B : Set V) (I : Type v) where
  edge : Set (V × V)
  carrier : Set V
  rank : V → ℕ
  endpoints_mem : ∀ e ∈ edge, e.1 ∈ carrier ∧ e.2 ∈ carrier
  biunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ edge)
  rank_step : ∀ {x y}, (x, y) ∈ edge → rank x < rank y
  edge_real : edge ⊆ {e | Gamma.graph.Adj e.1 e.2}
  scheduled : I → V
  fair : ∀ x, x ∈ carrier → (¬ ∃ y, (x, y) ∈ edge) →
    x ∉ B → ∃ i, scheduled i = x
  targetPath : I → FinitePath Gamma.graph
  targetPath_start : ∀ i, (targetPath i).start = scheduled i
  targetPath_finish : ∀ i, (targetPath i).finish ∈ B
  targetPath_vertices : ∀ i, (targetPath i).support ⊆ carrier
  targetPath_edges : ∀ i, (targetPath i).edgeSet ⊆ edge

/-- The rank-free form of the final fair relation.  This is the convenient
output of an uncountable-cofinal scheduler: countable boundedness proves
that a hypothetical reverse ray already occurs at one stage, while a
finite-cycle argument does the same for directed cycles.  The global
natural-number depth is then constructed from well-foundedness rather than
being postulated as a compatibility condition on request-local ranks. -/
structure WellFoundedFairGlobalRelation (Gamma : DWeb V)
    (reference : Set Gamma.DPath) (kappa : Cardinal.{u})
    (B : Set V) (I : Type v) where
  edge : Set (V × V)
  carrier : Set V
  endpoints_mem : ∀ e ∈ edge, e.1 ∈ carrier ∧ e.2 ∈ carrier
  biunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ edge)
  no_directed_cycle : ¬ ContainsDirectedCycle edge
  no_reverse_ray : ¬ ContainsReverseDirectedRay edge
  edge_real : edge ⊆ {e | Gamma.graph.Adj e.1 e.2}
  scheduled : I → V
  fair : ∀ x, x ∈ carrier → (¬ ∃ y, (x, y) ∈ edge) →
    x ∉ B → ∃ i, scheduled i = x
  targetPath : I → FinitePath Gamma.graph
  targetPath_start : ∀ i, (targetPath i).start = scheduled i
  targetPath_finish : ∀ i, (targetPath i).finish ∈ B
  targetPath_vertices : ∀ i, (targetPath i).support ⊆ carrier
  targetPath_edges : ∀ i, (targetPath i).edgeSet ⊆ edge

omit [Preorder I] [Nonempty I] [IsDirectedOrder I] in
/-- Construct the global depth certificate from absence of backward rays.
This conversion is what permits the scheduler to use stage-local ranks only
to refute a ray after its countable edge set has been bounded at one stage. -/
noncomputable def WellFoundedFairGlobalRelation.ranked
    {reference : Set Gamma.DPath} {B : Set V}
    (R : WellFoundedFairGlobalRelation Gamma reference kappa B I) :
    RankedFairGlobalRelation Gamma reference kappa B I := by
  let hwf : WellFounded (fun x y ↦ (x, y) ∈ R.edge) :=
    ForwardOrientation.predecessor_wellFounded R.edge
      R.no_directed_cycle R.no_reverse_ray
  exact {
    edge := R.edge
    carrier := R.carrier
    rank := ForwardOrientation.wellFoundedDepth R.edge hwf
    endpoints_mem := R.endpoints_mem
    biunique := R.biunique
    rank_step := fun hxy ↦ by
      have hstep := ForwardOrientation.wellFoundedDepth_step
        R.edge R.biunique hwf hxy
      omega
    edge_real := R.edge_real
    scheduled := R.scheduled
    fair := R.fair
    targetPath := R.targetPath
    targetPath_start := R.targetPath_start
    targetPath_finish := R.targetPath_finish
    targetPath_vertices := R.targetPath_vertices
    targetPath_edges := R.targetPath_edges }

variable {reference : Set Gamma.DPath} {B : Set V}

omit [Preorder I] [Nonempty I] [IsDirectedOrder I] in
/-- Fairness and the embedded target routes eliminate every non-target
sink.  This is the exact terminal conclusion for which the scheduler is
needed; it is proved before the relation is decomposed into paths. -/
theorem RankedFairGlobalRelation.sinks_subset_target
    (R : RankedFairGlobalRelation Gamma reference kappa B I) :
    {x | x ∈ R.carrier ∧ ¬ ∃ y, (x, y) ∈ R.edge} ⊆ B := by
  rintro x ⟨hxcarrier, hxsink⟩
  by_contra hxB
  obtain ⟨i, hi⟩ := R.fair x hxcarrier hxsink hxB
  have hne : (R.targetPath i).start ≠ (R.targetPath i).finish := by
    intro h
    apply hxB
    rw [R.targetPath_start i] at h
    rw [hi] at h
    exact h ▸ R.targetPath_finish i
  obtain ⟨y, hy⟩ := finitePath_exists_edge_from_start (R.targetPath i) hne
  apply hxsink
  refine ⟨y, ?_⟩
  have hxy : (x, y) ∈ (R.targetPath i).edgeSet := by
    simpa [R.targetPath_start i, hi] using hy
  exact R.targetPath_edges i hxy

omit [Preorder I] [Nonempty I] [IsDirectedOrder I] in
/-- The single global rank makes the relation orientable.  Both the edge
and carrier equations are retained, so every later frontier/root statement
can be rewritten back to the construction's concrete sets. -/
theorem RankedFairGlobalRelation.exists_forwardOrientation
    (R : RankedFairGlobalRelation Gamma reference kappa B I) :
    ∃ O : ForwardOrientation (imaginaryGraph Gamma reference kappa),
      O.edge = R.edge ∧ O.carrier = R.carrier := by
  apply exists_forwardOrientation_exact R.edge R.carrier
  · intro e he
    exact original_adj_imaginaryGraph (R.edge_real he)
  · exact R.endpoints_mem
  · exact R.biunique
  · exact not_containsDirectedCycle_of_rank R.edge R.rank R.rank_step
  · exact not_containsReverseDirectedRay_of_rank R.edge R.rank R.rank_step

/-- Oriented form of the global fair relation.  The orientation is the
canonical output of relation decomposition, while target resolution is a
theorem rather than a field. -/
structure OrientedRankedFairGlobalRelation (Gamma : DWeb V)
    (reference : Set Gamma.DPath) (kappa : Cardinal.{u})
    (B : Set V) (I : Type v)
    (R : RankedFairGlobalRelation Gamma reference kappa B I) where
  orientation : ForwardOrientation (imaginaryGraph Gamma reference kappa)
  edge_eq : orientation.edge = R.edge
  carrier_eq : orientation.carrier = R.carrier

/-- Decompose the globally ranked fair relation exactly once. -/
noncomputable def RankedFairGlobalRelation.oriented
    (R : RankedFairGlobalRelation Gamma reference kappa B I) :
    OrientedRankedFairGlobalRelation Gamma reference kappa B I R := by
  let O := R.exists_forwardOrientation.choose
  exact ⟨O, R.exists_forwardOrientation.choose_spec.1,
    R.exists_forwardOrientation.choose_spec.2⟩

omit [Preorder I] [Nonempty I] [IsDirectedOrder I] in
/-- Every sink of the constructed orientation lies in the target. -/
theorem OrientedRankedFairGlobalRelation.sinks_subset_target
    {R : RankedFairGlobalRelation Gamma reference kappa B I}
    (O : OrientedRankedFairGlobalRelation Gamma reference kappa B I R) :
    {x | x ∈ O.orientation.carrier ∧
      ¬ ∃ y, (x, y) ∈ O.orientation.edge} ⊆ B := by
  rw [O.carrier_eq, O.edge_eq]
  exact R.sinks_subset_target

omit [Preorder I] [Nonempty I] [IsDirectedOrder I] in
/-- A construction which forces every relation ray to contain infinitely
many strong imaginary edges, while ensuring that no surviving real edge is
strong, has no forward ray.  The second premise is genuinely stronger than
`edge_real`: an original graph edge may also satisfy
`IsStrongImaginaryEdge`. -/
theorem RankedFairGlobalRelation.no_directedRay_of_no_strong_edge
    (R : RankedFairGlobalRelation Gamma reference kappa B I)
    (hstrong : ∀ r : DirectedPath.Ray
        (imaginaryGraph Gamma reference kappa),
      r.edgeSet ⊆ R.edge → (strongEdgeIndices r).Infinite)
    (hnoStrong : ∀ {x y}, (x, y) ∈ R.edge →
      ¬ IsStrongImaginaryEdge Gamma reference kappa x y) :
    ¬ ContainsDirectedRay R.edge := by
  rintro ⟨ray, hray⟩
  let r : DirectedPath.Ray (imaginaryGraph Gamma reference kappa) := {
    toFun := ray.vertex
    adj_succ := fun n ↦ original_adj_imaginaryGraph
      (R.edge_real (hray ⟨n, rfl⟩))
    injective := ray.injective }
  obtain ⟨n, hn⟩ := (hstrong r (by
    rintro e ⟨m, rfl⟩
    exact hray ⟨m, rfl⟩)).nonempty
  exact hnoStrong (hray ⟨n, rfl⟩) hn

/-! ### Endpoint purity of the final root orbits -/

/-- If every root orbit stops, relation roots lie in `A`, relation sinks lie
in `C`, and no internal point of an orbit can lie in either boundary, then
the canonical root-orbit blueprint is endpoint-pure between `A` and `C`.

The stopping hypothesis is deliberately phrased root-locally.  The outer
construction can prove it by giving a finite route from each actual root to
a relation sink, without first packaging a global no-forward-ray theorem. -/
theorem orientationBlueprint_endpointPure_of_root_stops
    {O : ForwardOrientation (imaginaryGraph Gamma reference kappa)}
    {A C : Set V}
    (hstops : ∀ r : O.Root, ¬ O.NeverStops r.1)
    (hrootSource : {x | O.IsRoot x} ⊆ A)
    (hsourceRoot : ∀ x, x ∈ O.carrier → x ∈ A →
      ¬ ∃ y, (y, x) ∈ O.edge)
    (hsinkFrontier :
      {x | x ∈ O.carrier ∧ ¬ ∃ y, (x, y) ∈ O.edge} ⊆ C)
    (hfrontierSink : ∀ x, x ∈ O.carrier → x ∈ C →
      ¬ ∃ y, (x, y) ∈ O.edge) :
    ∀ p ∈ (orientationBlueprint O).paths,
      (orientationBlueprint O).IsPathBetween A C p := by
  intro p hp
  obtain ⟨r, rfl⟩ := hp
  obtain ⟨q, hq⟩ := O.rootPath_eq_finite_of_stops r (hstops r)
  have hstartEq : q.start = r.1 := by
    have h := O.rootPath_initial r
    rw [hq] at h
    exact h
  have hstartSource : q.start ∈ A := by
    rw [hstartEq]
    exact hrootSource r.2
  have hfinishSink : q.finish ∈ O.carrier ∧
      ¬ ∃ y, (q.finish, y) ∈ O.edge := by
    have hterm : q.finish ∈ (orientationBlueprint O).terminalSet := by
      refine ⟨.inl q, ⟨r, hq⟩, ?_⟩
      exact (imaginaryWeb Gamma reference kappa).terminal?_finite q
    rw [orientationBlueprint_terminalSet_eq_no_outgoing O] at hterm
    exact hterm
  have hfinishFrontier : q.finish ∈ C :=
    hsinkFrontier hfinishSink
  have hsourceOnly : q.support ∩ A = {q.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxsource⟩
      apply Set.mem_singleton_iff.2
      by_contra hxstart
      obtain ⟨y, hyx⟩ :=
        Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          q hxq hxstart
      have hyxO : (y, x) ∈ O.edge := by
        apply O.rootPath_edgeSet_subset r
        rw [hq]
        exact hyx
      exact hsourceRoot x (O.endpoints_mem _ hyxO).2 hxsource ⟨y, hyxO⟩
    · intro x hx
      have hxeq : x = q.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.start_mem_support, hstartSource⟩
  have hfrontierOnly : q.support ∩ C = {q.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxfrontier⟩
      apply Set.mem_singleton_iff.2
      by_contra hxfinish
      obtain ⟨y, hxy⟩ :=
        Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          q hxq hxfinish
      have hxyO : (x, y) ∈ O.edge := by
        apply O.rootPath_edgeSet_subset r
        rw [hq]
        exact hxy
      exact hfrontierSink x (O.endpoints_mem _ hxyO).1 hxfrontier
        ⟨y, hxyO⟩
    · intro x hx
      have hxeq : x = q.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.finish_mem_support, hfinishFrontier⟩
  have hboundaryOnly : q.support ∩ (A ∪ C) =
      {q.start, q.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxboundary⟩
      rcases hxboundary with hxsource | hxfrontier
      · have hxstart : x ∈ ({q.start} : Set V) :=
          hsourceOnly ▸ ⟨hxq, hxsource⟩
        exact Set.mem_insert_iff.2 (Or.inl (Set.mem_singleton_iff.1 hxstart))
      · have hxfinish : x ∈ ({q.finish} : Set V) :=
          hfrontierOnly ▸ ⟨hxq, hxfrontier⟩
        exact Set.mem_insert_iff.2
          (Or.inr (Set.mem_singleton_iff.1 hxfinish))
    · intro x hx
      rcases Set.mem_insert_iff.1 hx with hstart | hfinish
      · subst x
        exact ⟨q.start_mem_support, Or.inl hstartSource⟩
      · have hfinishEq : x = q.finish := Set.mem_singleton_iff.1 hfinish
        subst x
        exact ⟨q.finish_mem_support, Or.inr hfinishFrontier⟩
  exact ⟨q, hq, hboundaryOnly, hsourceOnly⟩

/-- Convenient global-ray-free specialization of
`orientationBlueprint_endpointPure_of_root_stops`. -/
theorem orientationBlueprint_endpointPure_of_no_directedRay
    {O : ForwardOrientation (imaginaryGraph Gamma reference kappa)}
    {A C : Set V}
    (hnoRay : ¬ ContainsDirectedRay O.edge)
    (hrootSource : {x | O.IsRoot x} ⊆ A)
    (hsourceRoot : ∀ x, x ∈ O.carrier → x ∈ A →
      ¬ ∃ y, (y, x) ∈ O.edge)
    (hsinkFrontier :
      {x | x ∈ O.carrier ∧ ¬ ∃ y, (x, y) ∈ O.edge} ⊆ C)
    (hfrontierSink : ∀ x, x ∈ O.carrier → x ∈ C →
      ¬ ∃ y, (x, y) ∈ O.edge) :
    ∀ p ∈ (orientationBlueprint O).paths,
      (orientationBlueprint O).IsPathBetween A C p :=
  orientationBlueprint_endpointPure_of_root_stops
    (fun r ↦ O.stops_of_not_containsDirectedRay hnoRay r)
    hrootSource hsourceRoot hsinkFrontier hfrontierSink

/-! ### Transporting unhinderedness from the ladder stage -/

/-- If the target-reachable induced subweb has the same source as the
ambient web, unhinderedness of that induced subweb implies unhinderedness
of the ambient web.  A wave is restricted to its target-reaching essential
components; fullness there then gives an original member starting at every
ambient source. -/
theorem isUnhindered_of_essentialPart_of_source_eq
    (Q : DWeb V) (hsource : Q.essentialPart.source = Q.source)
    (hessential : Q.essentialPart.IsUnhindered) :
    Q.IsUnhindered := by
  rw [Q.isUnhindered_iff]
  intro W hW
  let U := SliceCandidate.restrictEssentialWarpPartFamily Q W
  have hU : Q.essentialPart.IsWave U :=
    SliceCandidate.isWave_restrictEssentialWarpPartFamily Q hW
  have hUinitial : Q.essentialPart.initialSet U =
      Q.essentialPart.source :=
    Q.essentialPart.isUnhindered_iff.mp hessential U hU
  apply Set.Subset.antisymm hW.2.1
  intro x hx
  have hxEssential : x ∈ Q.essentialPart.source := hsource.symm ▸ hx
  have hxInitial : x ∈ Q.essentialPart.initialSet U :=
    hUinitial.symm ▸ hxEssential
  obtain ⟨q, ⟨p, rfl⟩, hqx⟩ := hxInitial
  refine ⟨p.1, p.2.1, ?_⟩
  simpa only [SliceCandidate.initial_restrictEssentialPartPath] using hqx

/-- A legal ladder frontier roofs the original source. -/
theorem source_subset_roof_ladderFrontier
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    (a : Ladder.Stage kappa) :
    Gamma.source ⊆ Gamma.roof (L.frontier a) := by
  rw [L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages a,
    Gamma.roof_essential]
  exact hL.roofsSourceAtStages (Ladder.Stage.toExtended a)

/-- Club avoidance proves the essential ladder stage unhindered.  Since a
frontier roofs the original source, quotienting by its essential form is
the same as quotienting by the raw accumulated terminal frontier; the raw
quotient has the same source as its essential part.  Hence the full
frontier quotient is unhindered, not merely its target-reachable induced
subweb. -/
theorem quotient_ladderFrontier_isUnhindered
    {L : Gamma.KappaLadder kappa} (hL : L.IsLegal)
    (a : Ladder.Stage kappa)
    (hstage : (L.stageWeb a).IsUnhindered) :
    (Gamma.quotient (L.frontier a)).IsUnhindered := by
  let T := Gamma.terminalFrontier (L.warpAt a)
  have hroofT : Gamma.source ⊆ Gamma.roof T :=
    hL.roofsSourceAtStages (Ladder.Stage.toExtended a)
  have hfrontier : L.frontier a = Gamma.essential T :=
    L.frontier_eq_essential_terminalFrontier hL.roofsSourceAtStages a
  have hquotient : Gamma.quotient (L.frontier a) = Gamma.quotient T := by
    rw [hfrontier]
    exact Gamma.quotient_essential_eq_of_subset_roof T hroofT
  apply isUnhindered_of_essentialPart_of_source_eq
      (Gamma.quotient (L.frontier a))
  · rw [hquotient]
    have hleft : (Gamma.quotient T).essentialPart.source =
        Gamma.essential T :=
      Gamma.quotientEssentialPart_source_eq_essential_of_roofsSource hroofT
    have hright : (Gamma.quotient T).source = Gamma.essential T := by
      rw [DWeb.quotient_source, Set.union_comm]
      exact RelationalRoof.essential_union_eq_of_subset_roof
        Gamma.graph.Adj Gamma.target hroofT
    exact hleft.trans hright.symm
  · rw [hquotient]
    exact hstage

/-! ## The simultaneous root-orientation lane -/

/-- Relation-level endpoint of a global simultaneous replacement.  The
blueprint is not supplied as data: it is the canonical root-orbit
decomposition of `orientation`.  The two boundary fields are consequently
phrased as absence of an incoming or outgoing relation edge.

The final stopover and height data are explicit construction invariants.
This makes the structure strictly prior to, and sufficient for, a
`GloballyResolvedBlueprintCertificate`. -/
structure OrientedGlobalResolution (Gamma : DWeb V) (A0 : Set V)
    (kappa : Cardinal.{u}) where
  reference : Set Gamma.DPath
  orientation : ForwardOrientation
    (imaginaryGraph Gamma reference kappa)
  slice : Set V
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  reference_isWarp : Gamma.IsWarp reference
  edge_real : orientation.edge ⊆ {e | Gamma.graph.Adj e.1 e.2}
  sinks_target :
    {x | x ∈ orientation.carrier ∧
      ¬ ∃ y, (x, y) ∈ orientation.edge} ⊆ Gamma.target
  designated_source : A0 ⊆ Gamma.source
  designated_root :
    A0 ⊆ {x | x ∈ orientation.carrier ∧
      ¬ ∃ y, (y, x) ∈ orientation.edge}
  source_cover :
    (orientationBlueprint orientation).initialSet ∪
      Gamma.initialSet
        ((orientationBlueprint orientation).referenceRemainder slice) =
      Gamma.source
  terminal_frontier :
    (orientationBlueprint orientation).terminalSet ∪
      Gamma.terminalFrontier
        ((orientationBlueprint orientation).referenceRemainder slice) =
      stopover
  blueprint_endpointPure :
    ∀ p ∈ (orientationBlueprint orientation).paths,
      (orientationBlueprint orientation).IsPathBetween
        Gamma.source stopover p
  reference_endpointPure :
    ∀ p ∈ (orientationBlueprint orientation).referenceRemainder slice,
      CardinalInduction.IsPathBetween Gamma Gamma.source stopover p
  stopover_separator : IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave :
    (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

/-- The club/frontier/height information which accompanies a globally
ranked fair splice relation.  Roots and sinks are stated directly for the
concrete relation, so this structure is independent of the implementation
details of the well-founded orientation constructor.  The two endpoint
purity fields refer to the once-and-for-all canonical orientation chosen by
`RankedFairGlobalRelation.oriented`.

Unlike `OrientedGlobalResolution`, this does not contain an orientation and
does not assume terminal resolution.  Those are constructed from the global
rank and fair target routes. -/
structure RankedFairFinalGeometry
    (R : RankedFairGlobalRelation Gamma reference kappa Gamma.target I)
    (A0 : Set V) where
  slice : Set V
  stopover : Set V
  heightDelete : Set V
  heightWave : Set (Gamma.quotient heightDelete).DPath
  reference_isWarp : Gamma.IsWarp reference
  designated_source : A0 ⊆ Gamma.source
  designated_root : A0 ⊆
    {x | x ∈ R.carrier ∧ ¬ ∃ y, (y, x) ∈ R.edge}
  source_cover :
    {x | x ∈ R.carrier ∧ ¬ ∃ y, (y, x) ∈ R.edge} ∪
      Gamma.initialSet
        (referencePathsMeeting reference slice \
          referencePathsMeeting reference R.carrier) =
      Gamma.source
  terminal_frontier :
    {x | x ∈ R.carrier ∧ ¬ ∃ y, (x, y) ∈ R.edge} ∪
      Gamma.terminalFrontier
        (referencePathsMeeting reference slice \
          referencePathsMeeting reference R.carrier) =
      stopover
  blueprint_endpointPure :
    ∀ p ∈ (orientationBlueprint R.oriented.orientation).paths,
      (orientationBlueprint R.oriented.orientation).IsPathBetween
        Gamma.source stopover p
  reference_endpointPure :
    ∀ p ∈
        (referencePathsMeeting reference slice \
          referencePathsMeeting reference R.carrier),
      CardinalInduction.IsPathBetween Gamma Gamma.source stopover p
  stopover_separator : IsSeparatorFrom Gamma Gamma.source stopover
  stopover_trimmed : Gamma.essential stopover = stopover
  quotient_unhindered : (Gamma.quotient stopover).IsUnhindered
  heightDelete_nonSource : heightDelete ⊆ Gamma.sourceᶜ
  heightWave_isWave :
    (Gamma.quotient heightDelete).IsWave heightWave
  stopover_roofed : stopover ⊆ Gamma.roof
    ((Gamma.quotient heightDelete).terminalFrontier heightWave)
  heightDelete_card : #heightDelete ≤ kappa

omit [Preorder I] [Nonempty I] [IsDirectedOrder I] in
/-- A final globally ranked relation whose root/sink boundary is exactly a
selected legal-ladder frontier has all geometric fields required by the
half-way certificate.  The deletion set and quotient wave are constructed,
not assumed, by `HalfwayFrontierHeight.frontier_heightAtMost`; full quotient
unhinderedness is transported from the club stage by
`quotient_ladderFrontier_isUnhindered`. -/
theorem exists_rankedFairFinalGeometry_of_ladderFrontier
    {R : RankedFairGlobalRelation Gamma reference kappa Gamma.target I}
    {A0 : Set V}
    {L : Gamma.KappaLadder (Order.succ kappa)}
    (hGamma : Gamma.IsNormalized) (hL : L.IsLegal)
    (hkappa : aleph0 ≤ kappa)
    (a : Ladder.Stage (Order.succ kappa))
    (hstage : (L.stageWeb a).IsUnhindered)
    (hreference : Gamma.IsWarp reference)
    (hdesignated : A0 ⊆ Gamma.source)
    (hroot : A0 ⊆
      {x | x ∈ R.carrier ∧ ¬ ∃ y, (y, x) ∈ R.edge})
    (hsource :
      {x | x ∈ R.carrier ∧ ¬ ∃ y, (y, x) ∈ R.edge} ∪
        Gamma.initialSet
          (referencePathsMeeting reference (L.frontier a) \
            referencePathsMeeting reference R.carrier) =
        Gamma.source)
    (hterminal :
      {x | x ∈ R.carrier ∧ ¬ ∃ y, (x, y) ∈ R.edge} ∪
        Gamma.terminalFrontier
          (referencePathsMeeting reference (L.frontier a) \
            referencePathsMeeting reference R.carrier) =
        L.frontier a)
    (hblueprint :
      ∀ p ∈ (orientationBlueprint R.oriented.orientation).paths,
        (orientationBlueprint R.oriented.orientation).IsPathBetween
          Gamma.source (L.frontier a) p)
    (hreferencePure :
      ∀ p ∈
          (referencePathsMeeting reference (L.frontier a) \
            referencePathsMeeting reference R.carrier),
        CardinalInduction.IsPathBetween Gamma Gamma.source
          (L.frontier a) p) :
    Nonempty (RankedFairFinalGeometry R A0) := by
  obtain ⟨X, ⟨hXsource, Q, hQ, hroof⟩, hXcard⟩ :=
    HalfwayFrontierHeight.frontier_heightAtMost hGamma hL hkappa a
  exact ⟨{
    slice := L.frontier a
    stopover := L.frontier a
    heightDelete := X
    heightWave := Q
    reference_isWarp := hreference
    designated_source := hdesignated
    designated_root := hroot
    source_cover := hsource
    terminal_frontier := hterminal
    blueprint_endpointPure := hblueprint
    reference_endpointPure := hreferencePure
    stopover_separator := source_subset_roof_ladderFrontier hL a
    stopover_trimmed := hL.frontiersEssential a
    quotient_unhindered :=
      quotient_ladderFrontier_isUnhindered hL a hstage
    heightDelete_nonSource := hXsource
    heightWave_isWave := hQ
    stopover_roofed := hroof
    heightDelete_card := hXcard }⟩

/-- Assemble the final oriented resolution from the valid 9.33 global
relation invariant and the separate club/frontier/height certificate. -/
noncomputable def RankedFairFinalGeometry.globalResolution
    {R : RankedFairGlobalRelation Gamma reference kappa Gamma.target I}
    {A0 : Set V} (F : RankedFairFinalGeometry R A0) :
    OrientedGlobalResolution Gamma A0 kappa where
  reference := reference
  orientation := R.oriented.orientation
  slice := F.slice
  stopover := F.stopover
  heightDelete := F.heightDelete
  heightWave := F.heightWave
  reference_isWarp := F.reference_isWarp
  edge_real := by
    intro e he
    apply R.edge_real
    rwa [R.oriented.edge_eq] at he
  sinks_target := R.oriented.sinks_subset_target
  designated_source := F.designated_source
  designated_root := by
    rw [R.oriented.carrier_eq, R.oriented.edge_eq]
    exact F.designated_root
  source_cover := by
    rw [orientationBlueprint_initialSet_eq_no_incoming,
      R.oriented.carrier_eq, R.oriented.edge_eq]
    simpa only [LinkageBlueprint.referenceRemainder,
      orientationBlueprint_vertexSet, R.oriented.carrier_eq] using
      F.source_cover
  terminal_frontier := by
    rw [orientationBlueprint_terminalSet_eq_no_outgoing,
      R.oriented.carrier_eq, R.oriented.edge_eq]
    simpa only [LinkageBlueprint.referenceRemainder,
      orientationBlueprint_vertexSet, R.oriented.carrier_eq] using
      F.terminal_frontier
  blueprint_endpointPure := F.blueprint_endpointPure
  reference_endpointPure := by
    simpa only [LinkageBlueprint.referenceRemainder,
      orientationBlueprint_vertexSet, R.oriented.carrier_eq] using
      F.reference_endpointPure
  stopover_separator := F.stopover_separator
  stopover_trimmed := F.stopover_trimmed
  quotient_unhindered := F.quotient_unhindered
  heightDelete_nonSource := F.heightDelete_nonSource
  heightWave_isWave := F.heightWave_isWave
  stopover_roofed := F.stopover_roofed
  heightDelete_card := F.heightDelete_card

/-- Compile the well-founded relation endpoint into the canonical final
blueprint certificate.  Edge reality and terminal resolution are derived
from the exact edge/carrier boundary theorems for root-orbit decompositions. -/
def OrientedGlobalResolution.certificate
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (R : OrientedGlobalResolution Gamma A0 kappa) :
    GloballyResolvedBlueprintCertificate Gamma A0 kappa where
  reference := R.reference
  blueprint := orientationBlueprint R.orientation
  slice := R.slice
  stopover := R.stopover
  heightDelete := R.heightDelete
  heightWave := R.heightWave
  reference_isWarp := R.reference_isWarp
  edge_real := by
    intro e he
    rw [orientationBlueprint_edgeSet] at he
    exact R.edge_real he
  real_terminals_target := by
    intro x hx
    apply R.sinks_target
    refine ⟨?_, ?_⟩
    · rw [← orientationBlueprint_vertexSet]
      exact hx.1
    · rintro ⟨y, hy⟩
      apply hx.2
      refine ⟨y, ?_, R.edge_real hy⟩
      rwa [orientationBlueprint_edgeSet]
  designated_source := R.designated_source
  designated_initial := by
    rw [orientationBlueprint_initialSet_eq_no_incoming]
    exact R.designated_root
  source_cover := R.source_cover
  terminal_frontier := R.terminal_frontier
  blueprint_endpointPure := R.blueprint_endpointPure
  reference_endpointPure := R.reference_endpointPure
  stopover_separator := R.stopover_separator
  stopover_trimmed := R.stopover_trimmed
  quotient_unhindered := R.quotient_unhindered
  heightDelete_nonSource := R.heightDelete_nonSource
  heightWave_isWave := R.heightWave_isWave
  stopover_roofed := R.stopover_roofed
  heightDelete_card := R.heightDelete_card

/-- A simultaneous root-orientation resolution gives the required half-way
linkage without a transfinite liminf. -/
theorem OrientedGlobalResolution.exists_halfwayLinkage
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (R : OrientedGlobalResolution Gamma A0 kappa) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W :=
  R.certificate.exists_halfwayLinkage

/-- The globally ranked fair scheduler and the final club geometry directly
produce the construction certificate consumed by the half-way clause. -/
noncomputable def RankedFairFinalGeometry.certificate
    {R : RankedFairGlobalRelation Gamma reference kappa Gamma.target I}
    {A0 : Set V} (F : RankedFairFinalGeometry R A0) :
    GloballyResolvedBlueprintCertificate Gamma A0 kappa :=
  F.globalResolution.certificate

omit [Preorder I] [Nonempty I] [IsDirectedOrder I] in
/-- Final exact output of the sound one-relation form of Assertion 9.33. -/
theorem RankedFairFinalGeometry.exists_halfwayLinkage
    {R : RankedFairGlobalRelation Gamma reference kappa Gamma.target I}
    {A0 : Set V} (F : RankedFairFinalGeometry R A0) :
    ∃ W : Set Gamma.DPath,
      IsHalfwayLinkageOfAltitude Gamma A0 kappa W :=
  F.certificate.exists_halfwayLinkage

/-- Construction of one oriented global resolution for every designated
`kappa`-set proves the exact half-way clause. -/
theorem halfwayClauseAt_of_orientedGlobalResolutions
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hresolve : ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
      Nonempty (OrientedGlobalResolution Gamma A0 kappa)) :
    HalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  exact (hresolve A0 hA0 hcard).some.exists_halfwayLinkage

end HalfwayScheduler
end CardinalInduction
end Erdos599
