/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint930
import ErdosProblems.Erdos599.CyclowarpDecomposition
import ErdosProblems.Erdos599.GlobalBlueprintReplacement
import Mathlib.Data.Fintype.Order

/-!
# Relation limits of real-extension chains

The path-set limit of a chain of linkage blueprints is not appropriate for
Assertion 9.33: a finite path may be properly extended at every stage, so no
whole path value need eventually stabilize.  The observables that are
monotone under `RealExtends` are the real vertices and real edges.

This file takes their unions, proves that the union edge relation remains
bi-unique, and realizes it as the root-orbit decomposition of a forward
orientation.  Two genuinely global hypotheses are kept explicit: the union
has no directed cycle and no reverse directed ray.  The latter cannot be
deduced from the stagewise path property (successively prepending one edge
is a counterexample).
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

universe u v

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {T Z persistent B : Set V}

/-- A linearly ordered chain under the actual real-extension relation (9.32),
rather than literal inclusion of whole path records. -/
structure RealExtensionChain (I : Type v) [LinearOrder I]
    (Gamma : DWeb V) (Y : Set Gamma.DPath) (kappa : Cardinal.{u})
    (T Z persistent B : Set V) where
  stage : I → LinkageBlueprint Gamma Y kappa
  isBlueprint : ∀ i, (stage i).IsLinkageBlueprint T Z persistent
  stable : ∀ i, (stage i).Stable T persistent
  realExtends : ∀ {i j}, i ≤ j → (stage i).RealExtends (stage j) B

namespace RealExtensionChain

variable {I : Type v} [LinearOrder I]

/-- Every real vertex occurring at some stage. -/
def realVertexLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Set V :=
  ⋃ i, (C.stage i).realPart.vertices

/-- Every real edge occurring at some stage. -/
def realEdgeLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Set (V × V) :=
  ⋃ i, (C.stage i).realPart.edges

theorem stage_vertices_subset_realVertexLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) (i : I) :
    (C.stage i).realPart.vertices ⊆ C.realVertexLimit :=
  Set.subset_iUnion (fun j ↦ (C.stage j).realPart.vertices) i

theorem stage_edges_subset_realEdgeLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) (i : I) :
    (C.stage i).realPart.edges ⊆ C.realEdgeLimit :=
  Set.subset_iUnion (fun j ↦ (C.stage j).realPart.edges) i

theorem stage_vertices_mono
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) {i j : I}
    (hij : i ≤ j) :
    (C.stage i).realPart.vertices ⊆ (C.stage j).realPart.vertices :=
  (C.realExtends hij).realPart_extends.1

theorem stage_edges_mono
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) {i j : I}
    (hij : i ≤ j) :
    (C.stage i).realPart.edges ⊆ (C.stage j).realPart.edges :=
  (C.realExtends hij).realEdges_mono

/-- The union relation is locally a disjoint union of directed threads.
Two competing edges can be moved to the later of their two stages. -/
theorem realEdgeLimit_biUnique
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ C.realEdgeLimit) := by
  constructor
  · intro x y z hxz hyz
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxz
    obtain ⟨j, hyj⟩ := Set.mem_iUnion.1 hyz
    rcases le_total i j with hij | hji
    · exact (Alternating.IsWarp.familyEdges_leftUnique (C.stage j).isWarp)
        (C.stage_edges_mono hij hxi).1 hyj.1
    · exact (Alternating.IsWarp.familyEdges_leftUnique (C.stage i).isWarp)
        hxi.1 (C.stage_edges_mono hji hyj).1
  · intro x y z hxy hxz
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.1 hxy
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.1 hxz
    rcases le_total i j with hij | hji
    · exact (Alternating.IsWarp.familyEdges_rightUnique (C.stage j).isWarp)
        (C.stage_edges_mono hij hyi).1 hzj.1
    · exact (Alternating.IsWarp.familyEdges_rightUnique (C.stage i).isWarp)
        hyi.1 (C.stage_edges_mono hji hzj).1

theorem realEdgeLimit_in_graph
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    C.realEdgeLimit ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  intro e he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  exact Or.inl hei.2

theorem realEdgeLimit_endpoints
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    ∀ e ∈ C.realEdgeLimit,
      e.1 ∈ C.realVertexLimit ∧ e.2 ∈ C.realVertexLimit := by
  intro e he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  have hedge : e ∈ Alternating.familyEdges
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths := by
    exact hei.1
  have hends :
      e.1 ∈ (C.stage i).vertexSet ∧ e.2 ∈ (C.stage i).vertexSet :=
    Alternating.familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hedge
  exact ⟨Set.mem_iUnion.2 ⟨i, by simpa using hends.1⟩,
    Set.mem_iUnion.2 ⟨i, by simpa using hends.2⟩⟩

/-- A directed cycle in the union is already present at one stage.  This is
the finite half of the well-foundedness argument and needs no extra chain
invariant beyond monotonicity of real edges. -/
theorem realEdgeLimit_not_containsDirectedCycle
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) :
    ¬ Alternating.ContainsDirectedCycle C.realEdgeLimit := by
  rintro ⟨Q, hQ⟩
  let stageOf : Fin Q.length → I := fun n ↦
    Classical.choose (Set.mem_iUnion.1 (hQ ⟨n, rfl⟩))
  have hstageOf (n : Fin Q.length) :
      (Q.vertex n, Q.vertex (Q.next n)) ∈
        (C.stage (stageOf n)).realPart.edges :=
    Classical.choose_spec (Set.mem_iUnion.1 (hQ ⟨n, rfl⟩))
  let i₀ : Fin Q.length := ⟨0, Q.positive⟩
  letI : Nonempty I := ⟨stageOf i₀⟩
  obtain ⟨j, hj⟩ := Finite.exists_le stageOf
  have hQj : Q.EdgeSet ⊆ (C.stage j).edgeSet := by
    rintro e ⟨n, rfl⟩
    exact (C.stage_edges_mono (hj n) (hstageOf n)).1
  exact blueprint_edgeSet_not_containsDirectedCycle (C.stage j) ⟨Q, hQj⟩

/-- Global well-foundedness conditions required to decompose the union into
rooted finite paths and rays. -/
structure RelationLimitCore
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop where
  no_directed_cycle : ¬ Alternating.ContainsDirectedCycle C.realEdgeLimit
  no_reverse_ray : ¬ Alternating.ContainsReverseDirectedRay C.realEdgeLimit

/-- The precise root invariant needed to rule out the genuine obstruction
to a relation limit.  Every root of a stage real component lies on the
source side, and no original edge enters that side.  Stating the invariant
for the real relation is important: an imaginary predecessor may disappear
at a successor and therefore cannot anchor the limit relation. -/
structure SourceRooted (C :
    RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop where
  realRoot_mem_source : ∀ i x, x ∈ (C.stage i).realPart.vertices →
    (¬ ∃ y, (y, x) ∈ (C.stage i).realPart.edges) → x ∈ Gamma.source
  noEdgeEnters_source : Gamma.NoEdgeEnters Gamma.source

/-- The local chain invariant which directly rules out the reverse-ray
obstruction.  A successor may append real edges after old vertices, but it
never inserts a new real predecessor before a vertex which was already
present.  Unlike `SourceRooted`, this invariant also applies to real
components beginning immediately after an imaginary edge. -/
structure NoNewRealPredecessors (C :
    RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop where
  of_le : ∀ {i j : I}, i ≤ j → ∀ {x y : V},
    x ∈ (C.stage i).realPart.vertices →
    (y, x) ∈ (C.stage j).realPart.edges →
    (y, x) ∈ (C.stage i).realPart.edges

/-- A reverse ray in a chain satisfying `NoNewRealPredecessors` would
already occur at the stage containing its first edge.  Inductively, the
next edge either belongs to an earlier stage and hence is monotone into the
chosen stage, or belongs to a later stage and enters an old vertex, so the
invariant pulls it back. -/
theorem realEdgeLimit_not_containsReverseDirectedRay_of_noNewPredecessors
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewRealPredecessors) :
    ¬ Alternating.ContainsReverseDirectedRay C.realEdgeLimit := by
  rintro ⟨R, hR⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hR 0)
  have hstage : ∀ n : ℕ, (R.vertex (n + 1), R.vertex n) ∈
      (C.stage i).realPart.edges := by
    intro n
    induction n with
    | zero => simpa using hi
    | succ n ih =>
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hR (n + 1))
        rcases le_total i j with hij | hji
        · have hx : R.vertex (n + 1) ∈
              (C.stage i).realPart.vertices := by
            change R.vertex (n + 1) ∈ (C.stage i).vertexSet
            exact (Alternating.familyEdges_subset_vertexSet_prod
              (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths ih.1).1
          exact H.of_le hij hx hj
        · exact C.stage_edges_mono hji hj
  exact blueprint_edgeSet_not_containsReverseDirectedRay (C.stage i)
    ⟨R, fun n ↦ (hstage n).1⟩

/-- Source-rooted chains cannot acquire a reverse ray at a limit.  Starting
with the stage containing the first ray edge, take the first predecessor
edge which leaves that stage path.  Bi-uniqueness says that it enters the
initial vertex of the old path, hence an original edge enters the source,
contrary to normalization. -/
theorem realEdgeLimit_not_containsReverseDirectedRay
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.SourceRooted) :
    ¬ Alternating.ContainsReverseDirectedRay C.realEdgeLimit := by
  classical
  rintro ⟨R, hR⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hR 0)
  have hexit : ∃ n, (R.vertex (n + 1), R.vertex n) ∉
      (C.stage i).realPart.edges := by
    by_contra hall
    push_neg at hall
    exact blueprint_edgeSet_not_containsReverseDirectedRay (C.stage i)
      ⟨R, fun n ↦ (hall n).1⟩
  let n := Nat.find hexit
  have hnexit : (R.vertex (n + 1), R.vertex n) ∉
      (C.stage i).realPart.edges :=
    Nat.find_spec hexit
  have hnpos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    apply hnexit
    simpa [n, hn] using hi
  have hprev : (R.vertex n, R.vertex (n - 1)) ∈
      (C.stage i).realPart.edges := by
    have hlt : n - 1 < n := Nat.sub_lt hnpos (by omega)
    have hmem := Nat.find_min hexit hlt
    simpa [Nat.sub_add_cancel hnpos] using hmem
  have hxVertex : R.vertex n ∈ (C.stage i).realPart.vertices := by
    change R.vertex n ∈ (C.stage i).vertexSet
    have hedge : (R.vertex n, R.vertex (n - 1)) ∈
        Alternating.familyEdges (Γ := imaginaryWeb Gamma Y kappa)
          (C.stage i).paths := by
      exact hprev.1
    exact (Alternating.familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma Y kappa) (C.stage i).paths hedge).1
  have hnoIncoming : ¬ ∃ y,
      (y, R.vertex n) ∈ (C.stage i).realPart.edges := by
    rintro ⟨y, hy⟩
    have heq : y = R.vertex (n + 1) :=
      C.realEdgeLimit_biUnique.1
        (C.stage_edges_subset_realEdgeLimit i hy) (hR n)
    exact hnexit (heq ▸ hy)
  have hxSource : R.vertex n ∈ Gamma.source :=
    H.realRoot_mem_source i (R.vertex n) hxVertex hnoIncoming
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hR n)
  exact H.noEdgeEnters_source hj.2 hxSource

/-- The source-root invariant supplies both global decomposition obligations
for the real-edge union. -/
def relationLimitCore_of_sourceRooted
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.SourceRooted) : C.RelationLimitCore where
  no_directed_cycle := C.realEdgeLimit_not_containsDirectedCycle
  no_reverse_ray := C.realEdgeLimit_not_containsReverseDirectedRay H

/-- The scheduler-facing limit core: forward-only successor extensions
provide the exact invariant needed to exclude a reverse ray. -/
def relationLimitCore_of_noNewRealPredecessors
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewRealPredecessors) : C.RelationLimitCore where
  no_directed_cycle := C.realEdgeLimit_not_containsDirectedCycle
  no_reverse_ray :=
    C.realEdgeLimit_not_containsReverseDirectedRay_of_noNewPredecessors H

/-- The canonical forward orientation of the union of real edges. -/
noncomputable def relationLimitOrientation
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    Alternating.RelationDecomposition.ForwardOrientation
      (imaginaryGraph Gamma Y kappa) :=
  Classical.choose (exists_forwardOrientation_exact
    C.realEdgeLimit C.realVertexLimit C.realEdgeLimit_in_graph
      C.realEdgeLimit_endpoints C.realEdgeLimit_biUnique
      H.no_directed_cycle H.no_reverse_ray)

theorem relationLimitOrientation_spec
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    (C.relationLimitOrientation H).edge = C.realEdgeLimit ∧
      (C.relationLimitOrientation H).carrier = C.realVertexLimit :=
  Classical.choose_spec (exists_forwardOrientation_exact
    C.realEdgeLimit C.realVertexLimit C.realEdgeLimit_in_graph
      C.realEdgeLimit_endpoints C.realEdgeLimit_biUnique
      H.no_directed_cycle H.no_reverse_ray)

/-- Root-orbit decomposition of the monotone real observables. -/
noncomputable def relationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) : LinkageBlueprint Gamma Y kappa :=
  orientationBlueprint (C.relationLimitOrientation H)

theorem relationLimit_vertexSet
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    (C.relationLimit H).vertexSet = C.realVertexLimit := by
  rw [relationLimit, orientationBlueprint_vertexSet,
    (C.relationLimitOrientation_spec H).2]

theorem relationLimit_edgeSet
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    (C.relationLimit H).edgeSet = C.realEdgeLimit := by
  rw [relationLimit, orientationBlueprint_edgeSet,
    (C.relationLimitOrientation_spec H).1]

theorem relationLimit_edge_real
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) :
    (C.relationLimit H).familyGraph.edges ⊆
      {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  change e ∈ (C.relationLimit H).edgeSet at he
  rw [C.relationLimit_edgeSet H] at he
  obtain ⟨i, hei⟩ := Set.mem_iUnion.1 he
  exact hei.2

/-! ## Compiling raw relation-boundary data at the limit -/

/-- An initial vertex of a blueprint path has no incoming blueprint edge.
This elementary fact is valid for both finite members and rays and does not
require finite character of the warp. -/
theorem no_incoming_edge_of_mem_initialSet
    (W : LinkageBlueprint Gamma Y kappa) {x : V}
    (hx : x ∈ W.initialSet) : ¬ ∃ y, (y, x) ∈ W.edgeSet := by
  rintro ⟨y, hyx⟩
  obtain ⟨p, hpW, rfl⟩ := hx
  simp only [edgeSet, Set.mem_iUnion] at hyx
  obtain ⟨q, hqW, hyxq⟩ := hyx
  have hinitialq : p.initial ∈ q.support :=
    (q.edgeSet_subset_support_prod hyxq).2
  have hpq : p = q :=
    W.path_eq_of_mem_support hpW hqW p.initial_mem_support hinitialq
  subst q
  rcases p with p | r
  · exact Alternating.FinitePath.no_incoming_edge_at_start p y hyxq
  · obtain ⟨n, hn⟩ := hyxq
    have heq : r (n + 1) = r 0 := by
      simpa only [DirectedPath.Path.initial, DirectedPath.Ray.initial] using
        (congrArg Prod.snd hn).symm
    have : n + 1 = 0 := r.injective heq
    omega

/-- Under the forward-only predecessor invariant, every stage initial is a
root of the real-edge union.  Later stages cannot insert an incoming edge at
the old vertex, while earlier incoming edges would already be present by
monotonicity. -/
theorem stage_initialSet_subset_relationRoots
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewRealPredecessors) (i : I) :
    (C.stage i).initialSet ⊆
      {x | x ∈ C.realVertexLimit ∧
        ¬ ∃ y, (y, x) ∈ C.realEdgeLimit} := by
  intro x hx
  have hxvertex : x ∈ (C.stage i).realPart.vertices := by
    rcases hx with ⟨p, hp, rfl⟩
    exact ⟨p, hp, p.initial_mem_support⟩
  refine ⟨C.stage_vertices_subset_realVertexLimit i hxvertex, ?_⟩
  rintro ⟨y, hyx⟩
  obtain ⟨j, hyxj⟩ := Set.mem_iUnion.1 hyx
  have hnoincoming := no_incoming_edge_of_mem_initialSet (C.stage i) hx
  rcases le_total i j with hij | hji
  · exact hnoincoming ⟨y, (H.of_le hij hxvertex hyxj).1⟩
  · exact hnoincoming ⟨y, (C.stage_edges_mono hji hyxj).1⟩

/-- Source coverage of the union relation follows from source coverage at
the stages.  If a reference path retained at one stage later meets the union,
reapply coverage at a stage containing that meeting vertex; reference-warp
disjointness forces the retained member there to be the same path. -/
theorem relationLimit_covers_source
    [Nonempty I]
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.NoNewRealPredecessors) (hYwarp : Gamma.IsWarp Y) :
    Gamma.source ⊆
      {x | x ∈ C.realVertexLimit ∧
        ¬ ∃ y, (y, x) ∈ C.realEdgeLimit} ∪
        Gamma.initialSet
          (referencePathsMeeting Y T \
            referencePathsMeeting Y C.realVertexLimit) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  intro a ha
  rcases (C.isBlueprint i₀).covers_source ha with hainitial | hretained
  · exact Or.inl (C.stage_initialSet_subset_relationRoots H i₀ hainitial)
  · rcases hretained with ⟨p, ⟨hpT, hpnoti₀⟩, hpinitial⟩
    by_cases hpmeet : (p.support ∩ C.realVertexLimit).Nonempty
    · obtain ⟨x, hxp, hxlimit⟩ := hpmeet
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.1 hxlimit
      rcases (C.isBlueprint j).covers_source ha with hjinitial | hjretained
      · exact Or.inl (C.stage_initialSet_subset_relationRoots H j hjinitial)
      · rcases hjretained with ⟨q, ⟨hqT, hqnotj⟩, hqinitial⟩
        have hqp : q = p := by
          by_contra hne
          have hd := hYwarp hqT.1 hpT.1 hne
          exact Set.disjoint_left.1 hd
            (hqinitial ▸ q.initial_mem_support)
            (hpinitial ▸ p.initial_mem_support)
        subst q
        exact False.elim <| hqnotj
          ⟨hpT.1, ⟨x, hxp, by simpa only [realPart_vertices] using hxj⟩⟩
    · exact Or.inr ⟨p, ⟨hpT, fun hp ↦ hpmeet hp.2⟩, hpinitial⟩

/-- The source-facing non-local facts about the union relation which remain
after vertex/edge monotonicity has been discharged.  This record mentions no
proposed limit blueprint.  Its root and sink sets are computed directly from
the union of the stage real parts, exactly as in the relation-level form of
Assertion 9.31.

Roof containment and closure containment are deliberately absent: they are
automatic from the corresponding fields of every stage blueprint. -/
structure RelationLimitBoundaryData
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) : Prop where
  covers_source : Gamma.source ⊆
    {x | x ∈ C.realVertexLimit ∧ ¬ ∃ y, (y, x) ∈ C.realEdgeLimit} ∪
      Gamma.initialSet
        (referencePathsMeeting Y T \
          referencePathsMeeting Y C.realVertexLimit)
  card_vertices : #C.realVertexLimit ≤ kappa
  every_relation_ray_strong :
    ∀ r : DirectedPath.Ray (imaginaryGraph Gamma Y kappa),
      r.edgeSet ⊆ C.realEdgeLimit → (strongEdgeIndices r).Infinite
  terminal_boundary :
    {x | x ∈ C.realVertexLimit ∧ ¬ ∃ y, (x, y) ∈ C.realEdgeLimit} ⊆
      {x | IsPopular Gamma Y persistent kappa x} ∪ T
  stable_boundary :
    {x | x ∈ C.realVertexLimit ∧ ¬ ∃ y, (x, y) ∈ C.realEdgeLimit} ∩ T ⊆
      persistent

/-- The carrier-cardinality field of `RelationLimitBoundaryData` is
automatic for a chain with at most `kappa` stages.  Each stage has at most
`kappa` paths, and an infinite `kappa` bounds the countable support of every
finite path or ray. -/
theorem mk_realVertexLimit_le
    {J : Type u} [LinearOrder J] [Nonempty J]
    (C : RealExtensionChain J Gamma Y kappa T Z persistent B)
    (hkappa : aleph0 ≤ kappa) (hindex : #J ≤ kappa) :
    #C.realVertexLimit ≤ kappa := by
  refine (Cardinal.mk_iUnion_le
    (fun i ↦ (C.stage i).realPart.vertices)).trans ?_
  apply Cardinal.mul_le_of_le hkappa hindex
  apply ciSup_le
  intro i
  simpa only [realPart_vertices] using
    (C.stage i).mk_vertexSet_le_of_mk_paths_le hkappa
      (C.isBlueprint i).card_paths

/-! ### Boundary consequences of eventual terminal completion -/

/-- A sink of the union real relation was already a real terminal at some
stage.  This relation-level form avoids mentioning the chosen root-orbit
decomposition. -/
theorem exists_stage_realTerminal_of_mem_relationSink
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B) {x : V}
    (hx : x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.realEdgeLimit) :
    ∃ i, x ∈ (C.stage i).realPart.terminals := by
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx.1
  refine ⟨i, hxi, ?_⟩
  rintro ⟨y, hxy⟩
  exact hx.2 ⟨y, C.stage_edges_subset_realEdgeLimit i hxy⟩

/-- If every stage real terminal is eventually completed, every sink of the
union relation already lies in the target set of those completions.  A
nontrivial completion would supply an outgoing union edge at the sink. -/
theorem relationSink_subset_of_eventuallyCompleted
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
        ∃ j, x ∈ (C.stage j).completedRealVertices B) :
    {x | x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.realEdgeLimit} ⊆ B := by
  intro x hx
  obtain ⟨i, hxiterm⟩ :=
    C.exists_stage_realTerminal_of_mem_relationSink hx
  obtain ⟨j, hxcompleted⟩ := eventuallyCompleted i x hxiterm
  by_contra hxB
  apply (not_mem_realTerminals_of_realLinksTo hxB
    (realLinksTo_of_mem_completedRealVertices hxcompleted))
  rcases hxcompleted with ⟨p, hpB, hpsupport, hpedge, hxp⟩
  refine ⟨hpsupport hxp, ?_⟩
  rintro ⟨y, hxy⟩
  exact hx.2 ⟨y, C.stage_edges_subset_realEdgeLimit j hxy⟩

/-- Eventual completion reduces the terminal boundary of the union to the
elementary boundary condition on `B`. -/
theorem relationLimit_terminal_boundary_of_eventuallyCompleted
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
        ∃ j, x ∈ (C.stage j).completedRealVertices B)
    (hB : B ⊆ {x | IsPopular Gamma Y persistent kappa x} ∪ T) :
    {x | x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.realEdgeLimit} ⊆
        {x | IsPopular Gamma Y persistent kappa x} ∪ T :=
  (C.relationSink_subset_of_eventuallyCompleted eventuallyCompleted).trans hB

/-- Eventual completion likewise reduces stability at the union boundary to
the fixed compatibility `B ∩ T ⊆ persistent`. -/
theorem relationLimit_stable_boundary_of_eventuallyCompleted
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
        ∃ j, x ∈ (C.stage j).completedRealVertices B)
    (hstableB : B ∩ T ⊆ persistent) :
    {x | x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.realEdgeLimit} ∩ T ⊆ persistent := by
  rintro x ⟨hx, hxT⟩
  exact hstableB ⟨C.relationSink_subset_of_eventuallyCompleted
    eventuallyCompleted hx, hxT⟩

/-- For the final all-real union, a sink is already acceptable whenever
every stage real terminal which is not a genuine blueprint terminal lies in
the active slice.  Genuine blueprint terminals satisfy condition (6) at
their stage; the remaining case belongs to `T` directly. -/
theorem relationLimit_terminal_boundary_of_nonterminal_in_slice
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (nonterminal_in_slice : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
      x ∉ (C.stage i).terminalSet → x ∈ T) :
    {x | x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.realEdgeLimit} ⊆
        {x | IsPopular Gamma Y persistent kappa x} ∪ T := by
  intro x hx
  obtain ⟨i, hxreal⟩ := C.exists_stage_realTerminal_of_mem_relationSink hx
  by_cases hxterminal : x ∈ (C.stage i).terminalSet
  · exact (C.isBlueprint i).terminals_popular hxterminal
  · exact Or.inr (nonterminal_in_slice i x hxreal hxterminal)

/-- Stability of the final all-real boundary only requires eventual
completion of the eligible (`T`-valued) real terminals. -/
theorem relationLimit_stable_boundary_of_eventuallyCompleted_in_slice
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals → x ∈ T →
        ∃ j, x ∈ (C.stage j).completedRealVertices B)
    (hstableB : B ∩ T ⊆ persistent) :
    {x | x ∈ C.realVertexLimit ∧
      ¬ ∃ y, (x, y) ∈ C.realEdgeLimit} ∩ T ⊆ persistent := by
  rintro x ⟨hx, hxT⟩
  obtain ⟨i, hxreal⟩ := C.exists_stage_realTerminal_of_mem_relationSink hx
  obtain ⟨j, hxcompleted⟩ := eventuallyCompleted i x hxreal hxT
  have hxB : x ∈ B := by
    by_contra hxnotB
    apply (not_mem_realTerminals_of_realLinksTo hxnotB
      (realLinksTo_of_mem_completedRealVertices hxcompleted))
    rcases hxcompleted with ⟨p, hpB, hpsupport, hpedge, hxp⟩
    refine ⟨hpsupport hxp, ?_⟩
    rintro ⟨y, hxy⟩
    exact hx.2 ⟨y, C.stage_edges_subset_realEdgeLimit j hxy⟩
  exact hstableB ⟨hxB, hxT⟩

/-- The canonical root-orbit limit satisfies all six blueprint conditions
from raw boundary data on the union relation.  In particular, path
disjointness is constructed by the forward orientation, and the path-cardinal
bound follows from the cardinality of its carrier rather than being assumed
for the resulting path family. -/
theorem relationLimit_isLinkageBlueprint
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (D : C.RelationLimitBoundaryData) :
    (C.relationLimit H).IsLinkageBlueprint T Z persistent := by
  let O := C.relationLimitOrientation H
  have hOE : O.edge = C.realEdgeLimit :=
    (C.relationLimitOrientation_spec H).1
  have hOC : O.carrier = C.realVertexLimit :=
    (C.relationLimitOrientation_spec H).2
  refine
    { vertices_roofed := ?_
      covers_source := ?_
      vertices_closed := ?_
      card_paths := ?_
      infinitely_many_strong := ?_
      terminals_popular := ?_ }
  · intro x hx
    rw [C.relationLimit_vertexSet H] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact (C.isBlueprint i).vertices_roofed (by simpa using hxi)
  · rw [relationLimit, orientationBlueprint_initialSet_eq_no_incoming,
      retainedReferenceInitials, orientationBlueprint_vertexSet, hOC, hOE]
    exact D.covers_source
  · intro x hx
    rw [C.relationLimit_vertexSet H] at hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
    exact (C.isBlueprint i).vertices_closed (by simpa using hxi)
  · change #(Set.range O.rootPath) ≤ kappa
    refine Cardinal.mk_range_le.trans ?_
    refine (Cardinal.mk_subtype_mono (fun x hx ↦ hx.1)).trans ?_
    simpa only [hOC] using D.card_vertices
  · intro r hr
    apply D.every_relation_ray_strong r
    intro e he
    rw [← hOE, ← orientationBlueprint_edgeSet O]
    exact Set.mem_iUnion.2 ⟨(Sum.inr r :
      DirectedPath.Path (imaginaryGraph Gamma Y kappa)),
        Set.mem_iUnion.2 ⟨hr, he⟩⟩
  · rw [relationLimit, orientationBlueprint_terminalSet_eq_no_outgoing,
      hOC, hOE]
    exact D.terminal_boundary

/-- Stability of the canonical relation limit is likewise just the raw sink
boundary of the union relation. -/
theorem relationLimit_stable
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (D : C.RelationLimitBoundaryData) :
    (C.relationLimit H).Stable T persistent := by
  rw [Stable, relationLimit,
    orientationBlueprint_terminalSet_eq_no_outgoing,
    (C.relationLimitOrientation_spec H).2,
    (C.relationLimitOrientation_spec H).1]
  exact D.stable_boundary

theorem realPart_extends_relationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (i : I) :
    (C.stage i).realPart.Extends (C.relationLimit H).realPart := by
  constructor
  · change (C.stage i).vertexSet ⊆ (C.relationLimit H).vertexSet
    rw [C.relationLimit_vertexSet H]
    exact C.stage_vertices_subset_realVertexLimit i
  · intro e he
    rw [realPart_edges]
    refine ⟨?_, he.2⟩
    rw [C.relationLimit_edgeSet H]
    exact C.stage_edges_subset_realEdgeLimit i he

/-- The accounting half of (9.32) for a fair relation union.  The extra
hypothesis is exactly the scheduler obligation that every real terminal ever
created is eventually completed to `B`.  It is necessary: a stage vertex may
be the tail of an imaginary edge, and the all-real relation union deliberately
drops that edge.

If an old vertex is not a terminal of the union, choose a stage containing an
outgoing real limit edge.  At a comparable later stage, (9.32) says that the
vertex is either still a terminal, is the tail of a retained old edge, or has
already been completed.  The terminal case contradicts the chosen edge;
bi-uniqueness identifies a retained old edge with that real edge. -/
theorem accounted_relationLimit_of_eventuallyCompleted_nonterminal
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
      x ∉ (C.stage i).terminalSet →
        ∃ j, x ∈ (C.stage j).completedRealVertices B)
    (i : I) :
    (C.stage i).vertexSet ⊆
      ((C.relationLimit H).terminalSet ∩ (C.stage i).terminalSet) ∪
        {x | ∃ y, (x, y) ∈
          (C.stage i).familyGraph.edges ∩
            (C.relationLimit H).familyGraph.edges} ∪
          (C.relationLimit H).completedRealVertices B := by
  intro x hxi
  by_cases hxterm : x ∈ (C.relationLimit H).terminalSet
  · by_cases hxiterm : x ∈ (C.stage i).terminalSet
    · exact Or.inl (Or.inl ⟨hxterm, hxiterm⟩)
    · have hxrealterm : x ∈ (C.stage i).realPart.terminals := by
        refine ⟨by simpa only [realPart_vertices] using hxi, ?_⟩
        rintro ⟨y, hxy⟩
        have hxyLimit : (x, y) ∈ (C.relationLimit H).edgeSet := by
          rw [C.relationLimit_edgeSet H]
          exact C.stage_edges_subset_realEdgeLimit i hxy
        exact (mem_familyGraph_terminals_of_mem_terminalSet hxterm).2
          ⟨y, hxyLimit⟩
      obtain ⟨j, hxcompleted⟩ :=
        eventuallyCompleted i x hxrealterm hxiterm
      exact Or.inr <| completedRealVertices_mono
        (C.realPart_extends_relationLimit H j) hxcompleted
  · have hxlimitVertex : x ∈ (C.relationLimit H).vertexSet := by
      rw [C.relationLimit_vertexSet H]
      exact C.stage_vertices_subset_realVertexLimit i
        (by simpa only [realPart_vertices] using hxi)
    obtain ⟨y, hxyLimit⟩ :=
      (C.relationLimit H)
        |>.exists_outgoing_of_mem_vertexSet_of_not_mem_terminalSet
          hxlimitVertex hxterm
    have hxyRealLimit : (x, y) ∈ C.realEdgeLimit := by
      change (x, y) ∈ (C.relationLimit H).edgeSet at hxyLimit
      rwa [C.relationLimit_edgeSet H] at hxyLimit
    obtain ⟨j, hxyj⟩ := Set.mem_iUnion.1 hxyRealLimit
    rcases le_total i j with hij | hji
    · rcases (C.realExtends hij).2 hxi with hcommonTerm | hcompleted
      · rcases hcommonTerm with hterm | hedge
        · have hnoout :=
            mem_familyGraph_terminals_of_mem_terminalSet hterm.1
          exact False.elim (hnoout.2 ⟨y, hxyj.1⟩)
        · rcases hedge with ⟨z, hxzi, hxzj⟩
          have hzy : z = y :=
            Alternating.IsWarp.familyEdges_rightUnique
              (C.stage j).isWarp hxzj hxyj.1
          exact Or.inl (Or.inr ⟨y, hzy ▸ hxzi, by
            change (x, y) ∈ (C.relationLimit H).edgeSet
            rw [C.relationLimit_edgeSet H]
            exact C.stage_edges_subset_realEdgeLimit j hxyj⟩)
      · exact Or.inr <| completedRealVertices_mono
          (C.realPart_extends_relationLimit H j) hcompleted
    · exact Or.inl (Or.inr ⟨y, (C.stage_edges_mono hji hxyj).1,
        by
          change (x, y) ∈ (C.relationLimit H).edgeSet
          rw [C.relationLimit_edgeSet H]
          exact C.stage_edges_subset_realEdgeLimit j hxyj⟩)

/-- Completing every stage real terminal is a convenient stronger form of
the exact accounting hypothesis above. -/
theorem accounted_relationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
        ∃ j, x ∈ (C.stage j).completedRealVertices B) :
    ∀ i, (C.stage i).vertexSet ⊆
      ((C.relationLimit H).terminalSet ∩ (C.stage i).terminalSet) ∪
        {x | ∃ y, (x, y) ∈
          (C.stage i).familyGraph.edges ∩
            (C.relationLimit H).familyGraph.edges} ∪
          (C.relationLimit H).completedRealVertices B := by
  intro i
  exact C.accounted_relationLimit_of_eventuallyCompleted_nonterminal H
    (fun i x hx _ ↦ eventuallyCompleted i x hx) i

/-- The non-local output needed in addition to the monotone observables.
The `accounted` field is exactly the second conjunct of (9.32). -/
structure StableRelationLimitData
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) : Prop where
  isBlueprint : (C.relationLimit H).IsLinkageBlueprint T Z persistent
  stable : (C.relationLimit H).Stable T persistent
  accounted : ∀ i, (C.stage i).vertexSet ⊆
    ((C.relationLimit H).terminalSet ∩ (C.stage i).terminalSet) ∪
      {x | ∃ y, (x, y) ∈
        (C.stage i).familyGraph.edges ∩
          (C.relationLimit H).familyGraph.edges} ∪
        (C.relationLimit H).completedRealVertices B

/-- Raw union-relation boundary data and eventual completion of every stage
real terminal are precisely the two independent inputs needed for the stable
limit theorem.  The former compiles the six blueprint conditions and
stability; the latter derives the full persistence/accounting disjunction
(9.32). -/
def stableRelationLimitData_of_boundary_eventuallyCompleted
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (D : C.RelationLimitBoundaryData)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
        ∃ j, x ∈ (C.stage j).completedRealVertices B) :
    C.StableRelationLimitData H where
  isBlueprint := C.relationLimit_isLinkageBlueprint H D
  stable := C.relationLimit_stable H D
  accounted := C.accounted_relationLimit H eventuallyCompleted

/-- Exact scheduler form of relation-limit accounting: only real terminals
which are not already full blueprint terminals must be completed. -/
def stableRelationLimitData_of_boundary_eventuallyCompleted_nonterminal
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (D : C.RelationLimitBoundaryData)
    (eventuallyCompleted : ∀ i x,
      x ∈ (C.stage i).realPart.terminals →
      x ∉ (C.stage i).terminalSet →
        ∃ j, x ∈ (C.stage j).completedRealVertices B) :
    C.StableRelationLimitData H where
  isBlueprint := C.relationLimit_isLinkageBlueprint H D
  stable := C.relationLimit_stable H D
  accounted :=
    C.accounted_relationLimit_of_eventuallyCompleted_nonterminal H
      eventuallyCompleted

theorem realExtends_relationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (D : C.StableRelationLimitData H) (i : I) :
    (C.stage i).RealExtends (C.relationLimit H) B :=
  ⟨C.realPart_extends_relationLimit H i, D.accounted i⟩

/-- Sound replacement for the path-set-liminf limit theorem. -/
theorem stableLimitConclusion_relationLimit
    (C : RealExtensionChain I Gamma Y kappa T Z persistent B)
    (H : C.RelationLimitCore) (D : C.StableRelationLimitData H) :
    StableLimitConclusion C.stage (C.relationLimit H)
      T Z persistent B :=
  ⟨D.isBlueprint, D.stable, C.realExtends_relationLimit H D⟩

end RealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599
