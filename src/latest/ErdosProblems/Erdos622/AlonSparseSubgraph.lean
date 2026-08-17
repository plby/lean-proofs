/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos622.External.Erdos76.FiniteBernoulliLocality
import ErdosProblems.Erdos697.Erdos697Bernoulli
import ErdosProblems.Erdos622.AlonOriginal
import ErdosProblems.Erdos622.AlonScalar
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Alon's sparse high-girth spanning subgraph

This file encodes the finite product experiment in Lemma 3.2 of Alon's
linear-arboricity paper.  Its coordinate type is the edge set of the host
graph.  The two bad-event families are the deviation of a vertex degree and
the survival of all edges of a short cycle.

The definitions deliberately use edge supports, rather than enumerations of
cycles.  This makes the event index finite without requiring a finite instance
for the inductive type of graph walks, and it identifies different cyclic
enumerations having the same edge set.
-/

open Filter Finset
open scoped BigOperators SimpleGraph Topology

namespace Erdos622
namespace AlonSparseSubgraph

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The finite coordinate type for independent edge sampling. -/
abbrev Edge (G : SimpleGraph V) := G.edgeFinset

/-- Edges incident with `v`, regarded as coordinates of the product space. -/
def incidenceSupport (G : SimpleGraph V) (v : V) : Finset (Edge G) :=
  Finset.univ.filter fun e ↦ v ∈ e.1.toFinset

@[simp] theorem mem_incidenceSupport {G : SimpleGraph V} {v : V}
    {e : Edge G} :
    e ∈ incidenceSupport G v ↔ v ∈ e.1.toFinset := by
  simp [incidenceSupport]

/-- Forget the host-edge subtype. -/
def edgeValEmbedding (G : SimpleGraph V) : Edge G ↪ Sym2 V :=
  Function.Embedding.subtype fun e : Sym2 V ↦ e ∈ G.edgeFinset

/-- The number of edge coordinates in a vertex support is its host degree. -/
theorem card_incidenceSupport (G : SimpleGraph V) (v : V) :
    (incidenceSupport G v).card = G.degree v := by
  rw [← SimpleGraph.card_incidenceFinset_eq_degree]
  have hmap :
      (incidenceSupport G v).map (edgeValEmbedding G) =
        G.incidenceFinset v := by
    rw [SimpleGraph.incidenceFinset_eq_filter]
    ext e
    simp [incidenceSupport, edgeValEmbedding, and_comm]
  rw [← hmap, card_map]

/-- Number of sampled edges incident with `v`. -/
def sampledDegree (G : SimpleGraph V) (v : V) (S : Finset (Edge G)) : ℕ :=
  (S ∩ incidenceSupport G v).card

/-- A finite edge support that is exactly the edge set of a cycle of length at
most `s` in `G`. -/
def IsShortCycleSupport (G : SimpleGraph V) (s : ℕ)
    (C : Finset (Edge G)) : Prop :=
  ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length ≤ s ∧
    ∀ e : Edge G, e ∈ C ↔ e.1 ∈ p.edges

/-- The finite type of distinct short-cycle edge supports. -/
abbrev ShortCycleSupport (G : SimpleGraph V) (s : ℕ) :=
  {C : Finset (Edge G) // IsShortCycleSupport G s C}

/-- A fixed witnessing basepoint for an indexed cycle support. -/
def cycleStart (G : SimpleGraph V) (s : ℕ)
    (C : ShortCycleSupport G s) : V :=
  Classical.choose C.2

/-- A fixed cycle witnessing an indexed cycle support. -/
def cycleWalk (G : SimpleGraph V) (s : ℕ)
    (C : ShortCycleSupport G s) :
    G.Walk (cycleStart G s C) (cycleStart G s C) :=
  Classical.choose (Classical.choose_spec C.2)

theorem cycleWalk_spec (G : SimpleGraph V) (s : ℕ)
    (C : ShortCycleSupport G s) :
    (cycleWalk G s C).IsCycle ∧
      (cycleWalk G s C).length ≤ s ∧
      ∀ e : Edge G, e ∈ C.1 ↔ e.1 ∈ (cycleWalk G s C).edges :=
  Classical.choose_spec (Classical.choose_spec C.2)

/-- Vertex events and short-cycle events form the complete event family in
Alon's extraction experiment. -/
abbrev Event (G : SimpleGraph V) (s : ℕ) :=
  V ⊕ ShortCycleSupport G s

/-- The coordinates on which an Alon bad event depends. -/
def support (G : SimpleGraph V) (s : ℕ) : Event G s → Finset (Edge G)
  | Sum.inl v => incidenceSupport G v
  | Sum.inr C => C.1

/-- The bad event attached to a vertex or a short cycle.  The degree window is
kept integral here; the logarithmic values are supplied at the quantitative
endpoint. -/
def bad (G : SimpleGraph V) (s lower upper : ℕ) :
    Event G s → Finset (Edge G) → Prop
  | Sum.inl v, S => sampledDegree G v S < lower ∨ upper < sampledDegree G v S
  | Sum.inr C, S => C.1 ⊆ S

private theorem agreesOn_inter_eq {E : Type*} [DecidableEq E]
    {R S T : Finset E}
    (h : Erdos76.FiniteNibble.AgreesOn R S T) :
    S ∩ R = T ∩ R :=
  h

/-- The degree-deviation event depends only on incident edge coordinates. -/
theorem vertex_bad_eventDependsOn (G : SimpleGraph V) (s lower upper : ℕ)
    (v : V) :
    Erdos76.FiniteNibble.EventDependsOn (support G s (Sum.inl v))
      (bad G s lower upper (Sum.inl v)) := by
  intro S T hST
  change
    ((S ∩ incidenceSupport G v).card < lower ∨
        upper < (S ∩ incidenceSupport G v).card) ↔
      ((T ∩ incidenceSupport G v).card < lower ∨
        upper < (T ∩ incidenceSupport G v).card)
  change S ∩ incidenceSupport G v = T ∩ incidenceSupport G v at hST
  rw [hST]

private theorem subset_iff_inter_eq_self {E : Type*} [DecidableEq E]
    {C S : Finset E} : C ⊆ S ↔ S ∩ C = C := by
  rw [inter_eq_right]

/-- Cycle survival depends only on the coordinates belonging to the cycle. -/
theorem cycle_bad_eventDependsOn (G : SimpleGraph V) (s lower upper : ℕ)
    (C : ShortCycleSupport G s) :
    Erdos76.FiniteNibble.EventDependsOn (support G s (Sum.inr C))
      (bad G s lower upper (Sum.inr C)) := by
  intro S T hST
  change C.1 ⊆ S ↔ C.1 ⊆ T
  change S ∩ C.1 = T ∩ C.1 at hST
  rw [subset_iff_inter_eq_self, subset_iff_inter_eq_self]
  rw [hST]

/-- Every bad event in the extraction experiment is local to its declared
edge-coordinate support. -/
theorem bad_eventDependsOn (G : SimpleGraph V) (s lower upper : ℕ) :
    ∀ i : Event G s,
      Erdos76.FiniteNibble.EventDependsOn (support G s i)
        (bad G s lower upper i) := by
  rintro (v | C)
  · exact vertex_bad_eventDependsOn G s lower upper v
  · exact cycle_bad_eventDependsOn G s lower upper C

/-- The canonical dependency neighbourhood consists of all distinct events
whose coordinate supports overlap. -/
def dependency (G : SimpleGraph V) (s : ℕ) (i : Event G s) :
    Finset (Event G s) :=
  Finset.univ.filter fun j ↦ j ≠ i ∧ ¬ Disjoint (support G s i) (support G s j)

theorem dependency_containsSupportOverlaps (G : SimpleGraph V) (s : ℕ) :
    Erdos76.FiniteNibble.ContainsSupportOverlaps (support G s)
      (dependency G s) := by
  intro i j hij hoverlap
  simp only [dependency, mem_filter, mem_univ, true_and]
  exact ⟨hij.symm, hoverlap⟩

/-- A short-cycle support has cardinality equal to the length of any cycle
witnessing it. -/
theorem card_shortCycleSupport_eq_length {G : SimpleGraph V} {s : ℕ}
    (C : ShortCycleSupport G s) {v : V} {p : G.Walk v v}
    (hp : p.IsCycle)
    (hC : ∀ e : Edge G, e ∈ C.1 ↔ e.1 ∈ p.edges) :
    C.1.card = p.length := by
  have hcardEdges : p.edges.toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hp.edges_nodup, p.length_edges]
  calc
    C.1.card = p.edges.toFinset.card := by
      apply Finset.card_bij (fun e _ ↦ e.1)
      · intro e he
        exact List.mem_toFinset.mpr ((hC e).mp he)
      · intro e _ f _ hef
        exact Subtype.ext hef
      · intro e he
        have heList : e ∈ p.edges := List.mem_toFinset.mp he
        have heGset : e ∈ G.edgeSet := p.edges_subset_edgeSet heList
        have heG : e ∈ G.edgeFinset := by
          simpa [SimpleGraph.mem_edgeFinset] using heGset
        refine ⟨⟨e, heG⟩, (hC ⟨e, heG⟩).mpr heList, rfl⟩
    _ = p.length := hcardEdges

/-- Consequently every indexed cycle support has between three and `s`
coordinates. -/
theorem shortCycleSupport_card_bounds {G : SimpleGraph V} {s : ℕ}
    (C : ShortCycleSupport G s) :
    3 ≤ C.1.card ∧ C.1.card ≤ s := by
  rcases C.2 with ⟨v, p, hp, hps, hC⟩
  rw [card_shortCycleSupport_eq_length C hp hC]
  exact ⟨hp.three_le_length, hps⟩

/-! ## Counting local cycle dependencies -/

/-- In a graph of maximum degree `D`, the number of length-`k` walks between
two fixed vertices is at most `D^k`.  This deliberately counts all walks;
later cycle counts inject into this larger and easier family. -/
theorem card_finsetWalkLength_le (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (k : ℕ) (u v : V) :
    (G.finsetWalkLength k u v).card ≤ D ^ k := by
  induction k generalizing u with
  | zero =>
      rw [pow_zero]
      apply card_le_one.mpr
      intro p hp q hq
      apply SimpleGraph.Walk.eq_of_length_le_one
      · rw [SimpleGraph.mem_finsetWalkLength_iff] at hp
        omega
      · rw [SimpleGraph.mem_finsetWalkLength_iff] at hq
        omega
  | succ k ih =>
      rw [SimpleGraph.finsetWalkLength]
      calc
        (Finset.univ.biUnion fun (w : G.neighborSet u) ↦
            (G.finsetWalkLength k w v).map
              ⟨fun p ↦ SimpleGraph.Walk.cons w.property p,
                fun _ _ h ↦ by
                  cases h
                  rfl⟩).card ≤
            (Finset.univ : Finset (G.neighborSet u)).card * D ^ k := by
          apply Finset.card_biUnion_le_card_mul
          intro w _
          rw [card_map]
          exact ih w
        _ = Fintype.card (G.neighborSet u) * D ^ k := by
            rw [card_univ]
        _ = G.degree u * D ^ k := by
            rw [SimpleGraph.card_neighborSet_eq_degree]
        _ ≤ D * D ^ k := Nat.mul_le_mul_right (D ^ k) (hdegree u)
        _ = D ^ (k + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Length-`k` walks with fixed initial vertex and arbitrary endpoint. -/
abbrev WalkFrom (G : SimpleGraph V) (u : V) (k : ℕ) :=
  Σ v : V, {p : G.Walk u v // p.length = k}

/-- Peeling the first edge is an exact description of positive-length walks
with fixed initial vertex. -/
def walkFromSuccEquiv (G : SimpleGraph V) (u : V) (k : ℕ) :
    WalkFrom G u (k + 1) ≃
      Σ w : G.neighborSet u, WalkFrom G w k where
  toFun x := by
    rcases x with ⟨v, p, hp⟩
    cases p with
    | nil => simp at hp
    | cons h p =>
        exact ⟨⟨_, h⟩, ⟨v, ⟨p, by simp at hp; omega⟩⟩⟩
  invFun x := by
    have hx : G.Adj u x.1.1 := by
      simpa only [SimpleGraph.mem_neighborSet] using x.1.2
    exact ⟨x.2.1, ⟨SimpleGraph.Walk.cons hx x.2.2.1, by
      simp [x.2.2.2]⟩⟩
  left_inv x := by
    rcases x with ⟨v, p, hp⟩
    cases p with
    | nil => simp at hp
    | cons h p => rfl
  right_inv x := by
    rcases x with ⟨⟨w, h⟩, v, p, hp⟩
    rfl

/-- In a graph of maximum degree `D`, there are at most `D^k` walks of
length `k` from a fixed initial vertex, even when the endpoint is arbitrary. -/
theorem card_walkFrom_le (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (k : ℕ) (u : V) :
    Fintype.card (WalkFrom G u k) ≤ D ^ k := by
  induction k generalizing u with
  | zero =>
      rw [pow_zero]
      apply Fintype.card_le_one_iff.mpr
      intro x y
      rcases x with ⟨vx, px, hpx⟩
      rcases y with ⟨vy, py, hpy⟩
      have hvx : u = vx := px.eq_of_length_eq_zero hpx
      have hvy : u = vy := py.eq_of_length_eq_zero hpy
      subst vx
      subst vy
      have hpEq : px = SimpleGraph.Walk.nil :=
        SimpleGraph.Walk.eq_nil_iff_nil.mpr
          (SimpleGraph.Walk.length_eq_zero_iff.mp hpx)
      have hqEq : py = SimpleGraph.Walk.nil :=
        SimpleGraph.Walk.eq_nil_iff_nil.mpr
          (SimpleGraph.Walk.length_eq_zero_iff.mp hpy)
      subst px
      subst py
      rfl
  | succ k ih =>
      rw [Fintype.card_congr (walkFromSuccEquiv G u k), Fintype.card_sigma]
      calc
        (∑ w : G.neighborSet u, Fintype.card (WalkFrom G w k)) ≤
            ∑ _w : G.neighborSet u, D ^ k := by
          apply sum_le_sum
          intro w _
          exact ih w
        _ = (Finset.univ : Finset (G.neighborSet u)).card * D ^ k := by
          rw [sum_const, Nat.nsmul_eq_mul]
        _ = Fintype.card (G.neighborSet u) * D ^ k := by
          rw [card_univ]
        _ = G.degree u * D ^ k := by
          rw [SimpleGraph.card_neighborSet_eq_degree]
        _ ≤ D * D ^ k := Nat.mul_le_mul_right (D ^ k) (hdegree u)
        _ = D ^ (k + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Rooted cycle walks of length `n + 1`. -/
def RootedCycleWalk (G : SimpleGraph V) (n : ℕ) (u : V) :=
  {p : {p : G.Walk u u // p.length = n + 1} // p.1.IsCycle}

noncomputable instance rootedCycleWalkFintype (G : SimpleGraph V)
    (n : ℕ) (u : V) : Fintype (RootedCycleWalk G n u) := by
  unfold RootedCycleWalk
  infer_instance

/-- Close a prefix when its endpoint is adjacent to its prescribed root. -/
def closeWalkFrom (G : SimpleGraph V) {u : V} {n : ℕ}
    (p : WalkFrom G u n) : G.Walk u u :=
  if h : G.Adj p.1 u then p.2.1.concat h else SimpleGraph.Walk.nil

/-- Delete the closing edge of a rooted cycle. -/
def RootedCycleWalk.toWalkFrom (G : SimpleGraph V) {n : ℕ} {u : V}
    (p : RootedCycleWalk G n u) : WalkFrom G u n :=
  ⟨p.1.1.penultimate, ⟨p.1.1.dropLast, by
    rw [SimpleGraph.Walk.length_dropLast, p.1.2]
    omega⟩⟩

@[simp] theorem closeWalkFrom_toWalkFrom (G : SimpleGraph V)
    {n : ℕ} {u : V} (p : RootedCycleWalk G n u) :
    closeWalkFrom G p.toWalkFrom = p.1.1 := by
  unfold closeWalkFrom RootedCycleWalk.toWalkFrom
  rw [dif_pos (p.1.1.adj_penultimate p.2.not_nil)]
  exact p.1.1.concat_dropLast _

theorem RootedCycleWalk.toWalkFrom_injective (G : SimpleGraph V)
    {n : ℕ} {u : V} :
    Function.Injective
      (RootedCycleWalk.toWalkFrom G :
        RootedCycleWalk G n u → WalkFrom G u n) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (closeWalkFrom G) hpq
  simpa using h

theorem card_rootedCycleWalk_le_pow (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (n : ℕ) (u : V) :
    Fintype.card (RootedCycleWalk G n u) ≤ D ^ n := by
  exact (Fintype.card_le_of_injective (RootedCycleWalk.toWalkFrom G)
    (RootedCycleWalk.toWalkFrom_injective G)).trans
      (card_walkFrom_le G D hdegree n u)

/-- Exact-length short-cycle supports containing an edge incident with `u`.
The length is written `n + 1` to expose the exponent in the walk count. -/
def ShortCycleSupportAtVertexLength (G : SimpleGraph V) (s n : ℕ) (u : V) :=
  {C : ShortCycleSupport G s //
    C.1.card = n + 1 ∧ ∃ e ∈ C.1, u ∈ e.1.toFinset}

noncomputable instance shortCycleSupportAtVertexLengthFintype
    (G : SimpleGraph V) (s n : ℕ) (u : V) :
    Fintype (ShortCycleSupportAtVertexLength G s n u) := by
  unfold ShortCycleSupportAtVertexLength
  infer_instance

lemma mem_cycleWalk_support_of_mem_cycleSupport
    {G : SimpleGraph V} {s n : ℕ} {u : V}
    (C : ShortCycleSupportAtVertexLength G s n u) :
    u ∈ (cycleWalk G s C.1).support := by
  rcases C.2.2 with ⟨e, heC, hue⟩
  have hep : e.1 ∈ (cycleWalk G s C.1).edges :=
    ((cycleWalk_spec G s C.1).2.2 e).mp heC
  exact SimpleGraph.Walk.mem_support_of_mem_edges hep
    (Sym2.mem_toFinset.mp hue)

/-- Rotate the chosen support witness to the prescribed vertex. -/
def ShortCycleSupportAtVertexLength.toRootedCycleWalk
    {G : SimpleGraph V} {s n : ℕ} {u : V}
    (C : ShortCycleSupportAtVertexLength G s n u) :
    RootedCycleWalk G n u := by
  let hu : u ∈ (cycleWalk G s C.1).support :=
    mem_cycleWalk_support_of_mem_cycleSupport C
  let q := (cycleWalk G s C.1).rotate u hu
  refine ⟨⟨q, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.length_rotate]
    rw [← card_shortCycleSupport_eq_length C.1
      (cycleWalk_spec G s C.1).1 (cycleWalk_spec G s C.1).2.2]
    exact C.2.1
  · exact (cycleWalk_spec G s C.1).1.rotate hu

lemma ShortCycleSupportAtVertexLength.mem_iff_mem_toRootedCycleWalk_edges
    {G : SimpleGraph V} {s n : ℕ} {u : V}
    (C : ShortCycleSupportAtVertexLength G s n u) (e : Edge G) :
    e ∈ C.1.1 ↔ e.1 ∈ C.toRootedCycleWalk.1.1.edges := by
  let hu : u ∈ (cycleWalk G s C.1).support :=
    mem_cycleWalk_support_of_mem_cycleSupport C
  have hrotate := (cycleWalk G s C.1).rotate_edges u hu
  change e ∈ C.1.1 ↔
    e.1 ∈ ((cycleWalk G s C.1).rotate u hu).edges
  rw [(cycleWalk_spec G s C.1).2.2 e]
  exact hrotate.perm.mem_iff.symm

theorem ShortCycleSupportAtVertexLength.toRootedCycleWalk_injective
    {G : SimpleGraph V} {s n : ℕ} {u : V} :
    Function.Injective
      (ShortCycleSupportAtVertexLength.toRootedCycleWalk :
        ShortCycleSupportAtVertexLength G s n u → RootedCycleWalk G n u) := by
  intro C D hCD
  apply Subtype.ext
  apply Subtype.ext
  ext e
  rw [C.mem_iff_mem_toRootedCycleWalk_edges,
    D.mem_iff_mem_toRootedCycleWalk_edges]
  simpa only [eq_iff_iff] using
    congrArg (fun q : RootedCycleWalk G n u ↦ e.1 ∈ q.1.1.edges) hCD

/-- At most `D^n` distinct cycle supports of length `n + 1` contain a
prescribed vertex. -/
theorem card_shortCycleSupportAtVertexLength_le_pow
    (G : SimpleGraph V) (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (s n : ℕ) (u : V) :
    Fintype.card (ShortCycleSupportAtVertexLength G s n u) ≤ D ^ n := by
  exact (Fintype.card_le_of_injective
    ShortCycleSupportAtVertexLength.toRootedCycleWalk
    ShortCycleSupportAtVertexLength.toRootedCycleWalk_injective).trans
      (card_rootedCycleWalk_le_pow G D hdegree n u)

/-- Finset form of the preceding bound, convenient for dependency filters. -/
theorem card_filter_shortCycleSupportAtVertexLength_le_pow
    (G : SimpleGraph V) (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (s n : ℕ) (u : V) :
    (Finset.univ.filter fun C : ShortCycleSupport G s ↦
      C.1.card = n + 1 ∧ ∃ e ∈ C.1, u ∈ e.1.toFinset).card ≤ D ^ n := by
  rw [← Fintype.card_subtype]
  exact card_shortCycleSupportAtVertexLength_le_pow G D hdegree s n u

/-- Overlap with a vertex support is precisely containment of a cycle edge
incident with that vertex. -/
theorem not_disjoint_incidenceSupport_iff {G : SimpleGraph V} {v : V}
    {C : Finset (Edge G)} :
    ¬ Disjoint (incidenceSupport G v) C ↔
      ∃ e ∈ C, v ∈ e.1.toFinset := by
  rw [Finset.not_disjoint_iff]
  constructor
  · rintro ⟨e, heI, heC⟩
    exact ⟨e, heC, (mem_incidenceSupport.mp heI)⟩
  · rintro ⟨e, heC, hve⟩
    exact ⟨e, mem_incidenceSupport.mpr hve, heC⟩

/-- Per exact length, the number of cycle events adjacent to a vertex event
has Alon's `D^(length-1)` bound. -/
theorem card_filter_cycle_overlap_vertex_le_pow
    (G : SimpleGraph V) (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (s n : ℕ) (u : V) :
    (Finset.univ.filter fun C : ShortCycleSupport G s ↦
      C.1.card = n + 1 ∧
        ¬ Disjoint (incidenceSupport G u) C.1).card ≤ D ^ n := by
  have hfilters :
      (Finset.univ.filter fun C : ShortCycleSupport G s ↦
        C.1.card = n + 1 ∧
          ¬ Disjoint (incidenceSupport G u) C.1) =
      (Finset.univ.filter fun C : ShortCycleSupport G s ↦
        C.1.card = n + 1 ∧ ∃ e ∈ C.1, u ∈ e.1.toFinset) := by
    ext C
    simp only [mem_filter, mem_univ, true_and]
    rw [not_disjoint_incidenceSupport_iff]
  rw [hfilters]
  exact card_filter_shortCycleSupportAtVertexLength_le_pow
    G D hdegree s n u

/-! ### Cycle supports through a prescribed edge -/

/-- A cycle of length `n + 2` with prescribed first oriented edge. -/
def EdgeRootedCycleWalk (G : SimpleGraph V) (n : ℕ)
    {u v : V} (huv : G.Adj u v) :=
  {p : {p : G.Walk v u // p.length = n + 1} //
    (SimpleGraph.Walk.cons huv p.1).IsCycle}

noncomputable instance edgeRootedCycleWalkFintype (G : SimpleGraph V)
    (n : ℕ) {u v : V} (huv : G.Adj u v) :
    Fintype (EdgeRootedCycleWalk G n huv) := by
  unfold EdgeRootedCycleWalk
  infer_instance

/-- Close a prefix after adjoining a prescribed initial edge. -/
def closeEdgeWalkFrom (G : SimpleGraph V) {u v : V}
    (huv : G.Adj u v) {n : ℕ} (p : WalkFrom G v n) : G.Walk u u :=
  if h : G.Adj p.1 u then
    SimpleGraph.Walk.cons huv (p.2.1.concat h)
  else SimpleGraph.Walk.nil

/-- Delete the final closing edge of the tail. -/
def EdgeRootedCycleWalk.toWalkFrom (G : SimpleGraph V)
    {n : ℕ} {u v : V} {huv : G.Adj u v}
    (p : EdgeRootedCycleWalk G n huv) : WalkFrom G v n :=
  ⟨p.1.1.penultimate, ⟨p.1.1.dropLast, by
    rw [SimpleGraph.Walk.length_dropLast, p.1.2]
    omega⟩⟩

@[simp] theorem closeEdgeWalkFrom_toWalkFrom (G : SimpleGraph V)
    {n : ℕ} {u v : V} {huv : G.Adj u v}
    (p : EdgeRootedCycleWalk G n huv) :
    closeEdgeWalkFrom G huv p.toWalkFrom =
      SimpleGraph.Walk.cons huv p.1.1 := by
  have hpnot : ¬ p.1.1.Nil := by
    intro hp
    have hz : p.1.1.length = 0 :=
      SimpleGraph.Walk.length_eq_zero_iff.mpr hp
    rw [p.1.2] at hz
    have hcycle := p.2.three_le_length
    simp only [SimpleGraph.Walk.length_cons, p.1.2] at hcycle
    omega
  unfold closeEdgeWalkFrom EdgeRootedCycleWalk.toWalkFrom
  rw [dif_pos (p.1.1.adj_penultimate hpnot)]
  rw [p.1.1.concat_dropLast]

theorem EdgeRootedCycleWalk.toWalkFrom_injective (G : SimpleGraph V)
    {n : ℕ} {u v : V} {huv : G.Adj u v} :
    Function.Injective
      (EdgeRootedCycleWalk.toWalkFrom G :
        EdgeRootedCycleWalk G n huv → WalkFrom G v n) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (closeEdgeWalkFrom G huv) hpq
  simpa using h

/-- There are at most `D^n` oriented cycles of length `n + 2` through a
prescribed initial oriented edge. -/
theorem card_edgeRootedCycleWalk_le_pow (G : SimpleGraph V) (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (n : ℕ)
    {u v : V} (huv : G.Adj u v) :
    Fintype.card (EdgeRootedCycleWalk G n huv) ≤ D ^ n := by
  exact (Fintype.card_le_of_injective (EdgeRootedCycleWalk.toWalkFrom G)
    (EdgeRootedCycleWalk.toWalkFrom_injective G)).trans
      (card_walkFrom_le G D hdegree n v)

private lemma snd_dropLast_eq_snd_of_two_le_length {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : 2 ≤ p.length) :
    p.dropLast.snd = p.snd := by
  cases p with
  | nil => simp at hp
  | cons h p =>
      cases p with
      | nil => simp at hp
      | cons h' p =>
          rw [SimpleGraph.Walk.dropLast_cons_cons]
          exact SimpleGraph.Walk.snd_cons _ h

/-- Repackage a rooted cycle whose second vertex is `v` as a cycle with the
prescribed first edge `u→v`. -/
def EdgeRootedCycleWalk.ofCycle (G : SimpleGraph V)
    {n : ℕ} {u v : V} (huv : G.Adj u v) (p : G.Walk u u)
    (hp : p.IsCycle) (hlength : p.length = n + 2) (hsnd : p.snd = v) :
    EdgeRootedCycleWalk G n huv := by
  have hpnil : ¬ p.Nil := hp.not_nil
  let tail : G.Walk v u := p.tail.copy hsnd rfl
  refine ⟨⟨tail, ?_⟩, ?_⟩
  · simp only [tail, SimpleGraph.Walk.length_copy,
      SimpleGraph.Walk.length_tail, hlength]
    omega
  · have heq : SimpleGraph.Walk.cons huv tail = p := by
      apply SimpleGraph.Walk.ext_support
      simp only [SimpleGraph.Walk.support_cons, tail,
        SimpleGraph.Walk.support_copy]
      exact p.cons_support_tail hpnil
    rw [heq]
    exact hp

@[simp] lemma EdgeRootedCycleWalk.cons_ofCycle (G : SimpleGraph V)
    {n : ℕ} {u v : V} (huv : G.Adj u v) (p : G.Walk u u)
    (hp : p.IsCycle) (hlength : p.length = n + 2) (hsnd : p.snd = v) :
    SimpleGraph.Walk.cons huv
      (EdgeRootedCycleWalk.ofCycle G huv p hp hlength hsnd).1.1 = p := by
  apply SimpleGraph.Walk.ext_support
  unfold EdgeRootedCycleWalk.ofCycle
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_copy]
  exact p.cons_support_tail hp.not_nil

/-- The edge coordinate underlying a graph dart. -/
def dartEdgeCoordinate (G : SimpleGraph V) (d : G.Dart) : Edge G :=
  ⟨d.edge, by simpa [SimpleGraph.mem_edgeFinset] using d.edge_mem⟩

/-- Exact-length short-cycle supports containing a prescribed oriented edge.
Membership is undirected; the orientation only fixes a canonical code. -/
def ShortCycleSupportAtDartLength (G : SimpleGraph V) (s n : ℕ)
    (d : G.Dart) :=
  {C : ShortCycleSupport G s //
    C.1.card = n + 2 ∧ dartEdgeCoordinate G d ∈ C.1}

noncomputable instance shortCycleSupportAtDartLengthFintype
    (G : SimpleGraph V) (s n : ℕ) (d : G.Dart) :
    Fintype (ShortCycleSupportAtDartLength G s n d) := by
  unfold ShortCycleSupportAtDartLength
  infer_instance

def ShortCycleSupportAtDartLength.toVertex
    {G : SimpleGraph V} {s n : ℕ} {d : G.Dart}
    (C : ShortCycleSupportAtDartLength G s n d) :
    ShortCycleSupportAtVertexLength G s (n + 1) d.fst := by
  refine ⟨C.1, ?_, ?_⟩
  · simpa [Nat.add_assoc] using C.2.1
  · refine ⟨dartEdgeCoordinate G d, C.2.2, ?_⟩
    simp [dartEdgeCoordinate, SimpleGraph.Dart.edge]

/-- A cycle support containing `d` admits a cyclic enumeration whose first
oriented edge is exactly `d`. -/
lemma exists_oriented_cycleWalk_of_mem_dart
    {G : SimpleGraph V} {s n : ℕ} {d : G.Dart}
    (C : ShortCycleSupportAtDartLength G s n d) :
    ∃ p : G.Walk d.fst d.fst,
      p.IsCycle ∧ p.length = n + 2 ∧ p.snd = d.snd ∧
        ∀ e : Edge G, e ∈ C.1.1 ↔ e.1 ∈ p.edges := by
  let Cv := C.toVertex
  let p : G.Walk d.fst d.fst := Cv.toRootedCycleWalk.1.1
  have hpcycle : p.IsCycle := Cv.toRootedCycleWalk.2
  have hplength : p.length = n + 2 := by
    simpa [p, Cv, Nat.add_assoc] using Cv.toRootedCycleWalk.1.2
  have hsupport (e : Edge G) : e ∈ C.1.1 ↔ e.1 ∈ p.edges :=
    Cv.mem_iff_mem_toRootedCycleWalk_edges e
  have hdmem : d.edge ∈ p.edges := by
    simpa [dartEdgeCoordinate] using
      (hsupport (dartEdgeCoordinate G d)).mp C.2.2
  have hpnot : ¬ p.Nil := hpcycle.not_nil
  have hedges : p.edges ≠ [] := SimpleGraph.Walk.edges_eq_nil.not.mpr hpnot
  by_cases hlast : d.edge = p.edges.getLast hedges
  · have hedgeEq : s(d.fst, d.snd) = s(p.penultimate, d.fst) := by
      calc
        s(d.fst, d.snd) = d.edge := by rfl
        _ = p.edges.getLast hedges := hlast
        _ = s(p.penultimate, d.fst) :=
          p.getLast_edges_eq_mk_penultimate_end hedges
    have hsnd : p.penultimate = d.snd := by
      rw [Sym2.eq, Sym2.rel_iff] at hedgeEq
      rcases hedgeEq with h | h
      · exact (d.snd_ne_fst h.2).elim
      · exact h.2.symm
    refine ⟨p.reverse, hpcycle.reverse, ?_, ?_, ?_⟩
    · simpa using hplength
    · simpa [SimpleGraph.Walk.snd_reverse, hsnd]
    · intro e
      rw [hsupport e]
      simp
  · have hdDrop : d.edge ∈ p.edges.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hdmem hlast
    have hdPrefix : d.edge ∈ p.dropLast.edges := by
      simpa using hdDrop
    have hsndPrefix : d.snd = p.dropLast.snd := by
      exact hpcycle.isPath_dropLast.eq_snd_of_mem_edges
        (by simpa [SimpleGraph.Dart.edge] using hdPrefix)
    have htwo : 2 ≤ p.length := hpcycle.three_le_length.trans' (by omega)
    have hsnd : p.snd = d.snd := by
      rw [snd_dropLast_eq_snd_of_two_le_length p htwo] at hsndPrefix
      exact hsndPrefix.symm
    exact ⟨p, hpcycle, hplength, hsnd, hsupport⟩

/-- A fixed oriented enumeration supplied by the preceding existence lemma. -/
def orientedCycleWalk {G : SimpleGraph V} {s n : ℕ} {d : G.Dart}
    (C : ShortCycleSupportAtDartLength G s n d) : G.Walk d.fst d.fst :=
  Classical.choose (exists_oriented_cycleWalk_of_mem_dart C)

theorem orientedCycleWalk_spec {G : SimpleGraph V} {s n : ℕ} {d : G.Dart}
    (C : ShortCycleSupportAtDartLength G s n d) :
    (orientedCycleWalk C).IsCycle ∧
      (orientedCycleWalk C).length = n + 2 ∧
      (orientedCycleWalk C).snd = d.snd ∧
      ∀ e : Edge G, e ∈ C.1.1 ↔ e.1 ∈ (orientedCycleWalk C).edges :=
  Classical.choose_spec (exists_oriented_cycleWalk_of_mem_dart C)

def ShortCycleSupportAtDartLength.toEdgeRootedCycleWalk
    {G : SimpleGraph V} {s n : ℕ} {d : G.Dart}
    (C : ShortCycleSupportAtDartLength G s n d) :
    EdgeRootedCycleWalk G n d.adj :=
  EdgeRootedCycleWalk.ofCycle G d.adj (orientedCycleWalk C)
    (orientedCycleWalk_spec C).1 (orientedCycleWalk_spec C).2.1
    (orientedCycleWalk_spec C).2.2.1

lemma ShortCycleSupportAtDartLength.mem_iff_mem_toEdgeRootedCycleWalk_edges
    {G : SimpleGraph V} {s n : ℕ} {d : G.Dart}
    (C : ShortCycleSupportAtDartLength G s n d) (e : Edge G) :
    e ∈ C.1.1 ↔
      e.1 ∈ (SimpleGraph.Walk.cons d.adj
        C.toEdgeRootedCycleWalk.1.1).edges := by
  rw [(orientedCycleWalk_spec C).2.2.2 e]
  unfold ShortCycleSupportAtDartLength.toEdgeRootedCycleWalk
  change e.1 ∈ (orientedCycleWalk C).edges ↔ _
  rw [EdgeRootedCycleWalk.cons_ofCycle]

theorem ShortCycleSupportAtDartLength.toEdgeRootedCycleWalk_injective
    {G : SimpleGraph V} {s n : ℕ} {d : G.Dart} :
    Function.Injective
      (ShortCycleSupportAtDartLength.toEdgeRootedCycleWalk :
        ShortCycleSupportAtDartLength G s n d →
          EdgeRootedCycleWalk G n d.adj) := by
  intro C D hCD
  apply Subtype.ext
  apply Subtype.ext
  ext e
  rw [C.mem_iff_mem_toEdgeRootedCycleWalk_edges,
    D.mem_iff_mem_toEdgeRootedCycleWalk_edges]
  simpa only [eq_iff_iff] using congrArg
    (fun q : EdgeRootedCycleWalk G n d.adj ↦
      e.1 ∈ (SimpleGraph.Walk.cons d.adj q.1.1).edges) hCD

theorem card_shortCycleSupportAtDartLength_le_pow
    (G : SimpleGraph V) (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (s n : ℕ) (d : G.Dart) :
    Fintype.card (ShortCycleSupportAtDartLength G s n d) ≤ D ^ n := by
  exact (Fintype.card_le_of_injective
    ShortCycleSupportAtDartLength.toEdgeRootedCycleWalk
    ShortCycleSupportAtDartLength.toEdgeRootedCycleWalk_injective).trans
      (card_edgeRootedCycleWalk_le_pow G D hdegree n d.adj)

private theorem sym2_mk_out (e : Sym2 V) : s(e.out.1, e.out.2) = e := by
  simpa [Sym2.mk] using e.out_eq

/-- A deterministic orientation of an edge coordinate. -/
def edgeDart (G : SimpleGraph V) (e : Edge G) : G.Dart :=
  ⟨(e.1.out.1, e.1.out.2), by
    rw [← G.mem_edgeSet, sym2_mk_out]
    exact SimpleGraph.mem_edgeFinset.mp e.2⟩

@[simp] theorem dartEdgeCoordinate_edgeDart (G : SimpleGraph V) (e : Edge G) :
    dartEdgeCoordinate G (edgeDart G e) = e := by
  apply Subtype.ext
  simp [dartEdgeCoordinate, edgeDart, SimpleGraph.Dart.edge, sym2_mk_out]

/-- Finset form of the prescribed-dart exact-length cycle count. -/
theorem card_filter_cycle_containing_dart_le_pow
    (G : SimpleGraph V) (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (s n : ℕ) (d : G.Dart) :
    (Finset.univ.filter fun C : ShortCycleSupport G s ↦
      C.1.card = n + 2 ∧ dartEdgeCoordinate G d ∈ C.1).card ≤ D ^ n := by
  rw [← Fintype.card_subtype]
  change Fintype.card (ShortCycleSupportAtDartLength G s n d) ≤ D ^ n
  exact card_shortCycleSupportAtDartLength_le_pow G D hdegree s n d

/-- The orientation chosen for an edge coordinate does not change the
prescribed-edge support family. -/
theorem card_filter_cycle_containing_edge_le_pow
    (G : SimpleGraph V) (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (s n : ℕ) (e : Edge G) :
    (Finset.univ.filter fun C : ShortCycleSupport G s ↦
      C.1.card = n + 2 ∧ e ∈ C.1).card ≤ D ^ n := by
  have hfilters :
      (Finset.univ.filter fun C : ShortCycleSupport G s ↦
        C.1.card = n + 2 ∧ e ∈ C.1) =
      (Finset.univ.filter fun C : ShortCycleSupport G s ↦
        C.1.card = n + 2 ∧
          dartEdgeCoordinate G (edgeDart G e) ∈ C.1) := by
    rw [dartEdgeCoordinate_edgeDart]
  rw [hfilters]
  exact card_filter_cycle_containing_dart_le_pow
    G D hdegree s n (edgeDart G e)

/-- The exact local overlap count for cycle events: a fixed support `C`
meets at most `|C|·D^n` supports of length `n+2`. -/
theorem card_filter_cycle_overlap_cycle_le
    (G : SimpleGraph V) (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (s n : ℕ) (C : Finset (Edge G)) :
    (Finset.univ.filter fun K : ShortCycleSupport G s ↦
      K.1.card = n + 2 ∧ ¬ Disjoint C K.1).card ≤
        C.card * D ^ n := by
  let family : Edge G → Finset (ShortCycleSupport G s) := fun e ↦
    Finset.univ.filter fun K ↦ K.1.card = n + 2 ∧ e ∈ K.1
  have hfamily (e : Edge G) : (family e).card ≤ D ^ n := by
    exact card_filter_cycle_containing_edge_le_pow G D hdegree s n e
  have hfilter :
      (Finset.univ.filter fun K : ShortCycleSupport G s ↦
        K.1.card = n + 2 ∧ ¬ Disjoint C K.1) =
        C.biUnion family := by
    ext K
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, family]
    rw [Finset.not_disjoint_iff]
    constructor
    · rintro ⟨hlen, e, heC, heK⟩
      exact ⟨e, heC, hlen, heK⟩
    · rintro ⟨e, heC, hlen, heK⟩
      exact ⟨hlen, e, heC, heK⟩
  rw [hfilter]
  exact Finset.card_biUnion_le_card_mul C family (D ^ n)
    (fun e _ ↦ hfamily e)

/-- Exact mass of the event that all coordinates in `C` are selected in an
independent, constant-parameter Bernoulli edge sample. -/
theorem cycle_eventMass_eq_pow {G : SimpleGraph V} (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (C : Finset (Edge G)) :
    Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset (Edge G) ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S)
        (fun S ↦ C ⊆ S) = q ^ C.card := by
  let mass : Finset (Edge G) → ℝ := fun S ↦
    Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S
  have hmem (e : Edge G) :
      Erdos76.FiniteLocalLemma.eventMass mass (fun S ↦ e ∈ S) = q := by
    have hlocal :
        Erdos76.FiniteNibble.EventDependsOn ({e} : Finset (Edge G))
          (fun S ↦ e ∈ S) := by
      intro S T hST
      change S ∩ {e} = T ∩ {e} at hST
      simpa [Finset.ext_iff] using congrArg (fun X ↦ e ∈ X) hST
    rw [Erdos76.FiniteNibble.eventMass_eq_restrictedEventMass hlocal]
    unfold Erdos76.FiniteNibble.restrictedEventMass
    rw [Fintype.sum_eq_single
      (show Erdos76.FiniteNibble.Subsets ({e} : Finset (Edge G)) from
        ⟨{e}, Subset.rfl⟩)]
    · simp [Erdos76.FiniteNibble.bernoulliMass]
    · intro S hS
      have heS : e ∉ S.1 := by
        intro he
        apply hS
        apply Subtype.ext
        exact Finset.Subset.antisymm S.2 (singleton_subset_iff.mpr he)
      simp [heS]
  induction C using Finset.induction_on with
  | empty =>
      have hlocal :
          Erdos76.FiniteNibble.EventDependsOn
            (∅ : Finset (Edge G)) (fun _ ↦ True) :=
        Erdos76.FiniteNibble.eventDependsOn_true ∅
      rw [show (fun S : Finset (Edge G) ↦ ∅ ⊆ S) = (fun _ ↦ True) by
        funext S; simp]
      rw [Erdos76.FiniteNibble.eventMass_eq_restrictedEventMass hlocal]
      unfold Erdos76.FiniteNibble.restrictedEventMass
      rw [Fintype.sum_eq_single
        (show Erdos76.FiniteNibble.Subsets (∅ : Finset (Edge G)) from
          ⟨∅, Subset.rfl⟩)]
      · simp [Erdos76.FiniteNibble.bernoulliMass]
      · intro S hS
        exfalso
        apply hS
        apply Subtype.ext
        exact Finset.Subset.antisymm S.2 (empty_subset _)
  | @insert e C he ih =>
      have hlocalMem :
          Erdos76.FiniteNibble.EventDependsOn ({e} : Finset (Edge G))
            (fun S ↦ e ∈ S) := by
        intro S T hST
        change S ∩ {e} = T ∩ {e} at hST
        simpa [Finset.ext_iff] using congrArg (fun X ↦ e ∈ X) hST
      have hlocalC :
          Erdos76.FiniteNibble.EventDependsOn C (fun S ↦ C ⊆ S) := by
        intro S T hST
        change S ∩ C = T ∩ C at hST
        change C ⊆ S ↔ C ⊆ T
        rw [subset_iff_inter_eq_self, subset_iff_inter_eq_self, hST]
      have hfactor := Erdos76.FiniteNibble.eventMass_and_of_disjoint
        (p := fun _ : Edge G ↦ q)
        (R := ({e} : Finset (Edge G))) (T := C)
        (A := fun S ↦ e ∈ S) (B := fun S ↦ C ⊆ S)
        (Finset.disjoint_singleton_left.mpr he) hlocalMem hlocalC
      change Erdos76.FiniteLocalLemma.eventMass mass
          (fun S ↦ insert e C ⊆ S) = q ^ (insert e C).card
      calc
        Erdos76.FiniteLocalLemma.eventMass mass
            (fun S ↦ insert e C ⊆ S) =
            Erdos76.FiniteLocalLemma.eventMass mass
              (fun S ↦ e ∈ S ∧ C ⊆ S) := by
          unfold Erdos76.FiniteLocalLemma.eventMass
          apply Finset.sum_congr rfl
          intro S _
          have hins : insert e C ⊆ S ↔ e ∈ S ∧ C ⊆ S :=
            insert_subset_iff
          by_cases h : e ∈ S ∧ C ⊆ S
          · simp [h, hins.mpr h]
          · have hnins : ¬ insert e C ⊆ S := fun hs ↦ h (hins.mp hs)
            simp [h, hnins]
        _ = Erdos76.FiniteLocalLemma.eventMass mass (fun S ↦ e ∈ S) *
              Erdos76.FiniteLocalLemma.eventMass mass (fun S ↦ C ⊆ S) := by
          simpa [mass] using hfactor
        _ = q * q ^ C.card := by rw [hmem, ih]
        _ = q ^ (insert e C).card := by
          rw [card_insert_of_notMem he, pow_succ]
          ring

/-- Specialisation of the preceding identity to an indexed short cycle. -/
theorem indexed_cycle_eventMass_eq_pow {G : SimpleGraph V} {s lower upper : ℕ}
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (C : ShortCycleSupport G s) :
    Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset (Edge G) ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S)
        (bad G s lower upper (Sum.inr C)) = q ^ C.1.card := by
  exact cycle_eventMass_eq_pow q hq0 hq1 C.1

/-! ## Vertex-event estimates -/

/-- The restricted Bernoulli mass is the filtered powerset sum used by the
Chernoff estimates in `Erdos697`. -/
theorem restrictedEventMass_eq_sum_filter {E : Type*} [Fintype E]
    [DecidableEq E] (R : Finset E) (p : E → ℝ)
    (event : Finset E → Prop) :
    Erdos76.FiniteNibble.restrictedEventMass R p event =
      ∑ T ∈ R.powerset,
        if event T then Erdos697.Bernoulli.weight R p T else 0 := by
  unfold Erdos76.FiniteNibble.restrictedEventMass
  calc
    (∑ S : Erdos76.FiniteNibble.Subsets R,
        if event S.1 then
          Erdos76.FiniteNibble.bernoulliMass R p S.1 else 0) =
        ∑ S : ↥R.powerset,
          if event S.1 then
            Erdos76.FiniteNibble.bernoulliMass R p S.1 else 0 := by
      apply Fintype.sum_equiv
        (Erdos76.FiniteNibble.subsetsEquivPowersetAttach R)
      intro S
      rfl
    _ = ∑ T ∈ R.powerset,
          if event T then
            Erdos76.FiniteNibble.bernoulliMass R p T else 0 := by
      simpa using
        (Finset.sum_attach R.powerset (fun T : Finset E ↦
          if event T then
            Erdos76.FiniteNibble.bernoulliMass R p T else 0))
    _ = ∑ T ∈ R.powerset,
          if event T then Erdos697.Bernoulli.weight R p T else 0 := by
      apply sum_congr rfl
      intro T hT
      by_cases h : event T
      · simp only [h, if_true]
        unfold Erdos76.FiniteNibble.bernoulliMass Erdos697.Bernoulli.weight
        rfl
      · simp [h]

/-- A two-sided degree-deviation estimate, packaged in the restricted-product
representation used by the local-event encoding.  The upper cutoff is
`upper + 1`, since the bad event uses the strict inequality `upper < |T|`. -/
theorem restricted_card_outside_mass_le {E : Type*} [Fintype E]
    [DecidableEq E] (R : Finset E) (p : E → ℝ)
    (hp0 : ∀ e ∈ R, 0 ≤ p e) (hp1 : ∀ e ∈ R, p e ≤ 1)
    {lower upper : ℕ} {EW rLower rUpper : ℝ}
    (hEW : EW = ∑ e ∈ R, p e)
    (hrLower0 : 0 < rLower) (hrLower1 : rLower < 1)
    (hrUpper : 1 < rUpper)
    (hlower : (lower : ℝ) ≤ rLower * EW)
    (hupper : rUpper * EW ≤ ((upper + 1 : ℕ) : ℝ)) :
    Erdos76.FiniteNibble.restrictedEventMass R p
        (fun T ↦ T.card < lower ∨ upper < T.card) ≤
      Real.exp
          ((rLower * ((1 - rLower) / (2 * rLower)) +
              (1 / (1 + ((1 - rLower) / (2 * rLower))) - 1)) * EW) +
        Real.exp
          (((-(rUpper * ((rUpper - 1) / (2 * rUpper)))) +
              (1 / (1 - ((rUpper - 1) / (2 * rUpper))) - 1)) * EW) := by
  let event : Finset E → Prop :=
    fun T ↦ T.card < lower ∨ upper < T.card
  change Erdos76.FiniteNibble.restrictedEventMass R p event ≤ _
  have hsplit :
      (∑ T ∈ R.powerset,
          @ite ℝ (event T) (Classical.propDecidable _)
            (Erdos697.Bernoulli.weight R p T) 0) ≤
        (∑ T ∈ R.powerset.filter (fun T ↦ T.card < lower),
          Erdos697.Bernoulli.weight R p T) +
        (∑ T ∈ R.powerset.filter
            (fun T ↦ upper + 1 ≤ T.card),
          Erdos697.Bernoulli.weight R p T) := by
    simp_rw [sum_filter]
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro T hTR
    have hw : 0 ≤ Erdos697.Bernoulli.weight R p T :=
      Erdos697.Bernoulli.weight_nonneg R p hp0 hp1 hTR
    by_cases hlo : T.card < lower
    · simp only [event, hlo, true_or, if_true]
      split_ifs <;> linarith
    · by_cases hup : upper < T.card
      · have hup' : upper + 1 ≤ T.card := by omega
        simp [event, hlo, hup, hup', hw]
      · have hup' : ¬ upper + 1 ≤ T.card := by omega
        simp [event, hlo, hup, hup']
  calc
    Erdos76.FiniteNibble.restrictedEventMass R p event =
        ∑ T ∈ R.powerset,
          @ite ℝ (event T) (Classical.propDecidable _)
            (Erdos697.Bernoulli.weight R p T) 0 :=
      restrictedEventMass_eq_sum_filter R p event
    _ ≤ (∑ T ∈ R.powerset.filter (fun T ↦ T.card < lower),
          Erdos697.Bernoulli.weight R p T) +
        (∑ T ∈ R.powerset.filter (fun T ↦ upper + 1 ≤ T.card),
          Erdos697.Bernoulli.weight R p T) := hsplit
    _ ≤ _ := add_le_add
      (Erdos697.Bernoulli.lower_tail_chernoff R p hp0 hp1 hEW
        hrLower0 hrLower1 hlower)
      (Erdos697.Bernoulli.upper_tail_chernoff R p hp0 hp1 hEW
        hrUpper hupper)

/-- Chernoff bound for one vertex event in the full edge-coordinate product.
The mean is exposed as a parameter so later scalar estimates can replace it
by the chosen logarithmic target. -/
theorem vertex_eventMass_le {G : SimpleGraph V} (s lower upper : ℕ)
    (v : V) (q EW rLower rUpper : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hEW : EW = (G.degree v : ℝ) * q)
    (hrLower0 : 0 < rLower) (hrLower1 : rLower < 1)
    (hrUpper : 1 < rUpper)
    (hlower : (lower : ℝ) ≤ rLower * EW)
    (hupper : rUpper * EW ≤ ((upper + 1 : ℕ) : ℝ)) :
    Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset (Edge G) ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S)
        (bad G s lower upper (Sum.inl v)) ≤
      Real.exp
          ((rLower * ((1 - rLower) / (2 * rLower)) +
              (1 / (1 + ((1 - rLower) / (2 * rLower))) - 1)) * EW) +
        Real.exp
          (((-(rUpper * ((rUpper - 1) / (2 * rUpper)))) +
              (1 / (1 - ((rUpper - 1) / (2 * rUpper))) - 1)) * EW) := by
  let R := incidenceSupport G v
  rw [Erdos76.FiniteNibble.eventMass_eq_restrictedEventMass
    (vertex_bad_eventDependsOn G s lower upper v)]
  change Erdos76.FiniteNibble.restrictedEventMass R (fun _ ↦ q)
      (bad G s lower upper (Sum.inl v)) ≤ _
  have hrestricted :
      Erdos76.FiniteNibble.restrictedEventMass R (fun _ ↦ q)
          (bad G s lower upper (Sum.inl v)) =
        Erdos76.FiniteNibble.restrictedEventMass R (fun _ ↦ q)
          (fun T ↦ T.card < lower ∨ upper < T.card) := by
    unfold Erdos76.FiniteNibble.restrictedEventMass
    apply Fintype.sum_congr
    intro T
    have hTR : T.1 ∩ R = T.1 := inter_eq_left.mpr T.2
    simp only [bad, sampledDegree, R, hTR]
  rw [hrestricted]
  apply restricted_card_outside_mass_le R (fun _ ↦ q)
      (fun _ _ ↦ hq0) (fun _ _ ↦ hq1)
      (EW := EW) (rLower := rLower) (rUpper := rUpper)
      ?_ hrLower0 hrLower1 hrUpper hlower hupper
  simp [hEW, R, card_incidenceSupport, mul_comm]

/-- Algebraic lower-tail coefficient estimate used with a relative error
`delta`. -/
theorem lower_chernoff_coefficient_le {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    let r := 1 - delta
    r * ((1 - r) / (2 * r)) +
        (1 / (1 + ((1 - r) / (2 * r))) - 1) ≤
      -(delta ^ 2) / 6 := by
  dsimp
  let r : ℝ := 1 - delta
  have hr0 : 0 < r := sub_pos.mpr hdelta1
  have hrne : r ≠ 0 := hr0.ne'
  have hrpne : r + 1 ≠ 0 := by dsimp [r]; linarith
  have hdenform :
      1 + (1 - r) / (2 * r) = (r + 1) / (2 * r) := by
    field_simp [hrne]
    ring
  have heq :
      r * ((1 - r) / (2 * r)) +
          (1 / (1 + ((1 - r) / (2 * r))) - 1) =
        -((1 - r) ^ 2) / (2 * (r + 1)) := by
    rw [hdenform]
    field_simp [hrne, hrpne]
    ring
  change r * ((1 - r) / (2 * r)) +
      (1 / (1 + ((1 - r) / (2 * r))) - 1) ≤ _
  rw [heq]
  have hden : 0 < 2 * (r + 1) := by nlinarith
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 6)]
  dsimp [r]
  nlinarith [sq_nonneg delta]

/-- Algebraic upper-tail coefficient estimate for the same relative error. -/
theorem upper_chernoff_coefficient_le {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    let r := 1 + delta
    (-(r * ((r - 1) / (2 * r)))) +
        (1 / (1 - ((r - 1) / (2 * r))) - 1) ≤
      -(delta ^ 2) / 6 := by
  dsimp
  let r : ℝ := 1 + delta
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hrne : r ≠ 0 := hr0.ne'
  have hrpne : r + 1 ≠ 0 := by dsimp [r]; linarith
  have hdenform :
      1 - (r - 1) / (2 * r) = (r + 1) / (2 * r) := by
    field_simp [hrne]
    ring
  have heq :
      (-(r * ((r - 1) / (2 * r)))) +
          (1 / (1 - ((r - 1) / (2 * r))) - 1) =
        -((r - 1) ^ 2) / (2 * (r + 1)) := by
    rw [hdenform]
    field_simp [hrne, hrpne]
    ring
  change (-(r * ((r - 1) / (2 * r)))) +
      (1 / (1 - ((r - 1) / (2 * r))) - 1) ≤ _
  rw [heq]
  have hden : 0 < 2 * (r + 1) := by nlinarith
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 6)]
  dsimp [r]
  nlinarith [sq_nonneg delta]

/-- A convenient two-sided multiplicative Chernoff corollary. -/
theorem vertex_eventMass_le_two_mul_exp
    {G : SimpleGraph V} (s lower upper : ℕ) (v : V)
    (q EW delta : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hEW0 : 0 ≤ EW)
    (hEW : EW = (G.degree v : ℝ) * q)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hlower : (lower : ℝ) ≤ (1 - delta) * EW)
    (hupper : (1 + delta) * EW ≤ ((upper + 1 : ℕ) : ℝ)) :
    Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset (Edge G) ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S)
        (bad G s lower upper (Sum.inl v)) ≤
      2 * Real.exp (-(delta ^ 2 * EW) / 6) := by
  have hraw := vertex_eventMass_le s lower upper v q EW
    (1 - delta) (1 + delta) hq0 hq1 hEW
    (sub_pos.mpr hdelta1) (by linarith) (by linarith)
    hlower hupper
  have hlo := lower_chernoff_coefficient_le hdelta0 hdelta1
  have hup := upper_chernoff_coefficient_le hdelta0 hdelta1
  calc
    Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset (Edge G) ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S)
        (bad G s lower upper (Sum.inl v)) ≤ _ := hraw
    _ ≤ Real.exp (-(delta ^ 2 * EW) / 6) +
        Real.exp (-(delta ^ 2 * EW) / 6) := by
      apply add_le_add <;> apply Real.exp_le_exp.mpr
      · calc
          ((1 - delta) * ((1 - (1 - delta)) / (2 * (1 - delta))) +
              (1 / (1 + ((1 - (1 - delta)) / (2 * (1 - delta)))) - 1)) * EW ≤
              (-(delta ^ 2) / 6) * EW :=
            mul_le_mul_of_nonneg_right hlo hEW0
          _ = -(delta ^ 2 * EW) / 6 := by ring
      · calc
          ((-((1 + delta) * (((1 + delta) - 1) / (2 * (1 + delta))))) +
              (1 / (1 - (((1 + delta) - 1) / (2 * (1 + delta)))) - 1)) * EW ≤
              (-(delta ^ 2) / 6) * EW :=
            mul_le_mul_of_nonneg_right hup hEW0
          _ = -(delta ^ 2 * EW) / 6 := by ring
    _ = 2 * Real.exp (-(delta ^ 2 * EW) / 6) := by ring

/-! ## Specialized asymmetric-local-lemma assembly -/

/-- Vertex indices in the dependency neighborhood of an event. -/
def dependencyVertices (G : SimpleGraph V) (s : ℕ) (i : Event G s) : Finset V :=
  Finset.univ.filter fun v ↦ Sum.inl v ∈ dependency G s i

/-- Cycle indices in the dependency neighborhood of an event. -/
def dependencyCycles (G : SimpleGraph V) (s : ℕ) (i : Event G s) :
    Finset (ShortCycleSupport G s) :=
  Finset.univ.filter fun C ↦ Sum.inr C ∈ dependency G s i

theorem mem_dependency_iff (G : SimpleGraph V) (s : ℕ)
    (i j : Event G s) :
    j ∈ dependency G s i ↔
      j ≠ i ∧ ¬ Disjoint (support G s i) (support G s j) := by
  simp [dependency]

/-- Splitting a dependency sum along the two summands of the event type. -/
theorem sum_dependency_eq_parts (G : SimpleGraph V) (s : ℕ)
    (i : Event G s) (f : Event G s → ℝ) :
    (∑ j ∈ dependency G s i, f j) =
      (∑ v ∈ dependencyVertices G s i, f (Sum.inl v)) +
      ∑ C ∈ dependencyCycles G s i, f (Sum.inr C) := by
  calc
    (∑ j ∈ dependency G s i, f j) =
        ∑ j, if j ∈ dependency G s i then f j else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = (∑ v, if Sum.inl v ∈ dependency G s i then f (Sum.inl v) else 0) +
          ∑ C, if Sum.inr C ∈ dependency G s i then f (Sum.inr C) else 0 := by
      rw [Fintype.sum_sum_type]
    _ = _ := by simp [dependencyVertices, dependencyCycles, sum_filter]

/-- The elementary product estimate used below.  It is the finite union
bound in multiplicative form. -/
theorem one_sub_sum_le_prod_one_sub {I : Type*} [DecidableEq I]
    (T : Finset I) (x : I → ℝ)
    (hx0 : ∀ i ∈ T, 0 ≤ x i) (hx1 : ∀ i ∈ T, x i ≤ 1) :
    1 - ∑ i ∈ T, x i ≤ ∏ i ∈ T, (1 - x i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      rw [sum_insert ha, prod_insert ha]
      have hxa0 := hx0 a (mem_insert_self a T)
      have hxa1 := hx1 a (mem_insert_self a T)
      have hsum0 : 0 ≤ ∑ i ∈ T, x i :=
        sum_nonneg fun i hi ↦ hx0 i (mem_insert_of_mem hi)
      have hone : 0 ≤ 1 - x a := sub_nonneg.mpr hxa1
      calc
        1 - (x a + ∑ i ∈ T, x i) ≤
            (1 - x a) * (1 - ∑ i ∈ T, x i) := by nlinarith
        _ ≤ (1 - x a) * ∏ i ∈ T, (1 - x i) :=
          mul_le_mul_of_nonneg_left
            (ih (fun i hi ↦ hx0 i (mem_insert_of_mem hi))
              (fun i hi ↦ hx1 i (mem_insert_of_mem hi))) hone

/-- Distinct vertex events dependent with the event at `v` are indexed by
neighbors of `v`. -/
theorem card_dependencyVertices_vertex_le (G : SimpleGraph V) (s D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (v : V) :
    (dependencyVertices G s (Sum.inl v)).card ≤ D := by
  calc
    (dependencyVertices G s (Sum.inl v)).card ≤
        (G.neighborFinset v).card := by
      apply card_le_card
      intro w hw
      simp only [dependencyVertices, mem_filter, mem_univ, true_and] at hw
      have hw' := (mem_dependency_iff G s (Sum.inl v) (Sum.inl w)).mp hw
      have hne : w ≠ v := by
        intro h
        apply hw'.1
        simp [h]
      rw [SimpleGraph.mem_neighborFinset]
      rw [Finset.not_disjoint_iff] at hw'
      obtain ⟨e, hev, hew⟩ := hw'.2
      apply G.adj_of_mem_incidenceSet hne.symm
      · exact ⟨SimpleGraph.mem_edgeFinset.mp e.2,
          (Sym2.mem_toFinset.mp (mem_incidenceSupport.mp hev))⟩
      · exact ⟨SimpleGraph.mem_edgeFinset.mp e.2,
          (Sym2.mem_toFinset.mp (mem_incidenceSupport.mp hew))⟩
    _ = G.degree v := G.card_neighborFinset_eq_degree v
    _ ≤ D := hdegree v

/-- A cycle support meets vertex supports only at endpoints of its edges. -/
theorem card_dependencyVertices_cycle_le (G : SimpleGraph V) (s : ℕ)
    (C : ShortCycleSupport G s) :
    (dependencyVertices G s (Sum.inr C)).card ≤ 2 * C.1.card := by
  let endpoints : Finset V := C.1.biUnion fun e ↦ e.1.toFinset
  calc
    (dependencyVertices G s (Sum.inr C)).card ≤ endpoints.card := by
      apply card_le_card
      intro v hv
      simp only [dependencyVertices, mem_filter, mem_univ, true_and] at hv
      have hv' := (mem_dependency_iff G s (Sum.inr C) (Sum.inl v)).mp hv
      simp only [endpoints, mem_biUnion]
      rw [Finset.not_disjoint_iff] at hv'
      obtain ⟨e, heC, hev⟩ := hv'.2
      exact ⟨e, heC, mem_incidenceSupport.mp hev⟩
    _ ≤ C.1.card * 2 := by
      apply Finset.card_biUnion_le_card_mul
      intro e he
      exact (SimpleGraph.card_toFinset_mem_edgeFinset e).le
    _ = 2 * C.1.card := by omega

/-- Partitioning a finite sum by a bounded natural-valued size. -/
theorem sum_eq_sum_size_fibers {I : Type*} [DecidableEq I]
    (T : Finset I) (size : I → ℕ) (s : ℕ) (f : I → ℝ)
    (hsize : ∀ i ∈ T, size i ≤ s) :
    (∑ i ∈ T, f i) =
      ∑ k ∈ Finset.range (s + 1), ∑ i ∈ T.filter (fun i ↦ size i = k), f i := by
  calc
    (∑ i ∈ T, f i) =
        ∑ i ∈ T, ∑ k ∈ Finset.range (s + 1),
          if size i = k then f i else 0 := by
      apply sum_congr rfl
      intro i hi
      simp [Nat.lt_succ_iff.mpr (hsize i hi)]
    _ = ∑ k ∈ Finset.range (s + 1), ∑ i ∈ T,
          if size i = k then f i else 0 := by
      rw [sum_comm]
    _ = _ := by simp only [sum_filter]

/-- Exact-length cycle indices adjacent to a vertex event satisfy the rooted
walk count. -/
theorem card_dependencyCycles_vertex_length_le (G : SimpleGraph V) (s D n : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (v : V) :
    ((dependencyCycles G s (Sum.inl v)).filter
      (fun C ↦ C.1.card = n + 1)).card ≤ D ^ n := by
  refine (card_le_card ?_).trans
    (card_filter_cycle_overlap_vertex_le_pow G D hdegree s n v)
  intro C hC
  simp only [mem_filter] at hC ⊢
  have hdep := (mem_dependency_iff G s (Sum.inl v) (Sum.inr C)).mp
    ((mem_filter.mp hC.1).2)
  exact ⟨mem_univ C, hC.2, hdep.2⟩

/-- Exact-length cycle indices adjacent to a cycle event satisfy the
edge-rooted walk count. -/
theorem card_dependencyCycles_cycle_length_le (G : SimpleGraph V) (s D n : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) (C : ShortCycleSupport G s) :
    ((dependencyCycles G s (Sum.inr C)).filter
      (fun K ↦ K.1.card = n + 2)).card ≤ C.1.card * D ^ n := by
  refine (card_le_card ?_).trans
    (card_filter_cycle_overlap_cycle_le G D hdegree s n C.1)
  intro K hK
  simp only [mem_filter] at hK ⊢
  have hdep := (mem_dependency_iff G s (Sum.inr C) (Sum.inr K)).mp
    ((mem_filter.mp hK.1).2)
  exact ⟨mem_univ K, hK.2, hdep.2⟩

/-- Event-wise marginal majorants: one common vertex bound and the exact
cycle-survival probability. -/
def eventBound (G : SimpleGraph V) (s : ℕ) (q vertexBound : ℝ) :
    Event G s → ℝ
  | Sum.inl _ => vertexBound
  | Sum.inr C => q ^ C.1.card

/-- Alon's asymmetric local-lemma weights. -/
def eventWeight (G : SimpleGraph V) (s D : ℕ) : Event G s → ℝ
  | Sum.inl _ => (4 * (D : ℝ))⁻¹
  | Sum.inr C =>
      (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ (C.1.card - 1))⁻¹

/-- The total cycle-event weight adjacent to a vertex event is at most one
half.  The factor `s+1` in the weights pays for the possible cycle lengths. -/
theorem sum_dependencyCycles_vertex_weight_le_half
    (G : SimpleGraph V) (s D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ v, G.degree v ≤ D) (v : V) :
    (∑ C ∈ dependencyCycles G s (Sum.inl v),
      eventWeight G s D (Sum.inr C)) ≤ (1 : ℝ) / 2 := by
  let T := dependencyCycles G s (Sum.inl v)
  rw [sum_eq_sum_size_fibers T (fun C ↦ C.1.card) s
    (fun C ↦ eventWeight G s D (Sum.inr C))
    (fun C _ ↦ (shortCycleSupport_card_bounds C).2)]
  calc
    (∑ k ∈ range (s + 1),
        ∑ C ∈ T.filter (fun C ↦ C.1.card = k),
          eventWeight G s D (Sum.inr C)) ≤
        ∑ _k ∈ range (s + 1),
          (2 * ((s + 1 : ℕ) : ℝ))⁻¹ := by
      apply sum_le_sum
      intro k hk
      by_cases hk3 : 3 ≤ k
      · let n := k - 1
        have hnk : n + 1 = k := by omega
        let F := T.filter fun C ↦ C.1.card = k
        have hcard : F.card ≤ D ^ n := by
          simpa [F, T, hnk] using
            card_dependencyCycles_vertex_length_le G s D n hdegree v
        have hsum :
            (∑ C ∈ F, eventWeight G s D (Sum.inr C)) =
              (F.card : ℝ) *
                (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ n)⁻¹ := by
          calc
            (∑ C ∈ F, eventWeight G s D (Sum.inr C)) =
                ∑ _C ∈ F,
                  (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ n)⁻¹ := by
              apply sum_congr rfl
              intro C hCF
              have hCcard : C.1.card = k := (mem_filter.mp hCF).2
              have hexp : C.1.card - 1 = n := by
                rw [hCcard, ← hnk]
                omega
              simp only [eventWeight]
              rw [hexp]
            _ = _ := by simp [nsmul_eq_mul]
        rw [show T.filter (fun C ↦ C.1.card = k) = F by rfl, hsum]
        have hcardR : (F.card : ℝ) ≤ (D : ℝ) ^ n := by
          exact_mod_cast hcard
        have hinv0 : 0 ≤
            (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ n)⁻¹ := by
          positivity
        calc
          (F.card : ℝ) *
                (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ n)⁻¹ ≤
              (D : ℝ) ^ n *
                (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ n)⁻¹ :=
            mul_le_mul_of_nonneg_right hcardR hinv0
          _ = (2 * ((s + 1 : ℕ) : ℝ))⁻¹ := by
            field_simp
      · have hF : T.filter (fun C ↦ C.1.card = k) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro C hCT hCcard
          have hlen := (shortCycleSupport_card_bounds C).1
          omega
        rw [hF]
        simp only [sum_empty]
        exact inv_nonneg.mpr (by positivity)
    _ = (1 : ℝ) / 2 := by
      rw [sum_const, card_range]
      simp [nsmul_eq_mul]
      field_simp

/-- The total cycle-event weight adjacent to a length-`k` cycle event is at
most `k/(2D)`. -/
theorem sum_dependencyCycles_cycle_weight_le
    (G : SimpleGraph V) (s D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ v, G.degree v ≤ D) (C : ShortCycleSupport G s) :
    (∑ K ∈ dependencyCycles G s (Sum.inr C),
      eventWeight G s D (Sum.inr K)) ≤
        (C.1.card : ℝ) / (2 * D) := by
  let T := dependencyCycles G s (Sum.inr C)
  rw [sum_eq_sum_size_fibers T (fun K ↦ K.1.card) s
    (fun K ↦ eventWeight G s D (Sum.inr K))
    (fun K _ ↦ (shortCycleSupport_card_bounds K).2)]
  calc
    (∑ k ∈ range (s + 1),
        ∑ K ∈ T.filter (fun K ↦ K.1.card = k),
          eventWeight G s D (Sum.inr K)) ≤
        ∑ _k ∈ range (s + 1),
          (C.1.card : ℝ) /
            (2 * ((s + 1 : ℕ) : ℝ) * D) := by
      apply sum_le_sum
      intro k hk
      by_cases hk3 : 3 ≤ k
      · let n := k - 2
        have hnk : n + 2 = k := by omega
        let F := T.filter fun K ↦ K.1.card = k
        have hcard : F.card ≤ C.1.card * D ^ n := by
          simpa [F, T, hnk] using
            card_dependencyCycles_cycle_length_le G s D n hdegree C
        have hsum :
            (∑ K ∈ F, eventWeight G s D (Sum.inr K)) =
              (F.card : ℝ) *
                (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ (n + 1))⁻¹ := by
          calc
            (∑ K ∈ F, eventWeight G s D (Sum.inr K)) =
                ∑ _K ∈ F,
                  (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ (n + 1))⁻¹ := by
              apply sum_congr rfl
              intro K hKF
              have hKcard : K.1.card = k := (mem_filter.mp hKF).2
              have hexp : K.1.card - 1 = n + 1 := by
                rw [hKcard, ← hnk]
                omega
              simp only [eventWeight]
              rw [hexp]
            _ = _ := by simp [nsmul_eq_mul]
        rw [show T.filter (fun K ↦ K.1.card = k) = F by rfl, hsum]
        have hcardR : (F.card : ℝ) ≤
            (C.1.card : ℝ) * (D : ℝ) ^ n := by
          exact_mod_cast hcard
        have hinv0 : 0 ≤
            (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ (n + 1))⁻¹ := by
          positivity
        calc
          (F.card : ℝ) *
                (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ (n + 1))⁻¹ ≤
              ((C.1.card : ℝ) * (D : ℝ) ^ n) *
                (2 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ (n + 1))⁻¹ :=
            mul_le_mul_of_nonneg_right hcardR hinv0
          _ = (C.1.card : ℝ) /
              (2 * ((s + 1 : ℕ) : ℝ) * D) := by
            rw [pow_succ]
            field_simp
      · have hF : T.filter (fun K ↦ K.1.card = k) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro K hKT hKcard
          have hlen := (shortCycleSupport_card_bounds K).1
          omega
        rw [hF]
        simp only [sum_empty]
        positivity
    _ = (C.1.card : ℝ) / (2 * D) := by
      rw [sum_const, card_range]
      simp [nsmul_eq_mul]
      field_simp

theorem eventWeight_nonneg (G : SimpleGraph V) (s D : ℕ) :
    ∀ i : Event G s, 0 ≤ eventWeight G s D i := by
  rintro (v | C)
  · exact inv_nonneg.mpr (mul_nonneg (by norm_num) (Nat.cast_nonneg D))
  · exact inv_nonneg.mpr <| mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg (s + 1)))
      (pow_nonneg (Nat.cast_nonneg D) _)

theorem eventWeight_lt_one (G : SimpleGraph V) (s D : ℕ) (hD : 2 ≤ D) :
    ∀ i : Event G s, eventWeight G s D i < 1 := by
  rintro (v | C)
  · simp only [eventWeight]
    apply (inv_lt_one₀ (mul_pos (by norm_num) (by positivity))).2
    have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith
  · simp only [eventWeight]
    apply (inv_lt_one₀ (mul_pos
      (mul_pos (by norm_num) (by positivity)) (pow_pos (by positivity) _))).2
    have hsR : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le s))
    have hpR : (1 : ℝ) ≤ (D : ℝ) ^ (C.1.card - 1) := by
      apply one_le_pow₀
      exact_mod_cast (show 1 ≤ D by omega)
    nlinarith

theorem sum_dependencyVertices_vertex_weight_le_quarter
    (G : SimpleGraph V) (s D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ v, G.degree v ≤ D) (v : V) :
    (∑ w ∈ dependencyVertices G s (Sum.inl v),
      eventWeight G s D (Sum.inl w)) ≤ (1 : ℝ) / 4 := by
  simp only [eventWeight]
  rw [sum_const, nsmul_eq_mul]
  have hcardR : ((dependencyVertices G s (Sum.inl v)).card : ℝ) ≤ D := by
    exact_mod_cast card_dependencyVertices_vertex_le G s D hdegree v
  have hinv0 : 0 ≤ (4 * (D : ℝ))⁻¹ := by positivity
  calc
    ((dependencyVertices G s (Sum.inl v)).card : ℝ) *
        (4 * (D : ℝ))⁻¹ ≤
      (D : ℝ) * (4 * (D : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hcardR hinv0
    _ = (1 : ℝ) / 4 := by field_simp

theorem sum_dependencyVertices_cycle_weight_le
    (G : SimpleGraph V) (s D : ℕ) (hD : 2 ≤ D)
    (C : ShortCycleSupport G s) :
    (∑ v ∈ dependencyVertices G s (Sum.inr C),
      eventWeight G s D (Sum.inl v)) ≤
        (C.1.card : ℝ) / (2 * D) := by
  simp only [eventWeight]
  rw [sum_const, nsmul_eq_mul]
  have hcardR : ((dependencyVertices G s (Sum.inr C)).card : ℝ) ≤
      2 * C.1.card := by
    exact_mod_cast card_dependencyVertices_cycle_le G s C
  have hinv0 : 0 ≤ (4 * (D : ℝ))⁻¹ := by positivity
  calc
    ((dependencyVertices G s (Sum.inr C)).card : ℝ) *
        (4 * (D : ℝ))⁻¹ ≤
      (2 * (C.1.card : ℝ)) * (4 * (D : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right hcardR hinv0
    _ = (C.1.card : ℝ) / (2 * D) := by
      field_simp
      ring

/-- Numerical consequence of the local counts: every vertex-event
dependency product is at least `1/4`. -/
theorem quarter_le_vertex_dependency_product
    (G : SimpleGraph V) (s D : ℕ) (hD : 2 ≤ D)
    (hdegree : ∀ v, G.degree v ≤ D) (v : V) :
    (1 : ℝ) / 4 ≤
      ∏ j ∈ dependency G s (Sum.inl v),
        (1 - eventWeight G s D j) := by
  have hsum : (∑ j ∈ dependency G s (Sum.inl v),
      eventWeight G s D j) ≤ (3 : ℝ) / 4 := by
    rw [sum_dependency_eq_parts]
    linarith [sum_dependencyVertices_vertex_weight_le_quarter G s D hD hdegree v,
      sum_dependencyCycles_vertex_weight_le_half G s D hD hdegree v]
  calc
    (1 : ℝ) / 4 ≤
        1 - ∑ j ∈ dependency G s (Sum.inl v), eventWeight G s D j := by
      linarith
    _ ≤ _ := one_sub_sum_le_prod_one_sub _ _
      (fun j hj ↦ eventWeight_nonneg G s D j)
      (fun j hj ↦ (eventWeight_lt_one G s D hD j).le)

/-- Numerical consequence for a cycle event, assuming the girth cutoff is
small compared with `D`. -/
theorem half_le_cycle_dependency_product
    (G : SimpleGraph V) (s D : ℕ) (hD : 2 ≤ D) (hsD : 2 * s ≤ D)
    (hdegree : ∀ v, G.degree v ≤ D) (C : ShortCycleSupport G s) :
    (1 : ℝ) / 2 ≤
      ∏ j ∈ dependency G s (Sum.inr C),
        (1 - eventWeight G s D j) := by
  have hCD : 2 * C.1.card ≤ D :=
    (Nat.mul_le_mul_left 2 (shortCycleSupport_card_bounds C).2).trans hsD
  have hratio : (C.1.card : ℝ) / D ≤ (1 : ℝ) / 2 := by
    have hDR : (0 : ℝ) < D := by positivity
    have hCDR : (2 : ℝ) * C.1.card ≤ D := by exact_mod_cast hCD
    apply (div_le_iff₀ hDR).2
    nlinarith
  have hsum : (∑ j ∈ dependency G s (Sum.inr C),
      eventWeight G s D j) ≤ (1 : ℝ) / 2 := by
    rw [sum_dependency_eq_parts]
    have hv := sum_dependencyVertices_cycle_weight_le G s D hD C
    have hc := sum_dependencyCycles_cycle_weight_le G s D hD hdegree C
    calc
      (∑ v ∈ dependencyVertices G s (Sum.inr C),
          eventWeight G s D (Sum.inl v)) +
          ∑ K ∈ dependencyCycles G s (Sum.inr C),
            eventWeight G s D (Sum.inr K) ≤
          (C.1.card : ℝ) / (2 * D) +
            (C.1.card : ℝ) / (2 * D) := add_le_add hv hc
      _ = (C.1.card : ℝ) / D := by ring
      _ ≤ (1 : ℝ) / 2 := hratio
  calc
    (1 : ℝ) / 2 ≤
        1 - ∑ j ∈ dependency G s (Sum.inr C), eventWeight G s D j := by
      linarith
    _ ≤ _ := one_sub_sum_le_prod_one_sub _ _
      (fun j hj ↦ eventWeight_nonneg G s D j)
      (fun j hj ↦ (eventWeight_lt_one G s D hD j).le)

/-- Fully specialized finite asymmetric LLL.  All probability and locality
work is discharged here; callers need only verify the displayed numerical
parameter inequalities. -/
theorem exists_avoiding_of_lll_parameters
    (G : SimpleGraph V) (s lower upper D : ℕ)
    (q vertexBound : ℝ) (hD : 2 ≤ D)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hvertexBound0 : 0 ≤ vertexBound)
    (hparameter : ∀ i : Event G s,
      eventBound G s q vertexBound i ≤
        eventWeight G s D i *
          ∏ j ∈ dependency G s i, (1 - eventWeight G s D j))
    (hvertexMarginal : ∀ v : V,
      Erdos76.FiniteLocalLemma.eventMass
          (fun S : Finset (Edge G) ↦
            Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S)
          (bad G s lower upper (Sum.inl v)) ≤ vertexBound) :
    ∃ S : Finset (Edge G), ∀ i : Event G s,
      ¬ bad G s lower upper i S := by
  let mass : Finset (Edge G) → ℝ := fun S ↦
    Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S
  have hmass0 : ∀ S, 0 ≤ mass S := by
    intro S
    exact Erdos76.FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun _ _ ↦ hq0) (fun _ _ ↦ hq1)
  have hmassTotal : ∑ S, mass S = 1 := by
    change (∑ S : Finset (Edge G),
      Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S) = 1
    have hU :
        (Finset.univ : Finset (Finset (Edge G))) =
          (Finset.univ : Finset (Edge G)).powerset := by
      ext S
      simp only [Finset.mem_univ, Finset.mem_powerset, true_iff]
      exact Finset.subset_univ S
    calc
      (∑ S : Finset (Edge G),
        Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S) =
          ∑ S ∈ (Finset.univ : Finset (Edge G)).powerset,
            Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S := by
        rw [← hU]
      _ = 1 := Erdos76.FiniteNibble.sum_bernoulliMass
        (Finset.univ : Finset (Edge G)) (fun _ ↦ q)
  have hindep : Erdos76.FiniteLocalLemma.IndependentOutside mass
      (bad G s lower upper) (dependency G s) := by
    exact Erdos76.FiniteNibble.independentOutside_of_eventDependsOn
      (fun _ ↦ q) (support G s) (bad G s lower upper) (dependency G s)
      (bad_eventDependsOn G s lower upper)
      (dependency_containsSupportOverlaps G s)
  have hmarginal : ∀ i : Event G s,
      Erdos76.FiniteLocalLemma.eventMass mass (bad G s lower upper i) ≤
        eventBound G s q vertexBound i := by
    rintro (v | C)
    · exact hvertexMarginal v
    · change Erdos76.FiniteLocalLemma.eventMass mass
          (bad G s lower upper (Sum.inr C)) ≤ q ^ C.1.card
      exact (indexed_cycle_eventMass_eq_pow q hq0 hq1 C).le
  exact Erdos622.LinearArboricity.AsymmetricLocalLemma.exists_avoiding_all
    mass hmass0 hmassTotal (bad G s lower upper) (dependency G s)
    (eventBound G s q vertexBound) (eventWeight G s D)
    (eventWeight_nonneg G s D) (eventWeight_lt_one G s D hD) hparameter
    (Erdos622.LinearArboricity.AsymmetricLocalLemma.hasIndexedLocalBound_of_independentOutside
      mass hmass0
        (bad G s lower upper) (dependency G s)
        (eventBound G s q vertexBound) hindep hmarginal)

/-- Concrete numerical interface to the specialized LLL. -/
theorem exists_avoiding_of_scalar_bounds
    (G : SimpleGraph V) (s lower upper D : ℕ) (q vertexBound : ℝ)
    (hD : 2 ≤ D) (hsD : 2 * s ≤ D)
    (hdegree : ∀ v, G.degree v ≤ D)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hvertexBound0 : 0 ≤ vertexBound)
    (hvertexScalar : vertexBound ≤ (16 * (D : ℝ))⁻¹)
    (hcycleScalar : ∀ k, 3 ≤ k → k ≤ s →
      q ^ k ≤
        (4 * ((s + 1 : ℕ) : ℝ) * (D : ℝ) ^ (k - 1))⁻¹)
    (hvertexMarginal : ∀ v : V,
      Erdos76.FiniteLocalLemma.eventMass
          (fun S : Finset (Edge G) ↦
            Erdos76.FiniteNibble.bernoulliMass Finset.univ (fun _ ↦ q) S)
          (bad G s lower upper (Sum.inl v)) ≤ vertexBound) :
    ∃ S : Finset (Edge G), ∀ i : Event G s,
      ¬ bad G s lower upper i S := by
  apply exists_avoiding_of_lll_parameters G s lower upper D q vertexBound
    hD hq0 hq1 hvertexBound0
  · rintro (v | C)
    · simp only [eventBound, eventWeight]
      have hp := quarter_le_vertex_dependency_product G s D hD hdegree v
      calc
        vertexBound ≤ (16 * (D : ℝ))⁻¹ := hvertexScalar
        _ = (4 * (D : ℝ))⁻¹ * ((1 : ℝ) / 4) := by
          field_simp
          norm_num
        _ ≤ (4 * (D : ℝ))⁻¹ *
            ∏ j ∈ dependency G s (Sum.inl v),
              (1 - eventWeight G s D j) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
    · simp only [eventBound, eventWeight]
      have hp := half_le_cycle_dependency_product G s D hD hsD hdegree C
      have hC := hcycleScalar C.1.card
        (shortCycleSupport_card_bounds C).1
        (shortCycleSupport_card_bounds C).2
      calc
        q ^ C.1.card ≤
            (4 * ((s + 1 : ℕ) : ℝ) *
              (D : ℝ) ^ (C.1.card - 1))⁻¹ := hC
        _ = (2 * ((s + 1 : ℕ) : ℝ) *
              (D : ℝ) ^ (C.1.card - 1))⁻¹ * ((1 : ℝ) / 2) := by
          field_simp
          norm_num
        _ ≤ (2 * ((s + 1 : ℕ) : ℝ) *
              (D : ℝ) ^ (C.1.card - 1))⁻¹ *
            ∏ j ∈ dependency G s (Sum.inr C),
              (1 - eventWeight G s D j) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
  · exact hvertexMarginal

/-! ## Returning from edge coordinates to a spanning graph -/

/-- The graph consisting exactly of the sampled host edges. -/
def sampledGraph (G : SimpleGraph V) (S : Finset (Edge G)) : SimpleGraph V where
  Adj v w := ∃ e : Edge G, e ∈ S ∧ e.1 = s(v, w)
  symm := ⟨by
    intro v w
    rintro ⟨e, he, hval⟩
    exact ⟨e, he, hval.trans Sym2.eq_swap⟩
    ⟩
  loopless := ⟨by
    intro v
    rintro ⟨e, _he, hval⟩
    have heSet : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
    have hadj : G.Adj v v := by
      rw [← SimpleGraph.mem_edgeSet]
      simpa [hval] using heSet
    exact G.loopless.irrefl v hadj
    ⟩

@[simp] theorem sampledGraph_adj {G : SimpleGraph V} {S : Finset (Edge G)}
    {v w : V} :
    (sampledGraph G S).Adj v w ↔
      ∃ e : Edge G, e ∈ S ∧ e.1 = s(v, w) :=
  Iff.rfl

/-- The finite edge set of the sampled graph is the image of the sampled
coordinate set. -/
theorem edgeFinset_sampledGraph (G : SimpleGraph V) (S : Finset (Edge G)) :
    (sampledGraph G S).edgeFinset = S.map (edgeValEmbedding G) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ v w =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        sampledGraph_adj, Finset.mem_map]
      constructor
      · rintro ⟨f, hf, hval⟩
        exact ⟨f, hf, hval⟩
      · rintro ⟨f, hf, hval⟩
        exact ⟨f, hf, hval⟩

/-- A sampled graph is a spanning subgraph of its host. -/
theorem sampledGraph_le (G : SimpleGraph V) (S : Finset (Edge G)) :
    sampledGraph G S ≤ G := by
  intro v w
  rintro ⟨e, _he, hval⟩
  have heSet : e.1 ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp e.2
  rw [← SimpleGraph.mem_edgeSet]
  simpa [hval] using heSet

/-- Incidence coordinates selected at `v` map exactly to the sampled graph's
ordinary incidence finset. -/
theorem map_sampled_incidence (G : SimpleGraph V) (S : Finset (Edge G))
    (v : V) :
    (S ∩ incidenceSupport G v).map (edgeValEmbedding G) =
      (sampledGraph G S).incidenceFinset v := by
  rw [SimpleGraph.incidenceFinset_eq_filter, edgeFinset_sampledGraph]
  ext e
  simp [incidenceSupport, edgeValEmbedding]

/-- The graph degree is exactly the sampled incidence-coordinate count. -/
theorem degree_sampledGraph (G : SimpleGraph V) (S : Finset (Edge G))
    (v : V) :
    (sampledGraph G S).degree v = sampledDegree G v S := by
  rw [sampledDegree, ← SimpleGraph.card_incidenceFinset_eq_degree,
    ← map_sampled_incidence G S v, card_map]

/-- Avoiding every indexed short-cycle event forces extended girth at least
`s + 1`.  This formulation also covers an acyclic sampled graph, whose
extended girth is infinite. -/
theorem succ_le_egirth_sampledGraph_of_avoid
    (G : SimpleGraph V) (S : Finset (Edge G)) (s : ℕ)
    (havoid : ∀ C : ShortCycleSupport G s, ¬ C.1 ⊆ S) :
    ((s + 1 : ℕ) : ℕ∞) ≤ (sampledGraph G S).egirth := by
  rw [SimpleGraph.le_egirth]
  intro v p hp
  let hle : sampledGraph G S ≤ G := sampledGraph_le G S
  let q : G.Walk v v := p.mapLe hle
  let Cset : Finset (Edge G) :=
    Finset.univ.filter fun e ↦ e.1 ∈ q.edges
  have hqCycle : q.IsCycle := hp.mapLe hle
  have hqLength : q.length = p.length := p.length_mapLe hle
  by_cases hlen : p.length ≤ s
  · have hCprop' : IsShortCycleSupport G s Cset := by
      refine ⟨v, q, hqCycle, ?_, ?_⟩
      · simpa [hqLength] using hlen
      · intro e
        simp [Cset]
    let C : ShortCycleSupport G s := ⟨Cset, hCprop'⟩
    apply False.elim
    apply havoid C
    intro e heC
    have heq : e.1 ∈ q.edges := by
      simpa [C, Cset] using heC
    have hep : e.1 ∈ p.edges := by
      simpa [q, hle, SimpleGraph.Walk.edges_mapLe_eq_edges] using heq
    have heHset : e.1 ∈ (sampledGraph G S).edgeSet :=
      p.edges_subset_edgeSet hep
    have heHfin : e.1 ∈ (sampledGraph G S).edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr heHset
    rw [edgeFinset_sampledGraph] at heHfin
    obtain ⟨f, hfS, hfe⟩ := Finset.mem_map.mp heHfin
    have hsub : f = e := Subtype.ext hfe
    simpa [hsub] using hfS
  · have hlt : s < p.length := Nat.lt_of_not_ge hlen
    exact_mod_cast (Nat.succ_le_iff.mpr hlt)

/-- Deterministic endpoint of the finite product experiment: any outcome
avoiding all declared bad events is the edge set of a spanning high-girth
subgraph with every degree in the prescribed integral window. -/
theorem sampledGraph_spec_of_avoids
    (G : SimpleGraph V) (S : Finset (Edge G)) (s lower upper : ℕ)
    (havoid : ∀ i : Event G s, ¬ bad G s lower upper i S) :
    sampledGraph G S ≤ G ∧
      ((s + 1 : ℕ) : ℕ∞) ≤ (sampledGraph G S).egirth ∧
      ∀ v, lower ≤ (sampledGraph G S).degree v ∧
        (sampledGraph G S).degree v ≤ upper := by
  refine ⟨sampledGraph_le G S, ?_, ?_⟩
  · apply succ_le_egirth_sampledGraph_of_avoid G S s
    intro C hCS
    exact (havoid (Sum.inr C)) hCS
  · intro v
    have hv := havoid (Sum.inl v)
    rw [bad, not_or] at hv
    rw [degree_sampledGraph]
    exact ⟨Nat.le_of_not_gt hv.1, Nat.le_of_not_gt hv.2⟩

/-! ## Alon's logarithmic parameter choice -/

def alonLogDegree (D : ℕ) : ℝ := Real.log (D : ℝ)

def alonMeanDegree (D : ℕ) : ℝ := alonLogDegree D ^ 10

def alonDegreeError (D : ℕ) : ℝ := alonLogDegree D ^ 6

def alonLowerDegree (D : ℕ) : ℕ :=
  ⌊alonMeanDegree D - alonDegreeError D⌋₊

def alonUpperDegree (D : ℕ) : ℕ :=
  ⌈alonMeanDegree D + alonDegreeError D⌉₊

def alonGirthCutoff (D : ℕ) : ℕ :=
  ⌊alonLogDegree D / (20 * Real.log (alonLogDegree D))⌋₊

def alonSamplingProbability (D : ℕ) : ℝ :=
  alonMeanDegree D / D

def alonRelativeDeviation (D : ℕ) : ℝ :=
  (alonLogDegree D ^ 4)⁻¹

def alonVertexBound (D : ℕ) : ℝ :=
  2 * Real.exp (-(alonLogDegree D ^ 2) / 6)

/-- The logarithmic cutoff makes the largest cycle-survival probability
small enough for the asymmetric LLL. -/
theorem alon_cycle_scalar
    (D k : ℕ) (hD : 0 < D)
    (hlog : 1 < alonLogDegree D)
    (hloglog : 0 < Real.log (alonLogDegree D))
    (hcutoff : 4 * ((alonGirthCutoff D + 1 : ℕ) : ℝ) ≤ Real.sqrt D)
    (hk3 : 3 ≤ k) (hks : k ≤ alonGirthCutoff D) :
    alonSamplingProbability D ^ k ≤
      (4 * ((alonGirthCutoff D + 1 : ℕ) : ℝ) *
        (D : ℝ) ^ (k - 1))⁻¹ := by
  let L := alonLogDegree D
  let s := alonGirthCutoff D
  let t := alonMeanDegree D
  have hLpos : 0 < L := lt_trans zero_lt_one hlog
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hsReal : (s : ℝ) ≤ L / (20 * Real.log L) := by
    exact Nat.floor_le (div_nonneg hLpos.le (by positivity))
  have htwenty : (20 : ℝ) * (k : ℝ) * Real.log L ≤ L := by
    have hksR : (k : ℝ) ≤ s := by exact_mod_cast hks
    have hmul := mul_le_mul_of_nonneg_right hksR hloglog.le
    have hmul' := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 20)
    have hdenpos : 0 < 20 * Real.log L := mul_pos (by norm_num) hloglog
    have hsMul : (s : ℝ) * (20 * Real.log L) ≤ L :=
      (le_div_iff₀ hdenpos).mp hsReal
    nlinarith
  have hpow20 : L ^ (20 * k) ≤ (D : ℝ) := by
    calc
      L ^ (20 * k) = Real.exp (Real.log (L ^ (20 * k))) := by
        rw [Real.exp_log (pow_pos hLpos _)]
      _ = Real.exp (((20 * k : ℕ) : ℝ) * Real.log L) := by
        rw [Real.log_pow]
      _ ≤ Real.exp (Real.log (D : ℝ)) := by
        apply Real.exp_le_exp.mpr
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        exact htwenty
      _ = (D : ℝ) := Real.exp_log hDpos
  have htSqrt : t ^ k ≤ Real.sqrt D := by
    apply Real.le_sqrt_of_sq_le
    calc
      (t ^ k) ^ 2 = L ^ (20 * k) := by
        simp only [t, alonMeanDegree]
        ring
      _ ≤ (D : ℝ) := hpow20
  have hmain :
      4 * ((s + 1 : ℕ) : ℝ) * t ^ k ≤ (D : ℝ) := by
    calc
      4 * ((s + 1 : ℕ) : ℝ) * t ^ k ≤
          Real.sqrt D * Real.sqrt D :=
        mul_le_mul hcutoff htSqrt
          (pow_nonneg (pow_nonneg hLpos.le _) _) (Real.sqrt_nonneg _)
      _ = (D : ℝ) := Real.mul_self_sqrt hDpos.le
  have hfourpos : (0 : ℝ) < 4 * ((s + 1 : ℕ) : ℝ) := by positivity
  have htdiv : t ^ k ≤ (D : ℝ) /
      (4 * ((s + 1 : ℕ) : ℝ)) := by
    apply (le_div_iff₀ hfourpos).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hmain
  change (t / (D : ℝ)) ^ k ≤ _
  rw [div_pow]
  calc
    t ^ k / (D : ℝ) ^ k ≤
        ((D : ℝ) / (4 * ((s + 1 : ℕ) : ℝ))) /
          (D : ℝ) ^ k :=
      div_le_div_of_nonneg_right htdiv (by positivity)
    _ = (4 * ((s + 1 : ℕ) : ℝ) *
          (D : ℝ) ^ (k - 1))⁻¹ := by
      have hkpos : 0 < k := by omega
      rw [show k = (k - 1) + 1 by omega, pow_succ]
      field_simp
      congr 1

/-- The degree-window event has the exponentially small marginal used by the
LLL, uniformly over a regular host graph. -/
theorem alon_vertex_marginal
    (G : SimpleGraph V) (D : ℕ) (hD : 0 < D)
    (hregular : G.IsRegularOfDegree D)
    (hlog : 1 < alonLogDegree D)
    (hmeanD : alonMeanDegree D ≤ D)
    (v : V) :
    Erdos76.FiniteLocalLemma.eventMass
        (fun S : Finset (Edge G) ↦
          Erdos76.FiniteNibble.bernoulliMass Finset.univ
            (fun _ ↦ alonSamplingProbability D) S)
        (bad G (alonGirthCutoff D) (alonLowerDegree D)
          (alonUpperDegree D) (Sum.inl v)) ≤ alonVertexBound D := by
  let L := alonLogDegree D
  let mean := alonMeanDegree D
  let err := alonDegreeError D
  let q := alonSamplingProbability D
  let delta := alonRelativeDeviation D
  have hLpos : 0 < L := lt_trans zero_lt_one hlog
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hmean0 : 0 ≤ mean := by
    exact pow_nonneg (Real.log_natCast_nonneg D) _
  have hq0 : 0 ≤ q := div_nonneg hmean0 hDpos.le
  have hq1 : q ≤ 1 := by
    apply (div_le_iff₀ hDpos).2
    simpa [mean] using hmeanD
  have hdelta0 : 0 < delta := by
    simp only [delta, alonRelativeDeviation]
    positivity
  have hdelta1 : delta < 1 := by
    simp only [delta, alonRelativeDeviation]
    exact (inv_lt_one₀ (pow_pos hLpos 4)).2 (one_lt_pow₀ hlog (by norm_num))
  have herrMean : err ≤ mean := by
    simp only [err, mean, alonDegreeError, alonMeanDegree]
    calc
      alonLogDegree D ^ 6 = alonLogDegree D ^ 6 * 1 := by ring
      _ ≤ alonLogDegree D ^ 6 * alonLogDegree D ^ 4 := by
        exact mul_le_mul_of_nonneg_left (one_le_pow₀ hlog.le)
          (pow_nonneg hLpos.le _)
      _ = alonLogDegree D ^ 10 := by ring
  have hlowerReal :
      ((alonLowerDegree D : ℕ) : ℝ) ≤ (1 - delta) * mean := by
    have hfloor : ((alonLowerDegree D : ℕ) : ℝ) ≤ mean - err := by
      exact Nat.floor_le (sub_nonneg.mpr herrMean)
    have hid : (1 - delta) * mean = mean - err := by
      simp only [delta, mean, err, alonRelativeDeviation, alonMeanDegree,
        alonDegreeError]
      field_simp [ne_of_gt hLpos]
    rwa [hid]
  have hupperReal :
      (1 + delta) * mean ≤ ((alonUpperDegree D + 1 : ℕ) : ℝ) := by
    have hceil : mean + err ≤ (alonUpperDegree D : ℝ) := by
      exact Nat.le_ceil _
    have hid : (1 + delta) * mean = mean + err := by
      simp only [delta, mean, err, alonRelativeDeviation, alonMeanDegree,
        alonDegreeError]
      field_simp [ne_of_gt hLpos]
    rw [hid]
    exact hceil.trans (by norm_num)
  have hEW : mean = (G.degree v : ℝ) * q := by
    rw [hregular.degree_eq v]
    simp only [q, alonSamplingProbability, mean]
    field_simp
  have hmass := vertex_eventMass_le_two_mul_exp
    (alonGirthCutoff D) (alonLowerDegree D) (alonUpperDegree D) v
    q mean delta hq0 hq1 hmean0 hEW hdelta0 hdelta1 hlowerReal hupperReal
  have hdeltaMean : delta ^ 2 * mean = L ^ 2 := by
    simp only [delta, mean, alonRelativeDeviation, alonMeanDegree]
    field_simp [ne_of_gt hLpos]
    ring
  simpa only [q, delta, mean, alonVertexBound, L, hdeltaMean] using hmass

/-- For large logarithm, the common vertex marginal is below the scalar LLL
budget. -/
theorem alon_vertex_bound_le
    (D : ℕ) (hD : 32 ≤ D) (hlog : 12 ≤ alonLogDegree D) :
    alonVertexBound D ≤ (16 * (D : ℝ))⁻¹ := by
  let L := alonLogDegree D
  have hDpos : (0 : ℝ) < D := by positivity
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hlog
  have hexp : Real.exp (-(L ^ 2) / 6) ≤ Real.exp (-2 * L) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (L - 12)]
  have hexpEq : Real.exp (-2 * L) = ((D : ℝ) ^ 2)⁻¹ := by
    rw [show -2 * L = -(L + L) by ring, Real.exp_neg, Real.exp_add]
    simp only [L, alonLogDegree, Real.exp_log hDpos]
    ring
  unfold alonVertexBound
  change 2 * Real.exp (-(L ^ 2) / 6) ≤ _
  calc
    2 * Real.exp (-(L ^ 2) / 6) ≤ 2 * Real.exp (-2 * L) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 2 * ((D : ℝ) ^ 2)⁻¹ := by rw [hexpEq]
    _ ≤ (16 * (D : ℝ))⁻¹ := by
      rw [show 2 * ((D : ℝ) ^ 2)⁻¹ = 2 / (D : ℝ) ^ 2 by
        simp [div_eq_mul_inv]]
      rw [show (16 * (D : ℝ))⁻¹ = 1 / (16 * (D : ℝ)) by
        simp [one_div]]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hDR : (32 : ℝ) ≤ D := by exact_mod_cast hD
      nlinarith

/-! ## The sparse-subgraph extraction theorem -/

/-- Pointwise form of Alon's sparse-subgraph lemma.  The assumptions are
exactly the six scalar inequalities which hold for all sufficiently large
`D`; all graph- and probability-dependent work has already been discharged
by the finite asymmetric LLL above. -/
theorem exists_alon_sparse_subgraph_of_conditions
    (G : SimpleGraph V) (D : ℕ)
    (hregular : G.IsRegularOfDegree D)
    (hD : 32 ≤ D)
    (hlog : 12 ≤ alonLogDegree D)
    (hloglog : 0 < Real.log (alonLogDegree D))
    (hmeanD : alonMeanDegree D ≤ (D : ℝ))
    (hsD : 2 * alonGirthCutoff D ≤ D)
    (hcutoff :
      4 * ((alonGirthCutoff D + 1 : ℕ) : ℝ) ≤ Real.sqrt D) :
    ∃ H : SimpleGraph V,
      H ≤ G ∧
      ((alonGirthCutoff D + 1 : ℕ) : ℕ∞) ≤ H.egirth ∧
      ∀ v, alonLowerDegree D ≤ H.degree v ∧
        H.degree v ≤ alonUpperDegree D := by
  have hDpos : 0 < D := by omega
  have hDtwo : 2 ≤ D := by omega
  have hlogOne : 1 < alonLogDegree D := lt_of_lt_of_le (by norm_num) hlog
  have hdegree : ∀ v, G.degree v ≤ D := by
    intro v
    rw [hregular.degree_eq v]
  have hq0 : 0 ≤ alonSamplingProbability D := by
    exact div_nonneg (pow_nonneg (le_trans (by norm_num) hlog) _)
      (Nat.cast_nonneg D)
  have hDposReal : (0 : ℝ) < D := by exact_mod_cast hDpos
  have hq1 : alonSamplingProbability D ≤ 1 := by
    rw [alonSamplingProbability]
    exact (div_le_iff₀ hDposReal).2 (by simpa using hmeanD)
  have hvertexBound0 : 0 ≤ alonVertexBound D := by
    unfold alonVertexBound
    positivity
  obtain ⟨S, havoids⟩ := exists_avoiding_of_scalar_bounds G
    (alonGirthCutoff D) (alonLowerDegree D) (alonUpperDegree D) D
    (alonSamplingProbability D) (alonVertexBound D)
    hDtwo hsD hdegree hq0 hq1 hvertexBound0
    (alon_vertex_bound_le D hD hlog)
    (fun k hk3 hks ↦ alon_cycle_scalar D k hDpos hlogOne hloglog
      hcutoff hk3 hks)
    (fun v ↦ alon_vertex_marginal G D hDpos hregular hlogOne hmeanD v)
  exact ⟨sampledGraph G S,
    sampledGraph_spec_of_avoids G S (alonGirthCutoff D)
      (alonLowerDegree D) (alonUpperDegree D) havoids⟩

/-- Universe-uniform eventual form of Alon's Lemma 3.2.  The vertex type is
quantified *inside* the eventual quantifier, so the threshold depends only on
`D` and works simultaneously for every finite regular graph. -/
theorem eventually_exists_alon_sparse_subgraph :
    ∀ᶠ D : ℕ in atTop,
      ∀ (W : Type u) [Fintype W] (G : SimpleGraph W),
        G.IsRegularOfDegree D →
        ∃ H : SimpleGraph W,
          H ≤ G ∧
          (((⌊Real.log (D : ℝ) /
              (20 * Real.log (Real.log (D : ℝ)))⌋₊ + 1 : ℕ) : ℕ∞) ≤
            H.egirth) ∧
          ∀ v,
            ⌊Real.log (D : ℝ) ^ 10 - Real.log (D : ℝ) ^ 6⌋₊ ≤
                H.degree v ∧
              H.degree v ≤
                ⌈Real.log (D : ℝ) ^ 10 + Real.log (D : ℝ) ^ 6⌉₊ := by
  filter_upwards [AlonScalar.eventually_alon_scalar_conditions] with D hscalar
  rcases hscalar with ⟨hD, hlog, hloglog, hmeanD, hsD, hcutoff⟩
  intro W _ G hregular
  letI : DecidableEq W := Classical.decEq W
  have hlog' : 12 ≤ alonLogDegree D := by
    simpa [alonLogDegree] using hlog
  have hloglog' : 0 < Real.log (alonLogDegree D) := by
    simpa [alonLogDegree] using hloglog
  have hmeanD' : alonMeanDegree D ≤ (D : ℝ) := by
    simpa [alonMeanDegree, alonLogDegree] using hmeanD
  have hsD' : 2 * alonGirthCutoff D ≤ D := by
    simpa [alonGirthCutoff, alonLogDegree] using hsD
  have hcutoff' :
      4 * ((alonGirthCutoff D + 1 : ℕ) : ℝ) ≤ Real.sqrt D := by
    simpa [alonGirthCutoff, alonLogDegree] using hcutoff
  obtain ⟨H, hHG, hgirth, hdegrees⟩ :=
    exists_alon_sparse_subgraph_of_conditions G D hregular hD hlog'
      hloglog' hmeanD' hsD' hcutoff'
  refine ⟨H, hHG, ?_, ?_⟩
  · simpa [alonGirthCutoff, alonLogDegree] using hgirth
  · simpa [alonLowerDegree, alonUpperDegree, alonMeanDegree,
      alonDegreeError, alonLogDegree] using hdegrees

end

end AlonSparseSubgraph
end Erdos622
