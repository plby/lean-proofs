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
import ErdosProblems.Erdos622.LinearForest
import ErdosProblems.Erdos622.AlonSparseSubgraph
import ErdosProblems.Erdos622.External.Erdos76.HypergraphGreedyColoring
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# A direct finite linear-forest extraction

This file records the completely elementary part of the linear-arboricity
input used for Erdos Problem 622.  A graph is viewed as a rank-two indexed
hypergraph.  Greedy coloring of its conflict graph partitions its edges into
matchings, and averaging therefore produces a large matching, hence a linear
forest.

The bound proved here is deliberately stated with its exact constant.  It is
not Alon's asymptotic linear-arboricity theorem: greedy conflict coloring uses
`2 * D + 1` colors, whereas the DKM argument needs asymptotically `D / 2`
linear forests.  Thus this checked result also isolates, without concealing it
in an interface, the factor-four gap that the probabilistic theorem must close.
-/

open Finset

namespace Erdos622

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

namespace AlonDirect

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A matching represented directly by a finset of pairwise
endpoint-disjoint graph edges. -/
def FiniteMatchingEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : Finset (Sym2 V)) : Prop :=
  M ⊆ G.edgeFinset ∧
    (M : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset

/-- The edges of a finite simple graph, regarded as a two-uniform indexed
hypergraph. -/
def graphEdgeHypergraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos76.FiniteHypergraph V G.edgeFinset where
  vertexSet := univ
  support e := e.1.toFinset
  support_subset_vertexSet _ := subset_univ _

@[simp]
lemma graphEdgeHypergraph_support (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : G.edgeFinset) :
    (graphEdgeHypergraph G).support e = e.1.toFinset :=
  rfl

lemma graphEdgeHypergraph_isUniform_two (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (graphEdgeHypergraph G).IsUniform 2 := by
  intro e
  exact G.card_toFinset_mem_edgeFinset e

lemma graphEdgeHypergraph_edgeDegree (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    (graphEdgeHypergraph G).edgeDegree v = G.degree v := by
  rw [Erdos76.FiniteHypergraph.edgeDegree]
  change ((univ : Finset G.edgeFinset).filter fun e => v ∈ e.1.toFinset).card = G.degree v
  rw [← G.card_incidenceFinset_eq_degree]
  apply Finset.card_bij (fun e _ => e.1)
  · intro e he
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨SimpleGraph.mem_edgeFinset.mp e.2,
      Sym2.mem_toFinset.mp ((mem_filter.mp he).2)⟩
  · intro e he f hf hef
    exact Subtype.ext hef
  · intro e he
    refine ⟨⟨e, (G.incidenceFinset_subset v he)⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    have he' : e ∈ G.incidenceSet v := (G.mem_incidenceFinset v e).mp he
    exact Sym2.mem_toFinset.mpr he'.2

/-- A hypergraph matching among graph edges is a finite graph matching in the
usual pairwise-disjoint-endpoint sense. -/
lemma isFiniteMatching_of_hypergraph_isMatching (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : Finset G.edgeFinset)
    (hM : (graphEdgeHypergraph G).IsMatching M) :
    FiniteMatchingEdges G
      (M.map (Function.Embedding.subtype fun e : Sym2 V => e ∈ G.edgeFinset)) := by
  constructor
  · intro e he
    obtain ⟨f, _hfM, rfl⟩ := Finset.mem_map.mp he
    exact f.2
  · intro e he f hf hef
    obtain ⟨e', he'M, rfl⟩ := Finset.mem_map.mp he
    obtain ⟨f', hf'M, rfl⟩ := Finset.mem_map.mp hf
    have he'f' : e' ≠ f' := by
      intro h
      apply hef
      exact congrArg Subtype.val h
    exact hM he'M hf'M he'f'

/-- Greedy conflict coloring gives a matching whose cardinality is at least
the average over `2 * D + 1` colors.  This statement is unconditional and
uniform in the finite vertex type. -/
theorem exists_large_finiteMatching (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D) :
    ∃ M : Finset (Sym2 V),
      FiniteMatchingEdges G M ∧
      G.edgeFinset.card ≤ (2 * D + 1) * M.card := by
  let H := graphEdgeHypergraph G
  have hHuniform : H.IsUniform 2 := graphEdgeHypergraph_isUniform_two G
  have hHdegree : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D := by
    intro v _hv
    simpa [H, graphEdgeHypergraph_edgeDegree] using hdegree v
  obtain ⟨c⟩ := H.exists_edgeColoring_uniform_degree hHuniform hHdegree
  have hq : 0 < 2 * D + 1 := Nat.succ_pos _
  obtain ⟨i, hi⟩ :=
    c.exists_card_le_mul_restrictedColorClass
      (univ : Finset G.edgeFinset) hq
  let Msub : Finset G.edgeFinset :=
    c.restrictedColorClass (univ : Finset G.edgeFinset) i
  let M : Finset (Sym2 V) :=
    Msub.map (Function.Embedding.subtype fun e : Sym2 V => e ∈ G.edgeFinset)
  have hMhyper : H.IsMatching Msub :=
    c.restrictedColorClass_isMatching (univ : Finset G.edgeFinset) i
  refine ⟨M, ?_, ?_⟩
  · exact isFiniteMatching_of_hypergraph_isMatching G Msub hMhyper
  · have hcardM : M.card = Msub.card := by
      simp [M]
    simpa [Msub, M, hcardM] using hi

/-- Every graph of maximum degree at most `D` contains a matching, and hence
a linear forest, satisfying the same integral average bound.  The witness is
kept as an edge finset because this representation is directly consumable by
the matching and path-splicing layer of the Erdos 622 development. -/
theorem exists_large_linearForest_edges (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D) :
    ∃ M : Finset (Sym2 V),
      FiniteMatchingEdges G M ∧
      G.edgeFinset.card ≤ (2 * D + 1) * M.card :=
  exists_large_finiteMatching G D hdegree

/-! ## Finite codes for the short-cycle local-lemma estimates

The probabilistic construction also needs uniform bounds on the number of
short cycles meeting a fixed vertex or edge.  The elementary core of those
bounds is that a walk is specified one neighbour at a time.  We record that
core with an explicit finite code.  Closing a prefix of length `n` back to its
initial vertex gives a closed walk of length `n + 1`; fixing one additional
edge gives the `D ^ n` bound for a cycle of length `n + 2` through that edge.
-/

/-- A length-`n` walk starting at `u`, represented as successive choices from
finite neighbour sets.  Its endpoint is intentionally not an index: this
makes the elementary product bound on the number of codes transparent. -/
def WalkCode (G : SimpleGraph V) [DecidableRel G.Adj] :
    (n : ℕ) → V → Type u
  | 0, _ => PUnit
  | n + 1, u => Σ w : G.neighborFinset u, WalkCode G n w

noncomputable instance walkCodeFintype (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (u : V) : Fintype (WalkCode G n u) := by
  induction n generalizing u with
  | zero =>
      change Fintype PUnit
      infer_instance
  | succ n ih =>
      change Fintype (Σ w : G.neighborFinset u, WalkCode G n w)
      letI (w : G.neighborFinset u) : Fintype (WalkCode G n w) := ih w
      infer_instance

/-- The final vertex of a walk code. -/
def WalkCode.endpoint (G : SimpleGraph V) [DecidableRel G.Adj] :
    {n : ℕ} → {u : V} → WalkCode G n u → V
  | 0, u, _ => u
  | _ + 1, _, ⟨_, q⟩ => q.endpoint

/-- Interpret a finite walk code as a Mathlib walk. -/
def WalkCode.toWalk (G : SimpleGraph V) [DecidableRel G.Adj] :
    {n : ℕ} → {u : V} → (q : WalkCode G n u) → G.Walk u q.endpoint
  | 0, _, _ => SimpleGraph.Walk.nil
  | _ + 1, _, ⟨w, q⟩ =>
      SimpleGraph.Walk.cons ((G.mem_neighborFinset _ _).mp w.2) q.toWalk

/-- Encode a Mathlib walk by its successive finite-neighbour choices. -/
def WalkCode.ofWalk (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} : (p : G.Walk u v) → WalkCode G p.length u
  | SimpleGraph.Walk.nil => PUnit.unit
  | SimpleGraph.Walk.cons h p =>
      ⟨⟨_, by simpa using h⟩, WalkCode.ofWalk G p⟩

@[simp]
lemma WalkCode.endpoint_ofWalk (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) : (WalkCode.ofWalk G p).endpoint = v := by
  induction p with
  | nil => rfl
  | cons h p ih => simpa [WalkCode.ofWalk, WalkCode.endpoint] using ih

@[simp]
lemma WalkCode.support_toWalk_ofWalk (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) :
    (WalkCode.ofWalk G p).toWalk.support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      change _ :: (WalkCode.ofWalk G p).toWalk.support = _ :: p.support
      rw [ih]

@[simp]
lemma WalkCode.toWalk_ofWalk (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (p : G.Walk u v) :
    (WalkCode.ofWalk G p).toWalk.copy rfl (WalkCode.endpoint_ofWalk G p) = p := by
  apply SimpleGraph.Walk.ext_support
  simpa using WalkCode.support_toWalk_ofWalk G p

@[simp]
lemma WalkCode.length_toWalk (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} {u : V} (q : WalkCode G n u) : q.toWalk.length = n := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      rcases q with ⟨w, q⟩
      simp only [WalkCode.toWalk, SimpleGraph.Walk.length_cons]
      exact congrArg Nat.succ (ih q)

/-- At maximum degree `D`, there are at most `D ^ n` length-`n` walk codes
from any prescribed initial vertex. -/
theorem card_walkCode_le_pow (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D) (n : ℕ) (u : V) :
    Fintype.card (WalkCode G n u) ≤ D ^ n := by
  induction n generalizing u with
  | zero => simp [WalkCode]
  | succ n ih =>
      change Fintype.card (Σ w : G.neighborFinset u, WalkCode G n w) ≤ D ^ (n + 1)
      rw [Fintype.card_sigma]
      calc
        ∑ w : G.neighborFinset u, Fintype.card (WalkCode G n w) ≤
            ∑ _w : G.neighborFinset u, D ^ n :=
          Finset.sum_le_sum fun w _hw => ih w
        _ = G.degree u * D ^ n := by simp [SimpleGraph.card_neighborFinset_eq_degree]
        _ ≤ D * D ^ n := Nat.mul_le_mul_right (D ^ n) (hdegree u)
        _ = D ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

/-- A prefix of length `n` starting at `u`, together with the final edge
which closes it back to `u`.  It represents a rooted closed walk of total
length `n + 1`. -/
def RootedClosedWalkCode (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (u : V) :=
  {q : WalkCode G n u // G.Adj q.endpoint u}

noncomputable instance rootedClosedWalkCodeFintype (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (u : V) :
    Fintype (RootedClosedWalkCode G n u) := by
  unfold RootedClosedWalkCode
  infer_instance

/-- Rooted closed walks of length `n + 1` have the source-scale bound
`D ^ n`: the closing edge is forced once the length-`n` prefix is fixed. -/
theorem card_rootedClosedWalkCode_le_pow (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) (u : V) :
    Fintype.card (RootedClosedWalkCode G n u) ≤ D ^ n := by
  calc
    Fintype.card (RootedClosedWalkCode G n u) ≤
        Fintype.card (WalkCode G n u) := Fintype.card_subtype_le _
    _ ≤ D ^ n := card_walkCode_le_pow G D hdegree n u

/-- A fixed oriented edge followed by a length-`n` prefix and its forced
closing edge.  It represents an edge-rooted closed walk of length `n + 2`.
The endpoints are passed explicitly, which is the form needed in local
dependency estimates. -/
def EdgeRootedClosedWalkCode (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) {u v : V} (_huv : G.Adj u v) :=
  {q : WalkCode G n v // G.Adj q.endpoint u}

noncomputable instance edgeRootedClosedWalkCodeFintype (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) {u v : V} (huv : G.Adj u v) :
    Fintype (EdgeRootedClosedWalkCode G n huv) := by
  unfold EdgeRootedClosedWalkCode
  infer_instance

/-- For a fixed edge, the number of edge-rooted closed-walk codes of length
`n + 2` is at most `D ^ n`.  In the usual cycle-length notation `r = n + 2`,
this is precisely the `D ^ (r - 2)` estimate. -/
theorem card_edgeRootedClosedWalkCode_le_pow (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) {u v : V} (huv : G.Adj u v) :
    Fintype.card (EdgeRootedClosedWalkCode G n huv) ≤ D ^ n := by
  calc
    Fintype.card (EdgeRootedClosedWalkCode G n huv) ≤
        Fintype.card (WalkCode G n v) := Fintype.card_subtype_le _
    _ ≤ D ^ n := card_walkCode_le_pow G D hdegree n v

/-- The closed Mathlib walk represented by a rooted code. -/
def RootedClosedWalkCode.toWalk (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} {u : V} (q : RootedClosedWalkCode G n u) : G.Walk u u :=
  q.1.toWalk.concat q.2

@[simp]
lemma RootedClosedWalkCode.length_toWalk (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} {u : V}
    (q : RootedClosedWalkCode G n u) : q.toWalk.length = n + 1 := by
  simp [RootedClosedWalkCode.toWalk, WalkCode.length_toWalk]

/-- The closed Mathlib walk represented by an edge-rooted code. -/
def EdgeRootedClosedWalkCode.toWalk (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} {u v : V} {huv : G.Adj u v}
    (q : EdgeRootedClosedWalkCode G n huv) : G.Walk u u :=
  SimpleGraph.Walk.cons huv (q.1.toWalk.concat q.2)

@[simp]
lemma EdgeRootedClosedWalkCode.length_toWalk (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} {u v : V} {huv : G.Adj u v}
    (q : EdgeRootedClosedWalkCode G n huv) : q.toWalk.length = n + 2 := by
  simp [EdgeRootedClosedWalkCode.toWalk, WalkCode.length_toWalk]

/-- Rooted (oriented) simple-cycle codes of length `n + 1`.  This is the
actual cycle-event type; it is a subtype of the closed-walk codes counted
above. -/
def RootedCycleCode (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (u : V) :=
  {q : RootedClosedWalkCode G n u // q.toWalk.IsCycle}

noncomputable instance rootedCycleCodeFintype (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (u : V) :
    Fintype (RootedCycleCode G n u) := by
  unfold RootedCycleCode
  infer_instance

/-- A fixed initial oriented edge and an oriented simple cycle of length
`n + 2` containing it. -/
def EdgeRootedCycleCode (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) {u v : V} (huv : G.Adj u v) :=
  {q : EdgeRootedClosedWalkCode G n huv // q.toWalk.IsCycle}

noncomputable instance edgeRootedCycleCodeFintype (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) {u v : V} (huv : G.Adj u v) :
    Fintype (EdgeRootedCycleCode G n huv) := by
  unfold EdgeRootedCycleCode
  infer_instance

/-- There are at most `D ^ n` rooted oriented cycles of length `n + 1`
with a prescribed root.  Since forgetting orientation can only reduce the
number, this is the elementary `D ^ (r - 1)` estimate for length `r`. -/
theorem card_rootedCycleCode_le_pow (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) (u : V) :
    Fintype.card (RootedCycleCode G n u) ≤ D ^ n := by
  calc
    Fintype.card (RootedCycleCode G n u) ≤
        Fintype.card (RootedClosedWalkCode G n u) := Fintype.card_subtype_le _
    _ ≤ D ^ n := card_rootedClosedWalkCode_le_pow G D hdegree n u

/-- There are at most `D ^ n` oriented cycles of length `n + 2` with a
prescribed initial oriented edge.  This is the elementary
`D ^ (r - 2)` estimate for length `r`. -/
theorem card_edgeRootedCycleCode_le_pow (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) {u v : V} (huv : G.Adj u v) :
    Fintype.card (EdgeRootedCycleCode G n huv) ≤ D ^ n := by
  calc
    Fintype.card (EdgeRootedCycleCode G n huv) ≤
        Fintype.card (EdgeRootedClosedWalkCode G n huv) :=
      Fintype.card_subtype_le _
    _ ≤ D ^ n := card_edgeRootedClosedWalkCode_le_pow G D hdegree n huv

/-- The fixed-edge cycle code packaged with a graph dart. -/
abbrev DartRootedCycleCode (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (d : G.Dart) :=
  EdgeRootedCycleCode G n d.adj

/-- Per cycle length, the total number of oriented cycle codes assigned to
any finite set `S` of roots is at most `|S| * D ^ n`.  This is the form used
to count cycle-event neighbours of a vertex bad event. -/
theorem sum_card_rootedCycleCode_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) (S : Finset V) :
    (∑ u ∈ S, Fintype.card (RootedCycleCode G n u)) ≤ S.card * D ^ n := by
  calc
    (∑ u ∈ S, Fintype.card (RootedCycleCode G n u)) ≤
        ∑ _u ∈ S, D ^ n :=
      Finset.sum_le_sum fun u _hu => card_rootedCycleCode_le_pow G D hdegree n u
    _ = S.card * D ^ n := by simp

/-- Per cycle length, a finite set `S` of oriented edges has at most
`|S| * D ^ n` edge-rooted cycle codes of length `n + 2`.  For `|S| = k`
this is the `k * D ^ (r - 2)` local-dependency bound used for a length-`k`
cycle event against the length-`r` cycle events. -/
theorem sum_card_dartRootedCycleCode_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) (S : Finset G.Dart) :
    (∑ d ∈ S, Fintype.card (DartRootedCycleCode G n d)) ≤
      S.card * D ^ n := by
  calc
    (∑ d ∈ S, Fintype.card (DartRootedCycleCode G n d)) ≤
        ∑ _d ∈ S, D ^ n :=
      Finset.sum_le_sum fun d _hd =>
        card_edgeRootedCycleCode_le_pow G D hdegree n d.adj
    _ = S.card * D ^ n := by simp

/-- A finite disjoint union of rooted cycle codes, one fibre over each root
in `S`.  Keeping the root in the code makes this type directly usable as a
target for an injection from a dependency neighbourhood. -/
abbrev RootedCycleNeighborhoodCode (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (S : Finset V) :=
  Σ u : S, RootedCycleCode G n u

/-- A finite disjoint union of edge-rooted cycle codes, one fibre over each
oriented edge in `S`. -/
abbrev DartCycleNeighborhoodCode (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) (S : Finset G.Dart) :=
  Σ d : S, DartRootedCycleCode G n d

/-- Cardinal version of `sum_card_rootedCycleCode_le`. -/
theorem card_rootedCycleNeighborhoodCode_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) (S : Finset V) :
    Fintype.card (RootedCycleNeighborhoodCode G n S) ≤ S.card * D ^ n := by
  rw [Fintype.card_sigma]
  calc
    (∑ u : S, Fintype.card (RootedCycleCode G n u)) ≤
        ∑ _u : S, D ^ n :=
      Finset.sum_le_sum fun u _hu => card_rootedCycleCode_le_pow G D hdegree n u
    _ = S.card * D ^ n := by simp

/-- Cardinal version of the source `k * D ^ (r - 2)` fixed-edge
neighbourhood estimate. -/
theorem card_dartCycleNeighborhoodCode_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) (S : Finset G.Dart) :
    Fintype.card (DartCycleNeighborhoodCode G n S) ≤ S.card * D ^ n := by
  rw [Fintype.card_sigma]
  calc
    (∑ d : S, Fintype.card (DartRootedCycleCode G n d)) ≤
        ∑ _d : S, D ^ n :=
      Finset.sum_le_sum fun d _hd =>
        card_edgeRootedCycleCode_le_pow G D hdegree n d.1.adj
    _ = S.card * D ^ n := by simp

/-! ### Bounds for Mathlib's cycle walks

The next wrapper connects the finite codes to the `Walk.IsCycle` objects used
by the short-cycle-support development. -/

/-- A Mathlib cycle walk of length `n + 1`, rooted at `u`.  The fixed-length
subtype is placed on the inside so its standard finite instance is available
without asserting finiteness of the type of walks of arbitrary length. -/
def RootedCycleWalk (G : SimpleGraph V) (n : ℕ) (u : V) :=
  {p : {p : G.Walk u u // p.length = n + 1} // p.1.IsCycle}

noncomputable instance rootedCycleWalkFintype (G : SimpleGraph V)
    (n : ℕ) (u : V) : Fintype (RootedCycleWalk G n u) := by
  unfold RootedCycleWalk
  infer_instance

/-- Delete the final edge of a nonempty closed walk and encode the remaining
prefix. -/
def RootedClosedWalkCode.ofClosedWalk (G : SimpleGraph V)
    [DecidableRel G.Adj] {u : V} (p : G.Walk u u) (hp : ¬ p.Nil) :
    RootedClosedWalkCode G p.dropLast.length u :=
  ⟨WalkCode.ofWalk G p.dropLast, by
    rw [WalkCode.endpoint_ofWalk]
    exact p.adj_penultimate hp⟩

/-- Decoding the prefix and its closing edge recovers the original closed
walk. -/
@[simp]
lemma RootedClosedWalkCode.toWalk_ofClosedWalk (G : SimpleGraph V)
    [DecidableRel G.Adj] {u : V} (p : G.Walk u u) (hp : ¬ p.Nil) :
    (RootedClosedWalkCode.ofClosedWalk G p hp).toWalk = p := by
  unfold RootedClosedWalkCode.toWalk RootedClosedWalkCode.ofClosedWalk
  apply SimpleGraph.Walk.ext_support
  rw [SimpleGraph.Walk.support_concat, WalkCode.support_toWalk_ofWalk]
  exact p.support_dropLast_concat hp

@[simp]
lemma RootedClosedWalkCode.toWalk_cast (G : SimpleGraph V)
    [DecidableRel G.Adj] {m n : ℕ} {u : V} (h : m = n)
    (q : RootedClosedWalkCode G m u) :
    (h ▸ q : RootedClosedWalkCode G n u).toWalk = q.toWalk := by
  subst n
  rfl

/-- Encode a rooted cycle of length `n + 1` by its length-`n` prefix. -/
def RootedCycleWalk.toClosedWalkCode (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} {u : V} (p : RootedCycleWalk G n u) :
    RootedClosedWalkCode G n u := by
  have hp : ¬ p.1.1.Nil := p.2.not_nil
  have hlength : p.1.1.dropLast.length = n := by
    rw [SimpleGraph.Walk.length_dropLast, p.1.2]
    omega
  exact hlength ▸ RootedClosedWalkCode.ofClosedWalk G p.1.1 hp

@[simp]
lemma RootedCycleWalk.toWalk_toClosedWalkCode (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} {u : V} (p : RootedCycleWalk G n u) :
    (p.toClosedWalkCode G).toWalk = p.1.1 := by
  unfold RootedCycleWalk.toClosedWalkCode
  rw [RootedClosedWalkCode.toWalk_cast]
  exact RootedClosedWalkCode.toWalk_ofClosedWalk G p.1.1 p.2.not_nil

/-- The prefix encoding of rooted fixed-length cycle walks is injective. -/
theorem RootedCycleWalk.toClosedWalkCode_injective (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} {u : V} :
    Function.Injective
      (RootedCycleWalk.toClosedWalkCode G :
        RootedCycleWalk G n u → RootedClosedWalkCode G n u) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have hwalk := congrArg (RootedClosedWalkCode.toWalk G) hpq
  simpa using hwalk

/-- The exact Mathlib-cycle formulation of the rooted
`D ^ (r - 1)` enumeration bound. -/
theorem card_rootedCycleWalk_le_pow (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) (u : V) :
    Fintype.card (RootedCycleWalk G n u) ≤ D ^ n := by
  calc
    Fintype.card (RootedCycleWalk G n u) ≤
        Fintype.card (RootedClosedWalkCode G n u) :=
      Fintype.card_le_of_injective (RootedCycleWalk.toClosedWalkCode G)
        (RootedCycleWalk.toClosedWalkCode_injective G)
    _ ≤ D ^ n := card_rootedClosedWalkCode_le_pow G D hdegree n u

/-- A Mathlib cycle of length `n + 2` whose first oriented edge is the
prescribed edge `u → v`; the stored walk is the remaining tail from `v`
back to `u`. -/
def EdgeRootedCycleWalk (G : SimpleGraph V) (n : ℕ)
    {u v : V} (huv : G.Adj u v) :=
  {p : {p : G.Walk v u // p.length = n + 1} //
    (SimpleGraph.Walk.cons huv p.1).IsCycle}

noncomputable instance edgeRootedCycleWalkFintype (G : SimpleGraph V)
    (n : ℕ) {u v : V} (huv : G.Adj u v) :
    Fintype (EdgeRootedCycleWalk G n huv) := by
  unfold EdgeRootedCycleWalk
  infer_instance

/-- Encode the tail of a cycle after deleting its final closing edge. -/
def EdgeRootedClosedWalkCode.ofTail (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    (p : G.Walk v u) (hp : ¬ p.Nil) :
    EdgeRootedClosedWalkCode G p.dropLast.length huv :=
  ⟨WalkCode.ofWalk G p.dropLast, by
    rw [WalkCode.endpoint_ofWalk]
    exact p.adj_penultimate hp⟩

@[simp]
lemma EdgeRootedClosedWalkCode.toWalk_ofTail (G : SimpleGraph V)
    [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v)
    (p : G.Walk v u) (hp : ¬ p.Nil) :
    (EdgeRootedClosedWalkCode.ofTail G huv p hp).toWalk =
      SimpleGraph.Walk.cons huv p := by
  unfold EdgeRootedClosedWalkCode.toWalk EdgeRootedClosedWalkCode.ofTail
  apply SimpleGraph.Walk.ext_support
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
    WalkCode.support_toWalk_ofWalk]
  rw [p.support_dropLast_concat hp]

@[simp]
lemma EdgeRootedClosedWalkCode.toWalk_cast (G : SimpleGraph V)
    [DecidableRel G.Adj] {m n : ℕ} {u v : V} {huv : G.Adj u v}
    (h : m = n) (q : EdgeRootedClosedWalkCode G m huv) :
    (h ▸ q : EdgeRootedClosedWalkCode G n huv).toWalk = q.toWalk := by
  subst n
  rfl

/-- Prefix encoding of an actual cycle with a prescribed first edge. -/
def EdgeRootedCycleWalk.toClosedWalkCode (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} {u v : V} {huv : G.Adj u v}
    (p : EdgeRootedCycleWalk G n huv) :
    EdgeRootedClosedWalkCode G n huv := by
  have hp : ¬ p.1.1.Nil := by
    intro hp
    have : p.1.1.length = 0 :=
      SimpleGraph.Walk.length_eq_zero_iff.mpr hp
    rw [p.1.2] at this
    omega
  have hlength : p.1.1.dropLast.length = n := by
    rw [SimpleGraph.Walk.length_dropLast, p.1.2]
    omega
  exact hlength ▸ EdgeRootedClosedWalkCode.ofTail G huv p.1.1 hp

@[simp]
lemma EdgeRootedCycleWalk.toWalk_toClosedWalkCode (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} {u v : V} {huv : G.Adj u v}
    (p : EdgeRootedCycleWalk G n huv) :
    (p.toClosedWalkCode G).toWalk = SimpleGraph.Walk.cons huv p.1.1 := by
  unfold EdgeRootedCycleWalk.toClosedWalkCode
  rw [EdgeRootedClosedWalkCode.toWalk_cast]
  exact EdgeRootedClosedWalkCode.toWalk_ofTail G huv p.1.1 (by
    intro hp
    have : p.1.1.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr hp
    rw [p.1.2] at this
    omega)

theorem EdgeRootedCycleWalk.toClosedWalkCode_injective
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ} {u v : V} {huv : G.Adj u v} :
    Function.Injective
      (EdgeRootedCycleWalk.toClosedWalkCode G :
        EdgeRootedCycleWalk G n huv → EdgeRootedClosedWalkCode G n huv) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have hwalk := congrArg (EdgeRootedClosedWalkCode.toWalk G) hpq
  simpa using hwalk

/-- Exact Mathlib-cycle version of the prescribed-edge
`D ^ (r - 2)` bound. -/
theorem card_edgeRootedCycleWalk_le_pow (G : SimpleGraph V)
    [DecidableRel G.Adj] (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (n : ℕ) {u v : V} (huv : G.Adj u v) :
    Fintype.card (EdgeRootedCycleWalk G n huv) ≤ D ^ n := by
  calc
    Fintype.card (EdgeRootedCycleWalk G n huv) ≤
        Fintype.card (EdgeRootedClosedWalkCode G n huv) :=
      Fintype.card_le_of_injective (EdgeRootedCycleWalk.toClosedWalkCode G)
        (EdgeRootedCycleWalk.toClosedWalkCode_injective G)
    _ ≤ D ^ n := card_edgeRootedClosedWalkCode_le_pow G D hdegree n huv

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
prescribed first edge `u → v`. -/
noncomputable def EdgeRootedCycleWalk.ofCycle (G : SimpleGraph V)
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

@[simp]
lemma EdgeRootedCycleWalk.cons_ofCycle (G : SimpleGraph V)
    {n : ℕ} {u v : V} (huv : G.Adj u v) (p : G.Walk u u)
    (hp : p.IsCycle) (hlength : p.length = n + 2) (hsnd : p.snd = v) :
    SimpleGraph.Walk.cons huv
      (EdgeRootedCycleWalk.ofCycle G huv p hp hlength hsnd).1.1 = p := by
  apply SimpleGraph.Walk.ext_support
  unfold EdgeRootedCycleWalk.ofCycle
  simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_copy]
  exact p.cons_support_tail hp.not_nil

/-! ### Distinct short-cycle support indices

The local-lemma experiment indexes a cycle by its edge support, not by a
choice of cyclic enumeration.  We now inject those actual event indices into
the finite codes above. -/

/-- Exact-length short-cycle supports containing an edge incident with `u`. -/
def ShortCycleSupportAtVertexLength (G : SimpleGraph V) (s n : ℕ) (u : V) :=
  {C : AlonSparseSubgraph.ShortCycleSupport G s //
    C.1.card = n + 1 ∧ ∃ e ∈ C.1, u ∈ e.1.toFinset}

noncomputable instance shortCycleSupportAtVertexLengthFintype
    (G : SimpleGraph V) (s n : ℕ) (u : V) :
    Fintype (ShortCycleSupportAtVertexLength G s n u) := by
  unfold ShortCycleSupportAtVertexLength
  infer_instance

namespace ShortCycleSupport

noncomputable def chosenVertex {G : SimpleGraph V} {s : ℕ}
    (C : AlonSparseSubgraph.ShortCycleSupport G s) : V :=
  Classical.choose C.2

noncomputable def chosenWalk {G : SimpleGraph V} {s : ℕ}
    (C : AlonSparseSubgraph.ShortCycleSupport G s) :
    G.Walk (chosenVertex C) (chosenVertex C) :=
  Classical.choose (Classical.choose_spec C.2)

lemma chosenWalk_spec {G : SimpleGraph V} {s : ℕ}
    (C : AlonSparseSubgraph.ShortCycleSupport G s) :
    (chosenWalk C).IsCycle ∧ (chosenWalk C).length ≤ s ∧
      ∀ e : AlonSparseSubgraph.Edge G,
        e ∈ C.1 ↔ e.1 ∈ (chosenWalk C).edges :=
  Classical.choose_spec (Classical.choose_spec C.2)

end ShortCycleSupport

lemma mem_chosenWalk_support_of_mem_cycleSupport
    {G : SimpleGraph V} {s n : ℕ} {u : V}
    (C : ShortCycleSupportAtVertexLength G s n u) :
    u ∈ (ShortCycleSupport.chosenWalk C.1).support := by
  rcases C.2.2 with ⟨e, heC, hue⟩
  have hep : e.1 ∈ (ShortCycleSupport.chosenWalk C.1).edges :=
    ((ShortCycleSupport.chosenWalk_spec C.1).2.2 e).mp heC
  exact SimpleGraph.Walk.mem_support_of_mem_edges hep
    (Sym2.mem_toFinset.mp hue)

/-- Rotate the chosen support witness to the prescribed vertex. -/
noncomputable def ShortCycleSupportAtVertexLength.toRootedCycleWalk
    {G : SimpleGraph V} {s n : ℕ} {u : V}
    (C : ShortCycleSupportAtVertexLength G s n u) :
    RootedCycleWalk G n u := by
  let hu : u ∈ (ShortCycleSupport.chosenWalk C.1).support :=
    mem_chosenWalk_support_of_mem_cycleSupport C
  let q := (ShortCycleSupport.chosenWalk C.1).rotate u hu
  refine ⟨⟨q, ?_⟩, ?_⟩
  · rw [SimpleGraph.Walk.length_rotate]
    rw [← AlonSparseSubgraph.card_shortCycleSupport_eq_length C.1
      (ShortCycleSupport.chosenWalk_spec C.1).1
      (ShortCycleSupport.chosenWalk_spec C.1).2.2]
    exact C.2.1
  · exact (ShortCycleSupport.chosenWalk_spec C.1).1.rotate hu

lemma ShortCycleSupportAtVertexLength.mem_iff_mem_toRootedCycleWalk_edges
    {G : SimpleGraph V} {s n : ℕ} {u : V}
    (C : ShortCycleSupportAtVertexLength G s n u)
    (e : AlonSparseSubgraph.Edge G) :
    e ∈ C.1.1 ↔ e.1 ∈ C.toRootedCycleWalk.1.1.edges := by
  let hu : u ∈ (ShortCycleSupport.chosenWalk C.1).support :=
    mem_chosenWalk_support_of_mem_cycleSupport C
  have hrotate := (ShortCycleSupport.chosenWalk C.1).rotate_edges u hu
  change e ∈ C.1.1 ↔
    e.1 ∈ ((ShortCycleSupport.chosenWalk C.1).rotate u hu).edges
  rw [(ShortCycleSupport.chosenWalk_spec C.1).2.2 e]
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

/-- For length `r = n + 1`, at most `D ^ (r - 1)` distinct cycle-event
supports contain a prescribed vertex. -/
theorem card_shortCycleSupportAtVertexLength_le_pow
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (hdegree : ∀ v, G.degree v ≤ D)
    (s n : ℕ) (u : V) :
    Fintype.card (ShortCycleSupportAtVertexLength G s n u) ≤ D ^ n := by
  calc
    Fintype.card (ShortCycleSupportAtVertexLength G s n u) ≤
        Fintype.card (RootedCycleWalk G n u) :=
      Fintype.card_le_of_injective
        ShortCycleSupportAtVertexLength.toRootedCycleWalk
        ShortCycleSupportAtVertexLength.toRootedCycleWalk_injective
    _ ≤ D ^ n := card_rootedCycleWalk_le_pow G D hdegree n u

/-- The edge coordinate underlying a graph dart. -/
def dartEdgeCoordinate (G : SimpleGraph V) (d : G.Dart) :
    AlonSparseSubgraph.Edge G :=
  ⟨d.edge, by
    simpa [SimpleGraph.mem_edgeFinset] using d.edge_mem⟩

/-- Exact-length short-cycle supports containing a prescribed oriented edge.
The orientation only chooses a canonical code; membership itself is
undirected. -/
def ShortCycleSupportAtDartLength (G : SimpleGraph V) (s n : ℕ)
    (d : G.Dart) :=
  {C : AlonSparseSubgraph.ShortCycleSupport G s //
    C.1.card = n + 2 ∧ dartEdgeCoordinate G d ∈ C.1}

noncomputable instance shortCycleSupportAtDartLengthFintype
    (G : SimpleGraph V) (s n : ℕ) (d : G.Dart) :
    Fintype (ShortCycleSupportAtDartLength G s n d) := by
  unfold ShortCycleSupportAtDartLength
  infer_instance

/-- Forgetting the prescribed edge to its first endpoint produces a member
of the vertex-rooted support family. -/
noncomputable def ShortCycleSupportAtDartLength.toVertex
    {G : SimpleGraph V} {s n : ℕ} {d : G.Dart}
    (C : ShortCycleSupportAtDartLength G s n d) :
    ShortCycleSupportAtVertexLength G s (n + 1) d.fst := by
  refine ⟨C.1, ?_, ?_⟩
  · simpa [Nat.add_assoc] using C.2.1
  · refine ⟨dartEdgeCoordinate G d, C.2.2, ?_⟩
    simp [dartEdgeCoordinate, SimpleGraph.Dart.edge]

/-- A cycle support containing `d` admits a cyclic enumeration whose first
oriented edge is exactly `d`.  The proof rotates to `d.fst`; if `d` is the
closing edge, it reverses the rotated cycle. -/
lemma exists_oriented_cycleWalk_of_mem_dart
    {G : SimpleGraph V} {s n : ℕ} {d : G.Dart}
    (C : ShortCycleSupportAtDartLength G s n d) :
    ∃ p : G.Walk d.fst d.fst,
      p.IsCycle ∧ p.length = n + 2 ∧ p.snd = d.snd ∧
        ∀ e : AlonSparseSubgraph.Edge G, e ∈ C.1.1 ↔ e.1 ∈ p.edges := by
  let Cv := C.toVertex
  let p : G.Walk d.fst d.fst := Cv.toRootedCycleWalk.1.1
  have hpcycle : p.IsCycle := Cv.toRootedCycleWalk.2
  have hplength : p.length = n + 2 := by
    simpa [p, Cv, Nat.add_assoc] using Cv.toRootedCycleWalk.1.2
  have hsupport (e : AlonSparseSubgraph.Edge G) :
      e ∈ C.1.1 ↔ e.1 ∈ p.edges := by
    exact Cv.mem_iff_mem_toRootedCycleWalk_edges e
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

end AlonDirect

end

end Erdos622
