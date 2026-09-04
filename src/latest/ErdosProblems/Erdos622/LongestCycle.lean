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
import ErdosProblems.Erdos622.DiracStability
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Connectivity consequences of bi-density

This file isolates the deterministic input to the longest-cycle part of the
Krivelevich--Lee--Sudakov stability argument.  If every two sets of size at
least `k` have an edge between them, and every vertex has degree at least
`2 * k - 1`, then deleting fewer than `k` vertices leaves a connected graph.
The same density hypothesis also rules out an independent set of size `k`.

The proof is a component exchange argument.  If two surviving vertices are
in different components after deleting `C`, let `A` be the component of the
first and `B` its complement among the surviving vertices.  Every neighbour
of the first vertex is in `A ∪ C`, and every neighbour of the second is in
`B ∪ C`.  The degree bound makes both sides have at least `k` vertices, while
there is no edge from `A` to `B`, contradicting bi-density.

This is the exact connectivity/independence interface consumed by the usual
Chvátal--Erdős longest-cycle theorem.  Keeping it separate avoids hiding any
of the vertex-deletion bookkeeping in that later exchange proof.
-/

open Finset
open scoped SimpleGraph

namespace Erdos622
namespace LongestCycle

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Longest paths -/

/-- A path which has maximum length among all paths in the graph. -/
def IsLongestPath {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧
    ∀ ⦃u v : V⦄ (q : G.Walk u v), q.IsPath → q.length ≤ p.length

/-- Every nonempty finite graph has a longest path. -/
theorem exists_isLongestPath [Nonempty V] :
    ∃ (a b : V) (p : G.Walk a b), IsLongestPath p := by
  obtain ⟨a, b, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  exact ⟨a, b, p, hp, fun {_ _} q hq ↦ hmax _ _ q hq⟩

/-- A neighbour of the terminal endpoint of a longest path already lies on
the path; otherwise concatenating that edge makes a longer path. -/
theorem IsLongestPath.end_neighbor_mem_support {a b z : V}
    {p : G.Walk a b} (hp : IsLongestPath p) (hbz : G.Adj b z) :
    z ∈ p.support := by
  by_contra hz
  have hlonger : (p.concat hbz).IsPath := hp.1.concat hz hbz
  have hle := hp.2 (p.concat hbz) hlonger
  simp at hle

/-- The analogous endpoint fact at the start of a longest path. -/
theorem IsLongestPath.start_neighbor_mem_support {a b z : V}
    {p : G.Walk a b} (hp : IsLongestPath p) (hza : G.Adj z a) :
    z ∈ p.support := by
  by_contra hz
  have hlonger : (p.cons hza).IsPath := hp.1.cons hz
  have hle := hp.2 (p.cons hza) hlonger
  simp at hle

/-- The neighbour set of the terminal endpoint is contained in the support
of a longest path with that endpoint removed. -/
theorem IsLongestPath.neighborFinset_end_subset_erase {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) :
    G.neighborFinset b ⊆ p.support.toFinset.erase b := by
  intro z hz
  have hbz : G.Adj b z := (G.mem_neighborFinset b z).mp hz
  exact Finset.mem_erase.mpr
    ⟨hbz.ne.symm, List.mem_toFinset.mpr (hp.end_neighbor_mem_support hbz)⟩

/-- Consequently, each endpoint degree is at most the length of a longest
path.  This is the basic numerical input to endpoint-rotation arguments. -/
theorem IsLongestPath.degree_end_le_length {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) :
    G.degree b ≤ p.length := by
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset b).card ≤ (p.support.toFinset.erase b).card :=
      Finset.card_le_card hp.neighborFinset_end_subset_erase
    _ = p.length := by
      rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr p.end_mem_support)]
      rw [List.toFinset_card_of_nodup hp.1.support_nodup, p.length_support]
      omega

/-- The neighbour set of the initial endpoint is likewise contained in the
support with that endpoint removed. -/
theorem IsLongestPath.neighborFinset_start_subset_erase {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) :
    G.neighborFinset a ⊆ p.support.toFinset.erase a := by
  intro z hz
  have haz : G.Adj a z := (G.mem_neighborFinset a z).mp hz
  exact Finset.mem_erase.mpr
    ⟨haz.ne.symm, List.mem_toFinset.mpr (hp.start_neighbor_mem_support haz.symm)⟩

/-- The same endpoint degree estimate at the start of a longest path. -/
theorem IsLongestPath.degree_start_le_length {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) :
    G.degree a ≤ p.length := by
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset a).card ≤ (p.support.toFinset.erase a).card :=
      Finset.card_le_card hp.neighborFinset_start_subset_erase
    _ = p.length := by
      rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr p.start_mem_support)]
      rw [List.toFinset_card_of_nodup hp.1.support_nodup, p.length_support]
      omega

private theorem exists_crossing_of_walk {S : Finset V} {u v : V}
    (q : G.Walk u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x y : V, x ∈ S ∧ y ∉ S ∧ G.Adj x y := by
  induction q with
  | nil => exact (hv hu).elim
  | @cons u w v huw q ih =>
      by_cases hw : w ∈ S
      · exact ih hw hv
      · exact ⟨u, w, hu, hw, huw⟩

/-- Closing a sufficiently long path by an edge between its endpoints gives
a cycle with exactly the same vertex support. -/
theorem IsLongestPath.exists_isCycle_of_end_adj {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) (hba : G.Adj b a)
    (hlen : 2 ≤ p.length) :
    ∃ q : G.Walk a a,
      q.IsCycle ∧ (∀ z : V, z ∈ q.support ↔ z ∈ p.support) ∧
        q.length = p.length + 1 := by
  let q : G.Walk a a := p.reverse.cons hba.symm
  have hedge : s(a, b) ∉ p.reverse.edges := by
    intro hedge
    have hedge' : s(a, b) ∈ p.edges := by simpa using hedge
    have hone := hp.1.length_eq_one_of_mem_edges hedge'
    omega
  have hq : q.IsCycle := by
    change (p.reverse.cons hba.symm).IsCycle
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    exact ⟨(SimpleGraph.Walk.isPath_reverse_iff p).mpr hp.1, hedge⟩
  refine ⟨q, hq, ?_, by simp [q]⟩
  intro z
  simp only [q, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_reverse, List.mem_cons, List.mem_reverse]
  constructor
  · rintro (rfl | hz)
    · exact p.start_mem_support
    · exact hz
  · exact Or.inr

/-- The standard cycle-extension consequence of longest-path maximality.
In a connected graph, if the endpoints of a longest path of length at least
two are adjacent, then the path visits every vertex exactly once. -/
theorem IsLongestPath.isHamiltonian_of_connected_of_end_adj {a b : V}
    {p : G.Walk a b} (hp : IsLongestPath p) (hconn : G.Connected)
    (hba : G.Adj b a) (hlen : 2 ≤ p.length) :
    p.IsHamiltonian := by
  apply hp.1.isHamiltonian_of_mem
  intro w
  by_contra hw
  obtain ⟨walk⟩ := hconn a w
  obtain ⟨z, t, hzSupport, htSupport, hzt⟩ :=
    exists_crossing_of_walk walk
      (List.mem_toFinset.mpr p.start_mem_support)
      (fun hw' ↦ hw (List.mem_toFinset.mp hw'))
  obtain ⟨q, hq, hqSupport, hqLength⟩ :=
    hp.exists_isCycle_of_end_adj hba hlen
  have hzq : z ∈ q.support := (hqSupport z).mpr
    (List.mem_toFinset.mp hzSupport)
  let r : G.Walk z z := q.rotate z hzq
  have hr : r.IsCycle := hq.rotate hzq
  have htNotR : t ∉ r.support := by
    intro htR
    have htQ : t ∈ q.support :=
      (SimpleGraph.Walk.mem_support_rotate_iff q z hzq).mp htR
    exact htSupport (List.mem_toFinset.mpr ((hqSupport t).mp htQ))
  have htNotTail : t ∉ r.tail.support := by
    intro ht
    have ht' : t ∈ r.support.tail := by
      rwa [SimpleGraph.Walk.support_tail_of_not_nil r hr.not_nil] at ht
    exact htNotR (List.tail_subset r.support ht')
  have hlonger : (r.tail.concat hzt).IsPath :=
    hr.isPath_tail.concat htNotTail hzt
  have hmax := hp.2 (r.tail.concat hzt) hlonger
  have hrlen : r.length = p.length + 1 := by
    simpa [r] using hqLength
  have htaillen : r.tail.length = r.length - 1 :=
    SimpleGraph.Walk.length_tail r
  simp only [SimpleGraph.Walk.length_concat] at hmax
  omega

/-- A graph-level closing criterion.  To prove Hamiltonicity it is enough to
show that the endpoints of every longest path are adjacent; minimum degree
two supplies the ordinary (length-at-least-three) cycle convention. -/
theorem isHamiltonian_of_longestPath_end_adj [Nonempty V]
    (hconn : G.Connected) (hDegree : ∀ v : V, 2 ≤ G.degree v)
    (hclose : ∀ ⦃a b : V⦄ (p : G.Walk a b),
      IsLongestPath p → G.Adj b a) :
    G.IsHamiltonian := by
  obtain ⟨a, b, p, hp⟩ := exists_isLongestPath (G := G)
  have hlen : 2 ≤ p.length :=
    (hDegree b).trans hp.degree_end_le_length
  have hba : G.Adj b a := hclose p hp
  have hpHam : p.IsHamiltonian :=
    hp.isHamiltonian_of_connected_of_end_adj hconn hba hlen
  obtain ⟨q, hq, _hqSupport, hqLength⟩ :=
    hp.exists_isCycle_of_end_adj hba hlen
  intro _hcard
  refine ⟨a, q, ?_⟩
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨hq, ?_⟩
  rw [hqLength, hpHam.length_eq]
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos
  omega

/-- The graph left after deleting the finite vertex set `C`. -/
abbrev deleteVertices (G : SimpleGraph V) (C : Finset V) :
    SimpleGraph {v : V // v ∉ C} :=
  G.induce {v : V | v ∉ C}

/-- A direct finite formulation of vertex-connectivity at least `k`.

For `k = 0` the condition is vacuous.  For positive `k`, the nonemptiness
part of `Connected` says in particular that deleting fewer than `k` vertices
does not delete the whole graph. -/
def VertexConnectedAtLeast (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ C : Finset V, C.card < k → (deleteVertices G C).Connected

/-- Strong bi-density gives the strict independence-number bound needed in a
longest-cycle argument. -/
theorem card_lt_of_isIndepSet_of_biDenseAbove {k b : ℕ}
    (hDense : DiracStability.BiDenseAbove G k b) {A : Finset V}
    (hA : G.IsIndepSet (A : Set V)) : A.card < k := by
  by_contra hnot
  have hkA : k ≤ A.card := by omega
  obtain ⟨A', hA'A, hA'card⟩ := Finset.exists_subset_card_eq hkA
  have hA'ind : G.IsIndepSet (A' : Set V) := by
    intro u hu v hv huv
    exact hA (hA'A hu) (hA'A hv) huv
  exact DiracStability.not_hasIndependentSetAt_of_biDenseAbove G hDense
    ⟨A', hA'card, hA'ind⟩

private theorem card_union_bound (A C : Finset V) :
    (A ∪ C).card ≤ A.card + C.card := by
  exact Finset.card_union_le A C

private theorem degree_le_card_add_of_neighbor_subset {v : V}
    {A C : Finset V} (hsub : G.neighborFinset v ⊆ A ∪ C) :
    G.degree v ≤ A.card + C.card := by
  rw [← G.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card hsub).trans (card_union_bound A C)

/-- The core component-exchange lemma.  Under the two numerical hypotheses,
any two vertices surviving a deletion of fewer than `k` vertices are
reachable in the induced surviving graph. -/
theorem reachable_deleteVertices_of_biDenseAbove
    {k : ℕ} (hDense : DiracStability.BiDenseAbove G k 0)
    (hDegree : ∀ v : V, 2 * k ≤ G.degree v + 1)
    {C : Finset V} (hC : C.card < k)
    (x y : {v : V // v ∉ C}) :
    (deleteVertices G C).Reachable x y := by
  let H : SimpleGraph {v : V // v ∉ C} := deleteVertices G C
  by_contra hxy
  let A' : Finset {v : V // v ∉ C} :=
    Finset.univ.filter fun z ↦ H.Reachable x z
  let B' : Finset {v : V // v ∉ C} := Finset.univ \ A'
  let e : {v : V // v ∉ C} ↪ V := Function.Embedding.subtype _
  let A : Finset V := A'.map e
  let B : Finset V := B'.map e
  have hxA' : x ∈ A' := by
    simp [A', SimpleGraph.Reachable.rfl]
  have hyB' : y ∈ B' := by
    simp only [B', Finset.mem_sdiff, Finset.mem_univ, true_and]
    simp only [A', Finset.mem_filter, Finset.mem_univ, true_and]
    exact hxy
  have hAcard : k ≤ A.card := by
    have hneighbors : G.neighborFinset x.1 ⊆ A ∪ C := by
      intro z hz
      by_cases hzC : z ∈ C
      · exact Finset.mem_union_right A hzC
      · apply Finset.mem_union_left C
        apply Finset.mem_map.mpr
        let z' : {v : V // v ∉ C} := ⟨z, hzC⟩
        refine ⟨z', ?_, rfl⟩
        simp only [A', Finset.mem_filter, Finset.mem_univ, true_and]
        have hxz : H.Adj x z' := by
          exact SimpleGraph.induce_adj.mpr
            ((G.mem_neighborFinset x.1 z).mp hz)
        exact hxz.reachable
    have hdeg := degree_le_card_add_of_neighbor_subset
      (G := G) hneighbors
    have hxdeg := hDegree x.1
    have hmap : A.card = A'.card := by
      simpa [A] using Finset.card_map e A'
    omega
  have hBcard : k ≤ B.card := by
    have hneighbors : G.neighborFinset y.1 ⊆ B ∪ C := by
      intro z hz
      by_cases hzC : z ∈ C
      · exact Finset.mem_union_right B hzC
      · apply Finset.mem_union_left C
        apply Finset.mem_map.mpr
        let z' : {v : V // v ∉ C} := ⟨z, hzC⟩
        refine ⟨z', ?_, rfl⟩
        simp only [B', Finset.mem_sdiff, Finset.mem_univ, true_and]
        simp only [A', Finset.mem_filter, Finset.mem_univ, true_and]
        intro hxzReach
        have hzy : H.Adj z' y := by
          exact SimpleGraph.induce_adj.mpr
            (((G.mem_neighborFinset y.1 z).mp hz).symm)
        exact hxy (hxzReach.trans hzy.reachable)
    have hdeg := degree_le_card_add_of_neighbor_subset
      (G := G) hneighbors
    have hydeg := hDegree y.1
    have hmap : B.card = B'.card := by
      simpa [B] using Finset.card_map e B'
    omega
  have hEmpty :
      @SimpleGraph.interedges V G (Classical.decRel G.Adj) A B = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro uv huv
    have huv' : (uv.1 ∈ A ∧ uv.2 ∈ B) ∧ G.Adj uv.1 uv.2 := by
      simpa [SimpleGraph.interedges_def] using huv
    obtain ⟨⟨huA, hvB⟩, huvAdj⟩ := huv'
    obtain ⟨u, huA', huEq⟩ := Finset.mem_map.mp huA
    obtain ⟨v, hvB', hvEq⟩ := Finset.mem_map.mp hvB
    change u.1 = uv.1 at huEq
    change v.1 = uv.2 at hvEq
    rw [← huEq, ← hvEq] at huvAdj
    have huReach : H.Reachable x u := by
      simpa [A'] using huA'
    have hvNotReach : ¬ H.Reachable x v := by
      simpa [B', A'] using hvB'
    have huvH : H.Adj u v := SimpleGraph.induce_adj.mpr huvAdj
    exact hvNotReach (huReach.trans huvH.reachable)
  have hpositive := hDense A B hAcard hBcard
  rw [hEmpty] at hpositive
  simp at hpositive

/-- Strong bi-density and minimum degree `2k-1` imply vertex-connectivity at
least `k`.  The separate order hypothesis is used only to produce a surviving
vertex after a deletion; reachability itself is supplied by the preceding
component-exchange lemma. -/
theorem vertexConnectedAtLeast_of_biDenseAbove
    {k : ℕ} (hkV : k ≤ Fintype.card V)
    (hDense : DiracStability.BiDenseAbove G k 0)
    (hDegree : ∀ v : V, 2 * k ≤ G.degree v + 1) :
    VertexConnectedAtLeast G k := by
  intro C hC
  have hsurvives : ∃ v : V, v ∉ C := by
    by_contra hnot
    push_neg at hnot
    have huniv : (Finset.univ : Finset V) ⊆ C := by
      intro v _
      exact hnot v
    have hcard := Finset.card_le_card huniv
    rw [Finset.card_univ] at hcard
    omega
  let v : {w : V // w ∉ C} := ⟨hsurvives.choose, hsurvives.choose_spec⟩
  let : Nonempty {w : V // w ∉ C} := ⟨v⟩
  exact ⟨fun x y ↦
    reachable_deleteVertices_of_biDenseAbove hDense hDegree hC x y⟩

/-- A packaged form of the two deterministic consequences needed before the
longest-cycle exchange: `k`-vertex-connectivity and independence number
strictly below `k`. -/
theorem connectivity_and_independence_of_biDenseAbove
    {k : ℕ} (hkV : k ≤ Fintype.card V)
    (hDense : DiracStability.BiDenseAbove G k 0)
    (hDegree : ∀ v : V, 2 * k ≤ G.degree v + 1) :
    VertexConnectedAtLeast G k ∧
      ∀ A : Finset V, G.IsIndepSet (A : Set V) → A.card < k := by
  exact ⟨vertexConnectedAtLeast_of_biDenseAbove hkV hDense hDegree,
    fun _ hA ↦ card_lt_of_isIndepSet_of_biDenseAbove hDense hA⟩

end LongestCycle
end Erdos622
