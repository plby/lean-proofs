/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Density

/-!
# Finite edge-counting identities for Erdős Problem 622

This file records the elementary double-counting facts used throughout the
finite graph argument.  `degreeInto G v S` counts neighbours of `v` in `S`,
`edgesInside G S` is the unordered edge set of the induced graph on `S`, and
`edgesAcross G S T` is the number of ordered adjacent pairs from `S` to `T`.
Consequently `edgesAcross` counts an edge once when `S` and `T` are disjoint,
and twice when both arguments are the same set.
-/

open scoped SimpleGraph

namespace Erdos622.EdgeCounting

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of neighbours of `v` that belong to `S`. -/
def degreeInto (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) : ℕ :=
  (G.neighborFinset v ∩ S).card

@[simp]
theorem degreeInto_empty (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degreeInto G v ∅ = 0 := by
  simp [degreeInto]

@[simp]
theorem degreeInto_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degreeInto G v Finset.univ = G.degree v := by
  simp [degreeInto, G.card_neighborFinset_eq_degree]

theorem degreeInto_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) :
    degreeInto G v S ≤ S.card := by
  exact Finset.card_le_card Finset.inter_subset_right

theorem degreeInto_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) :
    degreeInto G v S ≤ G.degree v := by
  simpa [degreeInto, G.card_neighborFinset_eq_degree] using
    Finset.card_le_card
      (Finset.inter_subset_left : G.neighborFinset v ∩ S ⊆ G.neighborFinset v)

theorem degreeInto_mono_set (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {S T : Finset V} (hST : S ⊆ T) :
    degreeInto G v S ≤ degreeInto G v T := by
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_inter] at hw ⊢
  exact ⟨hw.1, hST hw.2⟩

theorem degreeInto_mono_graph {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (v : V) (S : Finset V) :
    degreeInto G v S ≤ degreeInto H v S := by
  apply Finset.card_le_card
  intro w hw
  rw [Finset.mem_inter] at hw ⊢
  exact ⟨by simpa using hGH (by simpa using hw.1), hw.2⟩

theorem degreeInto_union_of_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) {S T : Finset V} (hST : Disjoint S T) :
    degreeInto G v (S ∪ T) = degreeInto G v S + degreeInto G v T := by
  rw [degreeInto, Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right
      Finset.inter_subset_right (Finset.disjoint_of_subset_left
        Finset.inter_subset_right hST))]
  rfl

theorem degreeInto_sdiff_add_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S T : Finset V) :
    degreeInto G v (S \ T) + degreeInto G v (S ∩ T) = degreeInto G v S := by
  rw [← degreeInto_union_of_disjoint G v (Finset.disjoint_sdiff_inter S T)]
  congr 2
  ext w
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  tauto

theorem degreeInto_compl_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) :
    degreeInto G v (Finset.univ \ S) + degreeInto G v S = G.degree v := by
  simpa using degreeInto_sdiff_add_inter G v Finset.univ S

theorem degreeInto_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (S : Finset V) :
    degreeInto G v S = ∑ w ∈ S, if G.Adj v w then 1 else 0 := by
  have heq : G.neighborFinset v ∩ S = S.filter fun w ↦ G.Adj v w := by
    ext w
    simp [and_comm]
  rw [degreeInto, heq]
  simpa using (Finset.sum_boole (fun w ↦ G.Adj v w) S).symm

/-- Degree in an induced graph is degree into the finite inducing set. -/
theorem degree_induce_eq_degreeInto_toFinset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [Fintype S] (v : S) :
    (G.induce S).degree v = degreeInto G v S.toFinset := by
  calc
    (G.induce S).degree v = ((G.induce S).neighborFinset v).card :=
      ((G.induce S).card_neighborFinset_eq_degree v).symm
    _ = (((G.induce S).neighborFinset v).map
        (.subtype (· ∈ S))).card := (Finset.card_map _).symm
    _ = (G.neighborFinset v ∩ S.toFinset).card := by
      congr 1
      ext w
      simp
    _ = degreeInto G v S.toFinset := rfl

/-- Finset-specialized form of `degree_induce_eq_degreeInto_toFinset`. -/
theorem degree_induce_eq_degreeInto (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : S) :
    (G.induce (S : Set V)).degree v = degreeInto G v S := by
  simpa only [Finset.toFinset_coe] using
    degree_induce_eq_degreeInto_toFinset G (S : Set V) v

/-- Double-counting ordered adjacent pairs in two vertex sets. -/
theorem sum_degreeInto_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) :
    ∑ v ∈ S, degreeInto G v T = ∑ w ∈ T, degreeInto G w S := by
  simp_rw [degreeInto_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro v hv
  simp only [G.adj_comm]

/-- Unordered edges having both endpoints in `S`. -/
def edgesInside (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S

theorem card_edgesInside (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    (edgesInside G S).card = (G.induce (S : Set V)).edgeFinset.card := by
  simpa [edgesInside] using G.card_filter_edgeFinset_toFinset_subset S

@[simp]
theorem edgesInside_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgesInside G ∅ = ∅ := by
  ext e
  simp [edgesInside]

@[simp]
theorem edgesInside_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgesInside G Finset.univ = G.edgeFinset := by
  ext e
  simp [edgesInside]

theorem edgesInside_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : S ⊆ T) :
    edgesInside G S ⊆ edgesInside G T := by
  intro e he
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2.trans hST⟩

theorem edgesInside_mono_graph {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (S : Finset V) :
    edgesInside G S ⊆ edgesInside H S := by
  intro e he
  have heG := (Finset.mem_filter.mp he).1
  have heH : e ∈ H.edgeFinset := by
    exact SimpleGraph.edgeFinset_mono hGH heG
  exact Finset.mem_filter.mpr ⟨heH, (Finset.mem_filter.mp he).2⟩

/-- The handshaking identity restricted to an inducing set. -/
theorem sum_degreeInto_self (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    ∑ v ∈ S, degreeInto G v S = 2 * (edgesInside G S).card := by
  classical
  let K : SimpleGraph V := (G.induce (S : Set V)).spanningCoe
  let : DecidableRel K.Adj := Classical.decRel _
  have hneighbor (v : V) : K.neighborFinset v =
      if v ∈ S then G.neighborFinset v ∩ S else ∅ := by
    ext w
    by_cases hv : v ∈ S <;> simp [K, hv]
  have hdegree (v : V) : K.degree v =
      if v ∈ S then degreeInto G v S else 0 := by
    rw [← K.card_neighborFinset_eq_degree, hneighbor]
    by_cases hv : v ∈ S <;> simp [hv, degreeInto]
  have hedge : K.edgeFinset = edgesInside G S := by
    ext e
    obtain ⟨x, y⟩ := e
    simp [K, edgesInside, Sym2.toFinset_mk_eq, Finset.insert_subset_iff]
  have hsum : (∑ v : V, K.degree v) = ∑ v ∈ S, degreeInto G v S := by
    calc
      _ = ∑ v : V, if v ∈ S then degreeInto G v S else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hdegree v
      _ = _ := by
        rw [← Finset.sum_filter]
        simp
  calc
    _ = ∑ v : V, K.degree v := hsum.symm
    _ = 2 * K.edgeFinset.card := K.sum_degrees_eq_twice_card_edges
    _ = 2 * (edgesInside G S).card := by rw [hedge]

/-- Number of ordered adjacent pairs from `S` to `T`. -/
def edgesAcross (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) : ℕ :=
  (G.interedges S T).card

@[simp]
theorem edgesAcross_empty_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Finset V) : edgesAcross G ∅ T = 0 := by
  simp [edgesAcross]

@[simp]
theorem edgesAcross_empty_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : edgesAcross G S ∅ = 0 := by
  simp [edgesAcross, SimpleGraph.interedges_def]

theorem edgesAcross_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) :
    edgesAcross G S T = edgesAcross G T S := by
  unfold edgesAcross
  refine Finset.card_bij (fun (x : V × V) _ ↦ x.swap) ?_ ?_ ?_
  · intro x hx
    simpa using hx
  · intro a ha b hb hab
    exact Prod.swap_injective hab
  · intro y hy
    exact ⟨y.swap, by simpa using hy, y.swap_swap⟩

theorem edgesAcross_eq_sum_degreeInto (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) :
    edgesAcross G S T = ∑ v ∈ S, degreeInto G v T := by
  rw [edgesAcross]
  calc
    (G.interedges S T).card =
        ∑ e ∈ S ×ˢ T, if G.Adj e.1 e.2 then 1 else 0 := by
      simpa [SimpleGraph.interedges_def] using
        (Finset.sum_boole (fun e : V × V ↦ G.Adj e.1 e.2) (S ×ˢ T)).symm
    _ = ∑ v ∈ S, ∑ w ∈ T, if G.Adj v w then 1 else 0 := by
      rw [Finset.sum_product]
    _ = ∑ v ∈ S, degreeInto G v T := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [degreeInto_eq_sum]

theorem edgesAcross_le_card_mul_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) :
    edgesAcross G S T ≤ S.card * T.card := by
  exact G.card_interedges_le_mul S T

theorem edgesAcross_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {S S' T T' : Finset V} (hS : S ⊆ S') (hT : T ⊆ T') :
    edgesAcross G S T ≤ edgesAcross G S' T' := by
  exact Finset.card_le_card (G.interedges_mono hS hT)

theorem edgesAcross_union_left (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : Disjoint S T) (U : Finset V) :
    edgesAcross G (S ∪ T) U = edgesAcross G S U + edgesAcross G T U := by
  rw [edgesAcross_eq_sum_degreeInto, Finset.sum_union hST,
    ← edgesAcross_eq_sum_degreeInto, ← edgesAcross_eq_sum_degreeInto]

theorem edgesAcross_union_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {T U : Finset V} (hTU : Disjoint T U) :
    edgesAcross G S (T ∪ U) = edgesAcross G S T + edgesAcross G S U := by
  rw [edgesAcross_comm G S, edgesAcross_union_left G hTU,
    edgesAcross_comm G T, edgesAcross_comm G U]

theorem edgesAcross_sdiff_add_inter_right
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T U : Finset V) :
    edgesAcross G S (T \ U) + edgesAcross G S (T ∩ U) = edgesAcross G S T := by
  rw [← edgesAcross_union_right G S (Finset.disjoint_sdiff_inter T U)]
  congr 2
  ext v
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  tauto

theorem edgesAcross_sdiff_add_inter_left
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T U : Finset V) :
    edgesAcross G (S \ U) T + edgesAcross G (S ∩ U) T = edgesAcross G S T := by
  simpa only [edgesAcross_comm G] using edgesAcross_sdiff_add_inter_right G T S U

theorem edgesAcross_compl_add_right
    (G : SimpleGraph V) [DecidableRel G.Adj] (S T : Finset V) :
    edgesAcross G S (Finset.univ \ T) + edgesAcross G S T =
      ∑ v ∈ S, G.degree v := by
  rw [edgesAcross_eq_sum_degreeInto, edgesAcross_eq_sum_degreeInto,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  exact degreeInto_compl_add G v T

theorem edgesAcross_self (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) :
    edgesAcross G S S = 2 * (edgesInside G S).card := by
  rw [edgesAcross_eq_sum_degreeInto, sum_degreeInto_self]

/-- Across a disjoint pair, graph and complement edge counts fill the rectangle. -/
theorem edgesAcross_add_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : Disjoint S T) :
    edgesAcross G S T + edgesAcross Gᶜ S T = S.card * T.card := by
  exact G.card_interedges_add_card_interedges_compl hST

/-- Sum of all degrees on one side of a vertex partition. -/
theorem sum_degrees_eq_twice_inside_add_across
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : Disjoint S T) (hcover : S ∪ T = Finset.univ) :
    ∑ v ∈ S, G.degree v =
      2 * (edgesInside G S).card + edgesAcross G S T := by
  have hvertex (v : V) :
      G.degree v = degreeInto G v S + degreeInto G v T := by
    rw [← degreeInto_union_of_disjoint G v hST, hcover, degreeInto_univ]
  calc
    ∑ v ∈ S, G.degree v =
        ∑ v ∈ S, (degreeInto G v S + degreeInto G v T) := by
          apply Finset.sum_congr rfl
          intro v hv
          exact hvertex v
    _ = (∑ v ∈ S, degreeInto G v S) + ∑ v ∈ S, degreeInto G v T := by
          rw [Finset.sum_add_distrib]
    _ = 2 * (edgesInside G S).card + edgesAcross G S T := by
          rw [sum_degreeInto_self, edgesAcross_eq_sum_degreeInto]

/-- Every edge of a graph lies either inside one side of a partition or across it. -/
theorem card_edges_partition
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S T : Finset V} (hST : Disjoint S T) (hcover : S ∪ T = Finset.univ) :
    G.edgeFinset.card =
      (edgesInside G S).card + edgesAcross G S T + (edgesInside G T).card := by
  have hsumS := sum_degrees_eq_twice_inside_add_across G hST hcover
  have hsumT := sum_degrees_eq_twice_inside_add_across G hST.symm
    (by simpa [Finset.union_comm] using hcover)
  have htotal :
      (∑ v ∈ S, G.degree v) + ∑ v ∈ T, G.degree v =
        ∑ v : V, G.degree v := by
    rw [← Finset.sum_union hST, hcover]
  rw [hsumS, hsumT, edgesAcross_comm G T S,
    G.sum_degrees_eq_twice_card_edges] at htotal
  omega

/-- In a regular graph, internal and crossing degrees add to the common degree. -/
theorem regular_degreeInto_add {G : SimpleGraph V} [DecidableRel G.Adj]
    {d : ℕ} (hreg : G.IsRegularOfDegree d)
    {S T : Finset V} (hST : Disjoint S T) (hcover : S ∪ T = Finset.univ)
    (v : V) :
    degreeInto G v S + degreeInto G v T = d := by
  rw [← degreeInto_union_of_disjoint G v hST, hcover, degreeInto_univ,
    hreg.degree_eq]

end Erdos622.EdgeCounting
