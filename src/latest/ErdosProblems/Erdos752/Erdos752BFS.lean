/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import ErdosProblems.Erdos594

/-!
# Breadth-first-layer helpers for Erdős Problem 752

This file isolates the finite counting and path-closing facts used when a
finite bipartite graph is decomposed into consecutive breadth-first layers.
-/

open Finset Function Set SimpleGraph

namespace Erdos752

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u}

/-- The vertices at distance `i` from `root`. -/
abbrev bfsLayer (G : SimpleGraph V) (root : V) (i : ℕ) : Set V :=
  Erdos594.layer G root i

@[simp]
lemma mem_bfsLayer {G : SimpleGraph V} {root v : V} {i : ℕ} :
    v ∈ bfsLayer G root i ↔ G.dist root v = i :=
  Iff.rfl

/-- Distinct breadth-first layers are disjoint. -/
lemma bfsLayer_disjoint {G : SimpleGraph V} {root : V} {i j : ℕ} (hij : i ≠ j) :
    Disjoint (bfsLayer G root i) (bfsLayer G root j) := by
  rw [Set.disjoint_left]
  intro v hvi hvj
  exact hij (hvi.symm.trans hvj)

/-- In a bipartite connected graph, adjacent vertices cannot have the same
distance from a fixed root. -/
lemma not_adj_of_dist_eq_of_isBipartite {G : SimpleGraph V}
    (hconn : G.Connected) (hbip : G.IsBipartite) {root u v : V}
    (hdist : G.dist root u = G.dist root v) : ¬G.Adj u v := by
  classical
  let cFin : G.Coloring (Fin 2) := Classical.choice hbip
  let c : G.Coloring Bool := G.recolorOfEquiv finTwoEquiv cFin
  obtain ⟨p, _hp, hp_len⟩ := hconn.exists_path_of_dist root u
  obtain ⟨q, _hq, hq_len⟩ := hconn.exists_path_of_dist root v
  have hparity : Even p.length ↔ Even q.length := by
    rw [hp_len, hq_len, hdist]
  have hcongr : (c root ↔ c u) ↔ (c root ↔ c v) := by
    rw [← c.even_length_iff_congr p, ← c.even_length_iff_congr q]
    exact hparity
  have hcolor : c u = c v := by
    apply Bool.eq_iff_iff.mpr
    tauto
  intro huv
  exact c.valid huv hcolor

/-- An edge of a connected bipartite graph joins consecutive BFS layers. -/
lemma adj_dist_eq_succ_or_eq_succ {G : SimpleGraph V}
    (hconn : G.Connected) (hbip : G.IsBipartite) {root u v : V}
    (huv : G.Adj u v) :
    G.dist root u + 1 = G.dist root v ∨
      G.dist root v + 1 = G.dist root u := by
  have hne : G.dist root u ≠ G.dist root v := by
    intro h
    exact not_adj_of_dist_eq_of_isBipartite hconn hbip h huv
  rcases huv.diff_dist_adj (u := root) with h | h | h
  · exact (hne h.symm).elim
  · exact Or.inl h.symm
  · have hpos : 0 < G.dist root u := by
      by_contra hn
      have hu0 : G.dist root u = 0 := Nat.eq_zero_of_not_pos hn
      have hv0 : G.dist root v = 0 := by omega
      exact hne (hu0.trans hv0.symm)
    right
    omega

/-- The graph formed by the edges between BFS layers `i` and `i+1`. -/
abbrev bfsPair (G : SimpleGraph V) (root : V) (i : ℕ) : SimpleGraph V :=
  G.between (bfsLayer G root i) (bfsLayer G root (i + 1))

/-- Every non-isolated vertex of a two-layer slice belongs to one of its two
defining layers. -/
lemma bfsPair_support_subset {G : SimpleGraph V} {root : V} {i : ℕ} :
    (bfsPair G root i).support ⊆
      bfsLayer G root i ∪ bfsLayer G root (i + 1) := by
  intro v hv
  obtain ⟨w, hvw⟩ := (bfsPair G root i).mem_support.mp hv
  rcases hvw.2 with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Cardinality bound for the support of a two-layer slice. -/
lemma ncard_bfsPair_support_le [Fintype V] {G : SimpleGraph V}
    {root : V} {i : ℕ} :
    (bfsPair G root i).support.ncard ≤
      (bfsLayer G root i).ncard + (bfsLayer G root (i + 1)).ncard := by
  refine (Set.ncard_le_ncard bfsPair_support_subset).trans ?_
  exact Set.ncard_union_le _ _

/-- For a vertex in layer `i+1`, its neighbors are exactly the union of its
neighbors in the preceding and following two-layer slices. -/
lemma neighborFinset_eq_bfsPair_union [Fintype V] {G : SimpleGraph V}
    [decG : DecidableRel G.Adj]
    (hconn : G.Connected) (hbip : G.IsBipartite) {root v : V} {i : ℕ}
    (hv : G.dist root v = i + 1) :
    G.neighborFinset v =
      (bfsPair G root i).neighborFinset v ∪
        (bfsPair G root (i + 1)).neighborFinset v := by
  classical
  letI : DecidableRel G.Adj := decG
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union]
  constructor
  · intro hvw
    rcases adj_dist_eq_succ_or_eq_succ hconn hbip (root := root) hvw with h | h
    · right
      rw [SimpleGraph.between_adj]
      refine ⟨hvw, Or.inl ⟨hv, ?_⟩⟩
      change G.dist root w = i + 1 + 1
      omega
    · left
      rw [SimpleGraph.between_adj]
      refine ⟨hvw, Or.inr ⟨hv, ?_⟩⟩
      change G.dist root w = i
      omega
  · rintro (h | h)
    · exact h.1
    · exact h.1

/-- The preceding and following slices give disjoint neighbor sets at a
vertex in their common layer. -/
lemma disjoint_neighborFinset_bfsPair [Fintype V] {G : SimpleGraph V}
    [decG : DecidableRel G.Adj]
    {root v : V} {i : ℕ} (hv : G.dist root v = i + 1) :
    Disjoint ((bfsPair G root i).neighborFinset v)
      ((bfsPair G root (i + 1)).neighborFinset v) := by
  classical
  letI : DecidableRel G.Adj := decG
  rw [Finset.disjoint_left]
  intro w hw₀ hw₁
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj] at hw₀ hw₁
  rcases hw₀.2 with h₀ | h₀ <;> rcases hw₁.2 with h₁ | h₁ <;>
    simp only [mem_bfsLayer] at h₀ h₁
  all_goals omega

/-- Degree splitting at a vertex in the common layer of two consecutive
two-layer slices. -/
lemma degree_eq_bfsPair_add [Fintype V] {G : SimpleGraph V}
    [decG : DecidableRel G.Adj]
    (hconn : G.Connected) (hbip : G.IsBipartite) {root v : V} {i : ℕ}
    (hv : G.dist root v = i + 1) :
    G.degree v = (bfsPair G root i).degree v +
      (bfsPair G root (i + 1)).degree v := by
  classical
  letI : DecidableRel G.Adj := decG
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_eq_bfsPair_union hconn hbip hv,
    Finset.card_union_of_disjoint (disjoint_neighborFinset_bfsPair hv)]
  rfl

/-- Summing degrees over a non-root BFS layer counts the edges in the two
adjacent two-layer slices. -/
lemma sum_degrees_bfsLayer_succ_eq [Fintype V] {G : SimpleGraph V}
    [decG : DecidableRel G.Adj] (hconn : G.Connected) (hbip : G.IsBipartite)
    (root : V) (i : ℕ) :
    ∑ v ∈ bfsLayer G root (i + 1), G.degree v =
      #(bfsPair G root i).edgeFinset +
        #(bfsPair G root (i + 1)).edgeFinset := by
  classical
  letI : DecidableRel G.Adj := decG
  have hprev : (bfsPair G root i).IsBipartiteWith
      (bfsLayer G root i) (bfsLayer G root (i + 1)) :=
    SimpleGraph.between_isBipartiteWith (bfsLayer_disjoint (by omega))
  have hnext : (bfsPair G root (i + 1)).IsBipartiteWith
      (bfsLayer G root (i + 1)) (bfsLayer G root (i + 1 + 1)) :=
    SimpleGraph.between_isBipartiteWith (bfsLayer_disjoint (by omega))
  have hprev' : (bfsPair G root i).IsBipartiteWith
      (bfsLayer G root i).toFinset (bfsLayer G root (i + 1)).toFinset := by
    simpa using hprev
  have hnext' : (bfsPair G root (i + 1)).IsBipartiteWith
      (bfsLayer G root (i + 1)).toFinset
      (bfsLayer G root (i + 1 + 1)).toFinset := by
    simpa using hnext
  calc
    ∑ v ∈ bfsLayer G root (i + 1), G.degree v =
        ∑ v ∈ bfsLayer G root (i + 1),
          ((bfsPair G root i).degree v +
            (bfsPair G root (i + 1)).degree v) := by
              apply Finset.sum_congr rfl
              intro v hv
              exact degree_eq_bfsPair_add hconn hbip
                (by simpa using (Set.mem_toFinset.mp hv))
    _ = (∑ v ∈ bfsLayer G root (i + 1), (bfsPair G root i).degree v) +
        ∑ v ∈ bfsLayer G root (i + 1),
          (bfsPair G root (i + 1)).degree v := by
          rw [Finset.sum_add_distrib]
    _ = #(bfsPair G root i).edgeFinset +
        #(bfsPair G root (i + 1)).edgeFinset := by
          rw [SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hprev',
            SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hnext']

/-- In a connected graph the zeroth BFS layer is the singleton root. -/
lemma bfsLayer_zero_eq {G : SimpleGraph V} (hconn : G.Connected) (root : V) :
    bfsLayer G root 0 = {root} := by
  ext v
  simp only [mem_bfsLayer, Set.mem_singleton_iff]
  simpa [eq_comm] using (hconn.dist_eq_zero_iff (u := root) (v := v))

/-- All edges incident with the root belong to the first two-layer slice. -/
lemma degree_root_eq_bfsPair_zero [Fintype V] {G : SimpleGraph V}
    [decG : DecidableRel G.Adj]
    (root : V) : G.degree root = (bfsPair G root 0).degree root := by
  classical
  letI : DecidableRel G.Adj := decG
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext w
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.between_adj,
    mem_bfsLayer]
  constructor
  · intro hrw
    refine ⟨hrw, Or.inl ⟨by simp, ?_⟩⟩
    simpa using SimpleGraph.dist_eq_one_iff_adj.mpr hrw
  · rintro ⟨hrw, _⟩
    exact hrw

/-- Summing degrees over the root layer counts the first slice. -/
lemma sum_degrees_bfsLayer_zero_eq [Fintype V] {G : SimpleGraph V}
    [decG : DecidableRel G.Adj] (hconn : G.Connected) (root : V) :
    ∑ v ∈ bfsLayer G root 0, G.degree v =
      #(bfsPair G root 0).edgeFinset := by
  classical
  letI : DecidableRel G.Adj := decG
  have hpair : (bfsPair G root 0).IsBipartiteWith
      (bfsLayer G root 0) (bfsLayer G root 1) :=
    SimpleGraph.between_isBipartiteWith (bfsLayer_disjoint (by omega))
  have hpair' : (bfsPair G root 0).IsBipartiteWith
      (bfsLayer G root 0).toFinset (bfsLayer G root 1).toFinset := by
    simpa using hpair
  have hzeroFin : (bfsLayer G root 0).toFinset = {root} := by
    ext v
    simpa [bfsLayer_zero_eq hconn]
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hpair'
  calc
    ∑ v ∈ bfsLayer G root 0, G.degree v = G.degree root := by
      rw [hzeroFin]
      simp
    _ = (bfsPair G root 0).degree root := degree_root_eq_bfsPair_zero root
    _ = #(bfsPair G root 0).edgeFinset := by
      rw [hzeroFin] at hsum
      simpa using hsum

/-- A finite graph has a BFS layer of maximum cardinality.  The formulation
quantifies over all natural indices, including the empty layers above the
diameter. -/
lemma exists_max_ncard_bfsLayer [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (root : V) :
    ∃ i : ℕ, 0 < (bfsLayer G root i).ncard ∧
      ∀ j : ℕ, (bfsLayer G root j).ncard ≤
        (bfsLayer G root i).ncard := by
  classical
  obtain ⟨v, _hv, hmax⟩ := Finset.univ.exists_max_image
    (fun w : V ↦ (bfsLayer G root (G.dist root w)).ncard)
    Finset.univ_nonempty
  refine ⟨G.dist root v, ?_, ?_⟩
  · exact (show (bfsLayer G root (G.dist root v)).Nonempty from ⟨v, rfl⟩).ncard_pos
  · intro j
    by_cases hj : (bfsLayer G root j).Nonempty
    · obtain ⟨w, hw⟩ := hj
      have hwmax := hmax w (Finset.mem_univ w)
      have hwdist : G.dist root w = j := hw
      rw [hwdist] at hwmax
      exact hwmax
    · have hempty : bfsLayer G root j = ∅ := Set.not_nonempty_iff_eq_empty.mp hj
      simp [hempty]

private lemma mul_ncard_le_sum_of_forall [Fintype V]
    (s : Set V) (f : V → ℕ) (c : ℕ)
    (h : ∀ v ∈ s, c ≤ f v) :
    c * s.ncard ≤ ∑ v ∈ s, f v := by
  classical
  calc
    c * s.ncard = ∑ _v ∈ s, c := by
      rw [Set.ncard_eq_toFinset_card']
      simp [mul_comm]
    _ ≤ ∑ v ∈ s, f v := by
      apply Finset.sum_le_sum
      intro v hv
      exact h v (Set.mem_toFinset.mp hv)

/-- A connected finite bipartite graph of minimum degree at least `2*d` has
a consecutive pair of BFS layers whose crossing graph has average degree at
least `d`.  The vertex count is the support of the crossing graph, so isolated
vertices in the two ambient layers cause no loss. -/
theorem exists_dense_bfs_pair [Fintype V] [Nonempty V] {G : SimpleGraph V}
    [decG : DecidableRel G.Adj] (hconn : G.Connected) (hbip : G.IsBipartite)
    (d : ℕ) (hd : 0 < d) (hmin : ∀ v : V, 2 * d ≤ G.degree v) (root : V) :
    ∃ i : ℕ, (bfsPair G root i).edgeFinset.Nonempty ∧
      d * (bfsPair G root i).support.ncard ≤
        2 * #(bfsPair G root i).edgeFinset := by
  classical
  letI : DecidableRel G.Adj := decG
  obtain ⟨i, hi_pos, hi_max⟩ := exists_max_ncard_bfsLayer G root
  let M := (bfsLayer G root i).ncard
  have hM : M = (bfsLayer G root i).ncard := rfl
  have hM_pos : 0 < M := by simpa [M] using hi_pos
  have hT_pos : 0 < d * M := Nat.mul_pos hd hM_pos
  cases i with
  | zero =>
      have hsupport : (bfsPair G root 0).support.ncard ≤ 2 * M := by
        calc
          (bfsPair G root 0).support.ncard ≤
              (bfsLayer G root 0).ncard +
                (bfsLayer G root 1).ncard := ncard_bfsPair_support_le
          _ ≤ M + M := Nat.add_le_add (hi_max 0) (hi_max 1)
          _ = 2 * M := by omega
      have hsum : 2 * (d * M) ≤ #(bfsPair G root 0).edgeFinset := by
        calc
          2 * (d * M) = 2 * d * M := by ring
          _ ≤ #(bfsPair G root 0).edgeFinset := by
            rw [← sum_degrees_bfsLayer_zero_eq hconn root]
            exact mul_ncard_le_sum_of_forall _ _ (2 * d)
              (fun v _hv ↦ hmin v)
      have hedgePos : 0 < #(bfsPair G root 0).edgeFinset := by omega
      refine ⟨0, Finset.card_pos.mp hedgePos, ?_⟩
      calc
        d * (bfsPair G root 0).support.ncard ≤ d * (2 * M) :=
          Nat.mul_le_mul_left d hsupport
        _ = 2 * (d * M) := by ring
        _ ≤ #(bfsPair G root 0).edgeFinset := hsum
        _ ≤ 2 * #(bfsPair G root 0).edgeFinset := by omega
  | succ i =>
      let B₀ := bfsPair G root i
      let B₁ := bfsPair G root (i + 1)
      have hs₀ : B₀.support.ncard ≤ 2 * M := by
        calc
          B₀.support.ncard ≤ (bfsLayer G root i).ncard +
              (bfsLayer G root (i + 1)).ncard := ncard_bfsPair_support_le
          _ ≤ M + M := Nat.add_le_add (hi_max i) (hi_max (i + 1))
          _ = 2 * M := by omega
      have hs₁ : B₁.support.ncard ≤ 2 * M := by
        calc
          B₁.support.ncard ≤ (bfsLayer G root (i + 1)).ncard +
              (bfsLayer G root (i + 1 + 1)).ncard := ncard_bfsPair_support_le
          _ ≤ M + M := Nat.add_le_add (hi_max (i + 1)) (hi_max (i + 1 + 1))
          _ = 2 * M := by omega
      have hsum_lower : 2 * (d * M) ≤ #B₀.edgeFinset + #B₁.edgeFinset := by
        calc
          2 * (d * M) = 2 * d * M := by ring
          _ ≤ #B₀.edgeFinset + #B₁.edgeFinset := by
            rw [← sum_degrees_bfsLayer_succ_eq hconn hbip root i]
            exact mul_ncard_le_sum_of_forall _ _ (2 * d)
              (fun v _hv ↦ hmin v)
      by_cases h₀ : d * B₀.support.ncard ≤ 2 * #B₀.edgeFinset
      · by_cases he₀ : B₀.edgeFinset.Nonempty
        · exact ⟨i, he₀, h₀⟩
        · have he₀zero : #B₀.edgeFinset = 0 := by
            rw [Finset.not_nonempty_iff_eq_empty] at he₀
            simp [he₀]
          have he₁pos : 0 < #B₁.edgeFinset := by omega
          refine ⟨i + 1, Finset.card_pos.mp he₁pos, ?_⟩
          calc
            d * B₁.support.ncard ≤ d * (2 * M) := Nat.mul_le_mul_left d hs₁
            _ = 2 * (d * M) := by ring
            _ ≤ #B₀.edgeFinset + #B₁.edgeFinset := hsum_lower
            _ = #B₁.edgeFinset := by omega
            _ ≤ 2 * #B₁.edgeFinset := by omega
      have he₀ : #B₀.edgeFinset < d * M := by
        have hlt : 2 * #B₀.edgeFinset < d * B₀.support.ncard :=
          Nat.lt_of_not_ge h₀
        have : 2 * #B₀.edgeFinset < 2 * (d * M) :=
          lt_of_lt_of_le hlt (by
            calc
              d * B₀.support.ncard ≤ d * (2 * M) := Nat.mul_le_mul_left d hs₀
              _ = 2 * (d * M) := by ring)
        omega
      by_cases h₁ : d * B₁.support.ncard ≤ 2 * #B₁.edgeFinset
      · have he₁pos : 0 < #B₁.edgeFinset := by omega
        exact ⟨i + 1, Finset.card_pos.mp he₁pos, h₁⟩
      exfalso
      have he₁ : #B₁.edgeFinset < d * M := by
        have hlt : 2 * #B₁.edgeFinset < d * B₁.support.ncard :=
          Nat.lt_of_not_ge h₁
        have : 2 * #B₁.edgeFinset < 2 * (d * M) :=
          lt_of_lt_of_le hlt (by
            calc
              d * B₁.support.ncard ≤ d * (2 * M) := Nat.mul_le_mul_left d hs₁
              _ = 2 * (d * M) := by ring)
        omega
      omega

end

end Erdos752
