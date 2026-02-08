/-

This is a Lean formalization of a solution to Erdős Problem 618.
https://www.erdosproblems.com/forum/thread/618

The original proof was found by: Noga Alon

https://web.math.princeton.edu/~nalon/PDFS/remark1901.pdf


This paper was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formalized and proved Theorem 1.2 from the paper "Triangle-free graphs of diameter 2" by Noga Alon.
The main result `theorem_1_2` states that for a triangle-free graph $G$ on $n$ vertices with maximum degree at most $c\sqrt{n}$ (where $c$ satisfies certain bounds), there exists a supergraph $G'$ of $G$ which is triangle-free, has diameter 2, and has at most $2.5cn^2$ edges.
The proof follows the probabilistic argument using the triangle-free process, as outlined in the paper. We formalized the process, the invariant, the stopping condition, and the final deterministic reduction.
We also proved the necessary lemmas regarding the independence number and the existence of a valid path in the process.
-/

import Mathlib

open scoped Classical

/-
A graph G is maximal triangle-free if it is triangle-free and cannot be extended to a larger triangle-free graph on the same vertex set.
-/
def SimpleGraph.IsMaximalTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.CliqueFree 3 ∧ ∀ H : SimpleGraph V, G ≤ H → H.CliqueFree 3 → G = H

/-
A maximal triangle-free graph has diameter at most 2 (every pair of distinct vertices is either adjacent or shares a common neighbor).
-/
theorem SimpleGraph.maximal_triangle_free_diam_two {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (h : G.IsMaximalTriangleFree) :
  ∀ x y, x ≠ y → G.Adj x y ∨ ∃ z, G.Adj x z ∧ G.Adj z y := by
    -- Assume that there exist vertices $x$ and $y$ such that $x \neq y$ and $G$ does not have an edge between them.
    by_contra h_contra
    obtain ⟨x, y, hxy, h_no_edge⟩ : ∃ x y : V, x ≠ y ∧ ¬G.Adj x y ∧ ¬∃ z : V, G.Adj x z ∧ G.Adj z y := by
      grind;
    -- Consider the graph $H$ obtained by adding the edge $(x, y)$ to $G$.
    set H : SimpleGraph V := G ⊔ (SimpleGraph.mk fun u v => u ≠ v ∧ (u = x ∧ v = y ∨ u = y ∧ v = x)) with hH_def;
    -- We need to show that $H$ is triangle-free.
    have hH_triangle_free : H.CliqueFree 3 := by
      intro t ht; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      -- Since $t$ is a clique in $H$, it must be a clique in $G$ or contain the edge $(x, y)$.
      by_cases hxy_in_t : x ∈ t ∧ y ∈ t;
      · -- Since $t$ is a clique in $H$, it must contain a third vertex $z$ such that $z$ is adjacent to both $x$ and $y$ in $H$.
        obtain ⟨z, hz⟩ : ∃ z ∈ t, z ≠ x ∧ z ≠ y := by
          exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( Finset.erase t x ) from by rw [ Finset.card_erase_of_mem hxy_in_t.1, ht.2 ] ; decide ) y );
        have := ht.1 hz.1 hxy_in_t.1; have := ht.1 hz.1 hxy_in_t.2; simp_all +decide ;
        exact h_no_edge.2 ⟨ z, by tauto, by tauto ⟩;
      · -- Since $t$ is a clique in $H$ and does not contain the edge $(x, y)$, it must be a clique in $G$.
        have ht_clique_G : G.IsClique (t : Set V) := by
          intro u hu v hv huv; specialize ht; have := ht.1 hu hv; aesop;
        have := h.1 t; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
    -- Since $H$ is triangle-free and $G$ is maximal triangle-free, we must have $G = H$.
    have hG_eq_H : G = H := by
      exact h.2 H ( le_sup_left ) hH_triangle_free ▸ rfl;
    simp +zetaDelta at *;
    exact h_no_edge.1 ( hG_eq_H ( by aesop ) )

/-
If G is a subgraph of H, then the independence number of H is at most the independence number of G.
-/
theorem SimpleGraph.indepNum_le_of_le {V : Type*} [Fintype V] {G H : SimpleGraph V} (h : G ≤ H) :
  H.indepNum ≤ G.indepNum := by
    apply_rules [ csSup_le_csSup ];
    · exact ⟨ _, fun n hn => by rcases hn with ⟨ s, hs ⟩ ; exact le_trans ( hs.card_eq.symm.le ) ( Finset.card_le_univ _ ) ⟩;
    · exact ⟨ 0, ⟨ ∅, by simp +decide [ SimpleGraph.isNIndepSet_iff ] ⟩ ⟩;
    · rintro n ⟨ s, hs ⟩ ; use s; simp_all +decide [ SimpleGraph.isNIndepSet_iff ] ;
      intro x hx y hy hxy; have := hs.1 hx hy; aesop;

/-
Every triangle-free graph G can be extended to a maximal triangle-free graph H, and the independence number of H is at most that of G.
-/
theorem SimpleGraph.exists_maximal_triangle_free_extension {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (h : G.CliqueFree 3) :
  ∃ H : SimpleGraph V, G ≤ H ∧ H.IsMaximalTriangleFree ∧ H.indepNum ≤ G.indepNum := by
    -- By definition of maximal triangle-free graphs, there exists a maximal triangle-free graph $H$ such that $G \leq H$.
    obtain ⟨H, hH⟩ : ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧ ∀ K : SimpleGraph V, H ≤ K → K.CliqueFree 3 → H = K := by
      have h_maximal : ∃ H ∈ {H : SimpleGraph V | G ≤ H ∧ H.CliqueFree 3}, ∀ K ∈ {H : SimpleGraph V | G ≤ H ∧ H.CliqueFree 3}, H ≤ K → H = K := by
        have h_finite : Set.Finite {H : SimpleGraph V | G ≤ H ∧ H.CliqueFree 3} := by
          exact Set.toFinite _
        have := h_finite.toFinset.exists_maximal;
        obtain ⟨ H, hH ⟩ := this ⟨ G, h_finite.mem_toFinset.mpr ⟨ le_rfl, h ⟩ ⟩;
        exact ⟨ H, by simpa using hH.1, fun K hK hHK => hH.eq_of_le ( by simpa using hK ) hHK ⟩;
      exact ⟨ h_maximal.choose, h_maximal.choose_spec.1.1, h_maximal.choose_spec.1.2, fun K hK₁ hK₂ => h_maximal.choose_spec.2 K ⟨ h_maximal.choose_spec.1.1.trans hK₁, hK₂ ⟩ hK₁ ⟩;
    refine' ⟨ H, hH.1, ⟨ hH.2.1, hH.2.2 ⟩, _ ⟩;
    apply SimpleGraph.indepNum_le_of_le; exact hH.left;

/-
In a triangle-free graph, the maximum degree is at most the independence number.
-/
theorem SimpleGraph.maxDegree_le_indepNum {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (h : G.CliqueFree 3) :
  G.maxDegree ≤ G.indepNum := by
    -- By definition of maximal triangle-free graph, there exists a maximal triangle-free graph $H$ such that $G \leq H$.
    obtain ⟨H, hH⟩ : ∃ H : SimpleGraph V, G ≤ H ∧ H.IsMaximalTriangleFree ∧ H.indepNum ≤ G.indepNum := by
      exact exists_maximal_triangle_free_extension G h;
    -- By definition of maximal triangle-free graph, the maximum degree of H is at most the independence number of H.
    have hH_max_deg : H.maxDegree ≤ H.indepNum := by
      -- Since H is maximal triangle-free, for any vertex v, the set of its neighbors forms an independent set.
      have hH_neighbor_indep : ∀ v : V, H.Adj v ≠ ⊥ → (H.neighborFinset v).card ≤ H.indepNum := by
        intros v hv
        have h_neighbor_indep : ∀ u w : V, u ≠ w → u ∈ H.neighborFinset v → w ∈ H.neighborFinset v → ¬H.Adj u w := by
          have := hH.2.1.1;
          intro u w hne hu hw h; have := this { u, w, v } ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
          simp_all +decide [ SimpleGraph.adj_comm ];
          rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] at this <;> simp_all +decide;
          · aesop;
          · aesop_cat;
        -- Since the set of neighbors of v is an independent set, its cardinality is at most the independence number of H.
        have h_neighbor_indep_set : H.IsIndepSet (H.neighborFinset v) := by
          exact fun u hu w hw huv => h_neighbor_indep u w huv hu hw;
        exact IsIndepSet.card_le_indepNum h_neighbor_indep_set;
      -- Since H is maximal triangle-free, for any vertex v, the degree of v is at most the independence number of H.
      have hH_degree_le_indep : ∀ v : V, H.degree v ≤ H.indepNum := by
        intro v; specialize hH_neighbor_indep v; by_cases hv : H.Adj v = ⊥ <;> simp_all +decide ;
        simp_all +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset ];
      exact maxDegree_le_of_forall_degree_le H H.indepNum hH_degree_le_indep;
    refine' le_trans _ ( hH_max_deg.trans hH.2.2 );
    have := @SimpleGraph.degree_le_of_le V;
    simp_all +decide [ SimpleGraph.maxDegree ];
    have h_max_deg_le : ∀ v : V, G.degree v ≤ H.degree v := by
      exact fun v => this hH.1;
    have h_max_deg_le : Finset.max (Finset.image (fun v => G.degree v) Finset.univ) ≤ Finset.max (Finset.image (fun v => H.degree v) Finset.univ) := by
      simp +decide [ Finset.max ];
      exact fun v => ⟨ v, h_max_deg_le v ⟩;
    cases h : Finset.max ( Finset.image ( fun v => G.degree v ) Finset.univ ) <;> cases h' : Finset.max ( Finset.image ( fun v => H.degree v ) Finset.univ ) <;> aesop

/-
If there exists a triangle-free supergraph Gm of G with independence number at most 5cn, then there exists a triangle-free supergraph G' of G with diameter 2 and at most 2.5cn^2 edges.
-/
theorem SimpleGraph.deterministic_reduction {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (n : ℕ) (c : ℝ) (h_n : Fintype.card V = n)
  (h_exists : ∃ G_m : SimpleGraph V, G ≤ G_m ∧ G_m.CliqueFree 3 ∧ (G_m.indepNum : ℝ) ≤ 5 * c * n) :
  ∃ G' : SimpleGraph V, G ≤ G' ∧ G'.CliqueFree 3 ∧
    (∀ x y : V, x ≠ y → G'.Adj x y ∨ ∃ z, G'.Adj x z ∧ G'.Adj z y) ∧
    (G'.edgeFinset.card : ℝ) ≤ 2.5 * c * n ^ 2 := by
      -- By `exists_maximal_triangle_free_extension`, G_m has a maximal triangle-free extension G' which has diameter 2.
      obtain ⟨G_m, hG_m⟩ := h_exists
      obtain ⟨G', hG'_sup, hG'_max, hG'_indep⟩ := exists_maximal_triangle_free_extension G_m (by
      exact hG_m.2.1);
      refine' ⟨ G', le_trans hG_m.1 hG'_sup, _, _, _ ⟩;
      · exact hG'_max.1;
      · exact fun x y a => maximal_triangle_free_diam_two G' hG'_max x y a;
      · -- By `maxDegree_le_indepNum`, $\Delta(G') \le \alpha(G')$.
        have hG'_max_deg : G'.maxDegree ≤ G'.indepNum := by
          apply SimpleGraph.maxDegree_le_indepNum;
          exact hG'_max.1;
        -- The number of edges in $G'$ is $\frac{1}{2} \sum_{v} \deg(v) \le \frac{1}{2} n \Delta(G')$.
        have hG'_edges : (G'.edgeFinset.card : ℝ) ≤ (n * G'.maxDegree : ℝ) / 2 := by
          have := SimpleGraph.sum_degrees_eq_twice_card_edges G';
          rw [ le_div_iff₀ ] <;> norm_cast;
          rw [ mul_comm, ← h_n ];
          exact this ▸ le_trans ( Finset.sum_le_sum fun _ _ => G'.degree_le_maxDegree _ ) ( by simp +decide );
        nlinarith [ show ( G'.maxDegree : ℝ ) ≤ G'.indepNum by exact_mod_cast hG'_max_deg, show ( G'.indepNum : ℝ ) ≤ G_m.indepNum by exact_mod_cast hG'_indep ]

/-
Definitions of eligible pairs and symmetry lemma.
-/
def SimpleGraph.eligiblePair {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) (n : ℕ) (u v : V) : Prop :=
  u ≠ v ∧ ¬G.Adj u v ∧ (G.degree u : ℝ) < 2 * c * Real.sqrt n ∧ (G.degree v : ℝ) < 2 * c * Real.sqrt n ∧
  ∀ w, ¬(G.Adj u w ∧ G.Adj v w)

theorem SimpleGraph.eligiblePair_symm {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) (n : ℕ) (u v : V) :
  G.eligiblePair c n u v ↔ G.eligiblePair c n v u := by
    unfold SimpleGraph.eligiblePair;
    tauto

/-
The set of eligible edges as a Finset.
-/
noncomputable def SimpleGraph.eligibleFinset {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) (n : ℕ) : Finset (Sym2 V) :=
  let r := G.eligiblePair c n
  have h_sym : Symmetric r := fun x y h => (G.eligiblePair_symm c n x y).mp h
  have : DecidablePred (· ∈ Sym2.fromRel h_sym) := Classical.decPred _
  (Sym2.fromRel h_sym).toFinset

/-
Two vertices have a common neighbor if they are distinct and there exists a vertex adjacent to both. This relation is symmetric.
-/
def SimpleGraph.hasCommonNeighbor {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  u ≠ v ∧ ∃ w, G.Adj u w ∧ G.Adj v w

theorem SimpleGraph.hasCommonNeighbor_symm {V : Type*} (G : SimpleGraph V) (u v : V) :
  G.hasCommonNeighbor u v ↔ G.hasCommonNeighbor v u := by
    simp +decide only [SimpleGraph.hasCommonNeighbor];
    simp +contextual only [ne_comm, and_comm]

/-
The set of pairs of vertices that share a common neighbor.
-/
noncomputable def SimpleGraph.commonNeighborFinset {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset (Sym2 V) :=
  let r := G.hasCommonNeighbor
  have h_sym : Symmetric r := fun x y h => (G.hasCommonNeighbor_symm x y).mp h
  have : DecidablePred (· ∈ Sym2.fromRel h_sym) := Classical.decPred _
  (Sym2.fromRel h_sym).toFinset

/-
Definitions of eligible pairs in U and common neighbor pairs in U.
-/
noncomputable def SimpleGraph.eligiblePairsIn {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) (n : ℕ) (U : Finset V) : Finset (Sym2 V) :=
  (G.eligibleFinset c n) ∩ U.sym2

noncomputable def SimpleGraph.commonNeighborPairsIn {V : Type*} [Fintype V] (G : SimpleGraph V) (U : Finset V) : Finset (Sym2 V) :=
  (G.commonNeighborFinset) ∩ U.sym2

/-
Corrected helper lemma: The set of distinct pairs in U \ S that do not share a common neighbor is a subset of the eligible pairs in U.
-/
def SimpleGraph.distinctPairsIn {V : Type*} [Fintype V] [DecidableEq V] (U : Finset V) : Finset (Sym2 V) :=
  U.sym2.filter (fun e => ¬e.IsDiag)

theorem subset_eligible_pairs_corrected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (c : ℝ) (n : ℕ) (U : Finset V) (S : Finset V)
  (h_indep : G.IsIndepSet U)
  (h_S_deg : ∀ v ∈ U, v ∉ S → (G.degree v : ℝ) < 2 * c * Real.sqrt n) :
  (SimpleGraph.distinctPairsIn (U \ S)) \ (G.commonNeighborPairsIn U) ⊆ G.eligiblePairsIn c n U := by
    simp +decide [ Finset.subset_iff, SimpleGraph.distinctPairsIn ];
    rintro ⟨ u, v ⟩ h₁ h₂ h₃; simp_all +decide [ SimpleGraph.eligiblePairsIn, SimpleGraph.commonNeighborPairsIn ] ;
    simp_all +decide [ SimpleGraph.eligibleFinset, SimpleGraph.commonNeighborFinset ];
    refine' ⟨ h₂, _, _, _, _ ⟩;
    · exact h_indep h₁.1.1 h₁.2.1 h₂;
    · exact h_S_deg u h₁.1.1 h₁.1.2;
    · exact h_S_deg v h₁.2.1 h₁.2.2;
    · exact fun w hw => h₃ ⟨ h₂, w, hw ⟩

theorem subset_eligible_pairs {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (c : ℝ) (n : ℕ) (U : Finset V) (S : Finset V)
  (h_indep : G.IsIndepSet U)
  (h_S_deg : ∀ v ∈ U, v ∉ S → (G.degree v : ℝ) < 2 * c * Real.sqrt n) :
  (SimpleGraph.distinctPairsIn (U \ S)) \ (G.commonNeighborPairsIn U) ⊆ G.eligiblePairsIn c n U := by
    convert subset_eligible_pairs_corrected G c n U S h_indep h_S_deg using 1

/-
The number of pairs in U with a common neighbor is at most the sum over all vertices w of the number of pairs in U that are neighbors of w.
-/
theorem common_neighbor_bound {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
  (G.commonNeighborPairsIn U).card ≤ ∑ w : V, (G.neighborFinset w ∩ U).card.choose 2 := by
    -- Let $P$ be the set of pairs in $U$ with a common neighbor.
    set P := (G.commonNeighborPairsIn U);
    -- By definition of $P$, we know that every element in $P$ is a pair of vertices in $U$ that share a common neighbor.
    have hP_subset : P ⊆ Finset.biUnion (Finset.univ : Finset V) (fun w => Finset.image (fun p => Sym2.mk (p.1, p.2)) (Finset.offDiag (G.neighborFinset w ∩ U))) := by
      intro p hp
      obtain ⟨u, v, huv, hw⟩ : ∃ u v : V, u ≠ v ∧ u ∈ U ∧ v ∈ U ∧ ∃ w, G.Adj u w ∧ G.Adj v w ∧ p = Sym2.mk (u, v) := by
        have hP_subset : ∀ p ∈ P, ∃ u v : V, u ≠ v ∧ u ∈ U ∧ v ∈ U ∧ ∃ w, G.Adj u w ∧ G.Adj v w ∧ p = Sym2.mk (u, v) := by
          intro p hp
          simp [P, SimpleGraph.commonNeighborPairsIn] at hp;
          rcases p with ⟨ u, v ⟩;
          rcases hp with ⟨ hp₁, hp₂ ⟩;
          simp [SimpleGraph.commonNeighborFinset] at hp₁;
          rcases hp₁ with ⟨ w, hw₁, hw₂ ⟩ ; use u, v ; aesop;
        exact hP_subset p hp;
      obtain ⟨ w, hu, hv, rfl ⟩ := hw.2.2; simp +decide [ * ] ;
      exact ⟨ w, u, v, ⟨ ⟨ hu.symm, hw.1 ⟩, ⟨ hv.symm, hw.2.1 ⟩, huv ⟩, Or.inl ⟨ rfl, rfl ⟩ ⟩;
    refine' le_trans ( Finset.card_le_card hP_subset ) _;
    refine' le_trans ( Finset.card_biUnion_le ) ( Finset.sum_le_sum fun w _ => _ );
    -- The number of pairs in the off-diagonal of a set is given by the binomial coefficient.
    have h_off_diag_card : Finset.card (Finset.offDiag (G.neighborFinset w ∩ U)) = (G.neighborFinset w ∩ U).card * ((G.neighborFinset w ∩ U).card - 1) := by
      simp +decide [ mul_tsub, Finset.offDiag_card ];
    have h_image_card : Finset.card (Finset.image (fun p => Sym2.mk (p.1, p.2)) (Finset.offDiag (G.neighborFinset w ∩ U))) ≤ Finset.card (Finset.offDiag (G.neighborFinset w ∩ U)) / 2 := by
      have h_image_card : ∀ p ∈ Finset.offDiag (G.neighborFinset w ∩ U), Finset.card (Finset.filter (fun q => Sym2.mk (q.1, q.2) = Sym2.mk (p.1, p.2)) (Finset.offDiag (G.neighborFinset w ∩ U))) ≥ 2 := by
        intro p hp; refine' Finset.one_lt_card.mpr ⟨ p, _, ( p.2, p.1 ), _, _ ⟩ <;> aesop;
      have h_image_card : Finset.card (Finset.offDiag (G.neighborFinset w ∩ U)) = Finset.sum (Finset.image (fun p => Sym2.mk (p.1, p.2)) (Finset.offDiag (G.neighborFinset w ∩ U))) (fun p => Finset.card (Finset.filter (fun q => Sym2.mk (q.1, q.2) = p) (Finset.offDiag (G.neighborFinset w ∩ U)))) := by
        rw [ Finset.card_eq_sum_ones, Finset.sum_image' ] ; aesop;
      rw [ h_image_card, Nat.le_div_iff_mul_le zero_lt_two ];
      exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun x hx => show Finset.card ( Finset.filter ( fun q => s(q.1, q.2) = x ) ( Finset.offDiag ( G.neighborFinset w ∩ U ) ) ) ≥ 2 from by obtain ⟨ p, hp, rfl ⟩ := Finset.mem_image.mp hx; solve_by_elim );
    convert h_image_card using 1;
    rw [ h_off_diag_card, Nat.choose_two_right ]

/-
The cardinality of the set of distinct pairs in U is binomial(|U|, 2).
-/
theorem card_distinctPairsIn {V : Type*} [Fintype V] [DecidableEq V] (U : Finset V) :
  (SimpleGraph.distinctPairsIn U).card = U.card.choose 2 := by
    -- Let's simplify the goal using the definition of `distinctPairsIn`.
    unfold SimpleGraph.distinctPairsIn;
    convert Finset.card_powersetCard 2 U using 1;
    refine' Finset.card_bij ( fun e he => Finset.filter ( fun x => x ∈ e ) U ) _ _ _;
    · simp +contextual [ Finset.mem_powersetCard, Sym2.forall ];
      intro x y hx hy hxy; rw [ show { z ∈ U | z = x ∨ z = y } = { x, y } by ext; aesop ] ; rw [ Finset.card_insert_of_notMem, Finset.card_singleton ] ; aesop;
    · simp +contextual [ Finset.ext_iff, Sym2.forall ];
      intro x y hx hy hxy x' y' hx' hy' hxy' h; have := h x hx; have := h y hy; have := h x' hx'; have := h y' hy'; aesop;
    · simp +decide [ Finset.mem_powersetCard, Finset.subset_iff ];
      intro b hb hb'; obtain ⟨ x, y, hxy ⟩ := Finset.card_eq_two.mp hb'; use Sym2.mk ( x, y ) ; aesop;

/-
Lower bound for the first binomial term, with sufficient conditions on c.
-/
theorem numeric_inequality_part1 (n : ℕ) (c : ℝ)
  (h_n : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_lower : c * Real.sqrt n ≥ 2) :
  let k := Nat.floor (5 * c * n) - Nat.floor (2 * c * n)
  (k.choose 2 : ℝ) ≥ (3 * c * n - 1) * (3 * c * n - 2) / 2 := by
    have h_k_ge_x (k : ℕ) (hk_ge_x : (k : ℝ) ≥ 3 * c * n - 1) : (k.choose 2 : ℝ) ≥ (3 * c * n - 1) * (3 * c * n - 2) / 2 := by
      rcases k with ( _ | _ | k ) <;> norm_num [ Nat.choose_two_right ] at *;
      · nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ) ];
      · nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, show ( c : ℝ ) * Real.sqrt n ≥ 2 by assumption, Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ) ];
      · rw [ Nat.cast_div ] <;> norm_num;
        · nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, show ( 3 * c * n : ℝ ) ≥ 2 by nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ) ] ];
        · exact Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] );
    refine h_k_ge_x _ ?_;
    rw [ Nat.cast_sub ] <;> norm_num;
    · linarith [ Nat.lt_floor_add_one ( 5 * c * n ), Nat.floor_le ( show 0 ≤ 2 * c * n by positivity ) ];
    · exact Nat.floor_mono <| by nlinarith;

/-
Upper bound for the second binomial term.
-/
theorem numeric_inequality_part2 (n : ℕ) (c : ℝ) (h_n : n ≥ 1) (h_c_pos : c > 0) :
  (n : ℝ) * (Nat.ceil (2 * c * Real.sqrt n)).choose 2 ≤ 2 * c^2 * n^2 + c * n * Real.sqrt n := by
    -- Let $d = \lceil 2c\sqrt{n} \rceil$. We have $d \le 2c\sqrt{n} + 1$.
    set d := Nat.ceil (2 * c * Real.sqrt n)
    have hd : (d : ℝ) ≤ 2 * c * Real.sqrt n + 1 := by
      exact le_of_lt <| Nat.ceil_lt_add_one <| by positivity;
    -- We have $\binom{d}{2} = \frac{d(d-1)}{2} \le \frac{(2c\sqrt{n}+1)(2c\sqrt{n})}{2}$.
    have h_choose : (Nat.choose d 2 : ℝ) ≤ (2 * c * Real.sqrt n + 1) * (2 * c * Real.sqrt n) / 2 := by
      have h_choose : (Nat.choose d 2 : ℝ) ≤ (d * (d - 1)) / 2 := by
        exact Nat.recOn d ( by norm_num ) fun n ih => by cases n <;> norm_num [ Nat.choose ] at * ; linarith;
      exact h_choose.trans ( by nlinarith [ show ( d : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.ceil_pos.mpr ( by positivity ) ) ] );
    convert mul_le_mul_of_nonneg_left h_choose ( Nat.cast_nonneg n ) using 1 ; ring_nf;
    norm_num [ sq, mul_assoc ]

/-
Algebraic inequality for the final step.
-/
theorem numeric_inequality_final_step (n : ℕ) (c : ℝ)
  (h_n : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_lower : c * Real.sqrt n ≥ 4) :
  (3 * c * n - 1) * (3 * c * n - 2) / 2 - (2 * c^2 * n^2 + c * n * Real.sqrt n) ≥ 2 * c^2 * n^2 := by
    -- By dividing both sides of the inequality by $c n$, we get $c n \geq 2 \sqrt{n} + 9 - 2 / (c n)$.
    have h_div : c * n ≥ 2 * Real.sqrt n + 9 - 2 / (c * n) := by
      rw [ sub_div', ge_iff_le, div_le_iff₀ ] <;> try positivity;
      nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, show ( c * n : ℝ ) ≥ 4 * Real.sqrt n by nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ) ], Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ) ];
    nlinarith [ show ( 0 :ℝ ) < c * n by positivity, div_mul_cancel₀ ( 2 :ℝ ) ( show ( c * n :ℝ ) ≠ 0 by positivity ) ]

/-
The number of vertices whose degree increases by at least k is at most 2m/k.
-/
theorem degree_increase_bound {V : Type*} [Fintype V] [DecidableEq V]
  (G₀ Gₘ : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel Gₘ.Adj]
  (h_le : G₀ ≤ Gₘ)
  (m : ℕ)
  (h_edges : (Gₘ.edgeFinset \ G₀.edgeFinset).card ≤ m)
  (k : ℝ) (hk : k > 0) :
  ({v : V | (Gₘ.degree v : ℝ) - (G₀.degree v : ℝ) ≥ k}.toFinset.card : ℝ) ≤ 2 * m / k := by
    -- The sum of degree increases is twice the number of added edges, which is at most 2m.
    have h_sum_increases : ∑ v : V, ((Gₘ.degree v : ℝ) - (G₀.degree v : ℝ)) ≤ 2 * m := by
      -- Since $G₀ \leq Gₘ$, the number of edges in $Gₘ$ is at least the number of edges in $G₀$, so the sum of the degrees in $Gₘ$ is at least the sum of the degrees in $G₀$.
      have h_deg_sum : ∑ v : V, (Gₘ.degree v : ℝ) - ∑ v : V, (G₀.degree v : ℝ) = 2 * ((Gₘ.edgeFinset \ G₀.edgeFinset).card : ℝ) := by
        have h_deg_sum : ∑ v : V, (Gₘ.degree v : ℝ) = 2 * (Gₘ.edgeFinset.card : ℝ) ∧ ∑ v : V, (G₀.degree v : ℝ) = 2 * (G₀.edgeFinset.card : ℝ) := by
          exact ⟨ mod_cast Gₘ.sum_degrees_eq_twice_card_edges, mod_cast G₀.sum_degrees_eq_twice_card_edges ⟩;
        rw [ h_deg_sum.1, h_deg_sum.2, Finset.card_sdiff ];
        rw [ Nat.cast_sub ];
        · rw [ Finset.inter_eq_left.mpr ];
          · ring;
          · exact SimpleGraph.edgeFinset_mono h_le;
        · exact Finset.card_le_card fun x hx => by aesop;
      simpa [ Finset.sum_sub_distrib ] using h_deg_sum.le.trans ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr h_edges ) zero_le_two );
    -- By Markov's inequality, the number of vertices with degree increase at least k is at most 2m/k.
    have h_markov : (∑ v : V, ((Gₘ.degree v : ℝ) - (G₀.degree v : ℝ))) ≥ k * ((Set.toFinset {v : V | (Gₘ.degree v : ℝ) - (G₀.degree v : ℝ) ≥ k}).card : ℝ) := by
      have h_markov : (∑ v ∈ Finset.filter (fun v => (Gₘ.degree v : ℝ) - (G₀.degree v : ℝ) ≥ k) Finset.univ, ((Gₘ.degree v : ℝ) - (G₀.degree v : ℝ))) ≥ k * ((Set.toFinset {v : V | (Gₘ.degree v : ℝ) - (G₀.degree v : ℝ) ≥ k}).card : ℝ) := by
        exact le_trans ( by norm_num; linarith ) ( Finset.sum_le_sum fun x hx => show ( ( Gₘ.degree x : ℝ ) - G₀.degree x ) ≥ k from by aesop );
      refine' le_trans h_markov ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => sub_nonneg_of_le _ );
      simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
      exact Finset.card_mono fun x hx => by have := h_le; aesop;
    rw [ le_div_iff₀' hk ] ; linarith

/-
The number of vertices in U with degree at least 2c*sqrt(n) is at most 2cn.
-/
theorem high_degree_subset_bound {V : Type*} [Fintype V] [DecidableEq V]
  (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
  (n : ℕ) (c : ℝ) (U : Finset V)
  (h_le : G₀ ≤ G)
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (h_edges_added : (G.edgeFinset \ G₀.edgeFinset).card ≤ Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_c_pos : c > 0)
  (h_n_pos : n > 0) :
  (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)).card ≤ 2 * c * n := by
    -- By degree_increase_bound, the number of such vertices is at most 2m/k.
    have h_degree_increase_bound : (Finset.card (Finset.filter (fun v => (G.degree v : ℝ) - (G₀.degree v : ℝ) ≥ c * Real.sqrt n) U)) ≤ 2 * (Nat.floor (c ^ 2 * n ^ (3 / 2 : ℝ))) / (c * Real.sqrt n) := by
      have h_degree_increase_bound : (Finset.card (Finset.filter (fun v => (G.degree v : ℝ) - (G₀.degree v : ℝ) ≥ c * Real.sqrt n) (Finset.univ : Finset V))) ≤ 2 * (Nat.floor (c ^ 2 * n ^ (3 / 2 : ℝ))) / (c * Real.sqrt n) := by
        have := degree_increase_bound G₀ G h_le ( ⌊c ^ 2 * n ^ ( 3 / 2 : ℝ ) ⌋₊ ) ( by exact_mod_cast h_edges_added ) ( c * Real.sqrt n ) ( by positivity ) ; aesop;
      exact le_trans ( mod_cast Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.subset_univ _ ) h_degree_increase_bound;
    refine' le_trans ( mod_cast Finset.card_mono _ ) ( h_degree_increase_bound.trans _ );
    · rw [ div_le_iff₀ ] <;> ring_nf <;> norm_num [ h_c_pos, h_n_pos ];
      exact le_trans ( Nat.floor_le ( by positivity ) ) ( by rw [ show ( n : ℝ ) ^ ( 3 / 2 : ℝ ) = n * Real.sqrt n by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; ring_nf; norm_num );
    · simp_all +decide [ Finset.subset_iff ];
      exact fun v hv hv' => by linarith [ h_G₀_max_deg v ] ;

/-
Binomial coefficient upper bound.
-/
theorem binom_upper_bound (n k : ℕ) (hk : k > 0) : (n.choose k : ℝ) ≤ ((Real.exp 1 * n) / k) ^ k := by
  -- We'll use the fact that $(n choose k) \leq \frac{n^k}{k!}$ and $k! \geq \left(\frac{k}{e}\right)^k$.
  have h_binom : (n.choose k : ℝ) ≤ n^k / (Nat.factorial k) := by
    exact Nat.choose_le_pow_div k n
  have h_factorial : (Nat.factorial k : ℝ) ≥ (k / Real.exp 1) ^ k := by
    field_simp;
    rw [ div_pow, div_le_iff₀ ( by positivity ) ];
    rw [ ← div_le_iff₀' ( by positivity ) ];
    rw [ ← Real.exp_nat_mul, mul_comm, Real.exp_eq_exp_ℝ ];
    rw [ NormedSpace.exp_eq_tsum_div ];
    exact Summable.le_tsum ( show Summable _ from Real.summable_pow_div_factorial _ ) k ( fun _ _ => by positivity ) |> le_trans ( by norm_num );
  refine le_trans h_binom ?_;
  convert div_le_div_of_nonneg_left _ _ h_factorial using 1 <;> ring_nf <;> norm_num [ hk.ne' ];
  · ring;
  · positivity

/-
The probability of avoiding hits is bounded by (1-p)^m.
-/
def Process (State : Type) := State → Finset State

noncomputable def prob_avoid {State : Type} (P : Process State) (Hit : State → Finset State) (m : ℕ) (s : State) : ℝ :=
  match m with
  | 0 => 1
  | k + 1 =>
    let opts := P s
    if opts.card = 0 then 1
    else
      let non_hits := opts \ (Hit s)
      (∑ x ∈ non_hits, prob_avoid P Hit k x) / opts.card

/-
Algebraic inequality for entropy bound.
-/
theorem entropy_inequality_simple (c : ℝ) (hc : 0 < c) (hc_le : c ≤ 1) :
  1 - Real.log 5 + Real.log (1 / c) ≤ 2 * Real.log 2 * Real.log (1 / c) := by
    -- Since $c \leq 1$, we have $\log(1/c) \geq 0$. Let $x = \log(1/c)$.
    set x := Real.log (1 / c)
    have hx_nonneg : 0 ≤ x := by
      exact Real.log_nonneg <| one_le_one_div hc hc_le;
    -- We'll use that $Real.log 5 \approx 1.609$ and $Real.log 2 \approx 0.693$.
    have h_log_approx : Real.log 5 > 1.6 ∧ Real.log 2 > 0.69 := by
      norm_num [ Real.lt_log_iff_exp_lt ];
      constructor <;> rw [ ← Real.log_lt_log_iff ( by positivity ) ] <;> norm_num;
      · rw [ div_lt_iff₀' ] <;> norm_num [ ← Real.log_rpow, Real.lt_log_iff_exp_lt ];
        have := Real.exp_one_lt_d9.le ; norm_num at * ; rw [ show Real.exp 8 = ( Real.exp 1 ) ^ 8 by rw [ ← Real.exp_nat_mul ] ; norm_num ] ; exact lt_of_le_of_lt ( pow_le_pow_left₀ ( by positivity ) this _ ) ( by norm_num );
      · exact Real.log_two_gt_d9.trans_le' <| by norm_num;
    norm_num at h_log_approx ; nlinarith [ Real.log_le_sub_one_of_pos hc ]

/-
The function x(1 + ln(n/x)) is increasing for x < n.
-/
theorem x_log_en_div_x_increasing {n : ℝ} (hn : n > 0) :
  StrictMonoOn (fun x => x * (1 + Real.log (n / x))) (Set.Ioo 0 n) := by
    -- Let's calculate the derivative of $f(x) = x(1 + \ln(n/x))$.
    have h_deriv : ∀ x ∈ Set.Ioo 0 n, deriv (fun x : ℝ => x * (1 + Real.log (n / x))) x = Real.log (n / x) := by
      intro x hx; norm_num [ div_eq_mul_inv, differentiableAt_inv, hx.1.ne', hx.2.ne' ] ; ring_nf;
      norm_num [ differentiableAt_inv, hx.1.ne', hx.2.ne', ne_of_gt ( mul_pos hn ( inv_pos.mpr hx.1 ) ) ] ; ring_nf;
      grind;
    -- Since the derivative is positive for $x \in (0, n)$, the function is strictly increasing on this interval.
    intros x hx y hy hxy
    have h_deriv_pos : 0 < deriv (fun x : ℝ => x * (1 + Real.log (n / x))) x := by
      exact h_deriv x hx ▸ Real.log_pos ( by rw [ lt_div_iff₀ hx.1 ] ; linarith [ hx.2 ] );
    -- By the Mean Value Theorem, since the derivative is positive on (x, y), there exists some c in (x, y) such that the derivative at c is equal to (f(y) - f(x)) / (y - x).
    obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y, deriv (fun x : ℝ => x * (1 + Real.log (n / x))) c = ( (fun x : ℝ => x * (1 + Real.log (n / x))) y - (fun x : ℝ => x * (1 + Real.log (n / x))) x ) / (y - x) := by
      apply_rules [ exists_deriv_eq_slope ];
      · exact continuousOn_of_forall_continuousAt fun z hz => ContinuousAt.mul continuousAt_id <| ContinuousAt.add continuousAt_const <| ContinuousAt.log ( continuousAt_const.div continuousAt_id <| ne_of_gt <| lt_of_lt_of_le hx.1 hz.1 ) <| ne_of_gt <| div_pos hn <| lt_of_lt_of_le hx.1 hz.1;
      · exact fun z hz => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.mul ( differentiableAt_id ) ( DifferentiableAt.add ( differentiableAt_const _ ) ( DifferentiableAt.log ( DifferentiableAt.div ( differentiableAt_const _ ) differentiableAt_id ( by linarith [ hx.1, hy.1, hz.1 ] ) ) ( by exact ne_of_gt ( div_pos hn ( by linarith [ hx.1, hy.1, hz.1 ] ) ) ) ) ) );
    have h_deriv_pos : 0 < deriv (fun x : ℝ => x * (1 + Real.log (n / x))) c := by
      exact h_deriv c ⟨ by linarith [ hc.1.1, hx.1 ], by linarith [ hc.1.2, hy.2 ] ⟩ ▸ Real.log_pos ( by rw [ lt_div_iff₀ ] <;> linarith [ hc.1.1, hc.1.2, hx.1, hx.2, hy.1, hy.2 ] ) ;
    rw [ hc.2, lt_div_iff₀ ] at h_deriv_pos <;> linarith

/-
Binomial coefficient bounded by entropy-like term.
-/
theorem binom_entropy_bound (n : ℕ) (c : ℝ) (hc : c > 0) (hc_small : 5 * c * n ≥ 1) (hc_upper : c ≤ 1/10) :
  (n.choose (Nat.floor (5 * c * n)) : ℝ) ≤ 2 ^ (10 * c * n * Real.log (1 / c)) := by
    -- Let $k = \lfloor 5cn \rfloor$. Since $5cn \geq 1$, we have $k \geq 1$. Also, since $c \leq 1/10$, we have $5cn \leq n/2$, so $k < n$.
    set k := Nat.floor (5 * c * n)
    have hk_ge_1 : 1 ≤ k := by
      exact Nat.floor_pos.mpr hc_small
    have hk_lt_n : k < n := by
      exact Nat.floor_lt ( by positivity ) |>.2 ( by nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast; contrapose! hk_ge_1; aesop ] );
    -- By binom_upper_bound, binom(n, k) <= (e n / k)^k = exp(k * ln(e n / k)).
    have h_binom_bound : (Nat.choose n k : ℝ) ≤ Real.exp (k * Real.log (Real.exp 1 * n / k)) := by
      have h_binom_bound : (Nat.choose n k : ℝ) ≤ ((Real.exp 1 * n) / k)^k := by
        convert binom_upper_bound n k hk_ge_1 using 1;
      exact h_binom_bound.trans_eq ( by rw [ Real.exp_nat_mul, Real.exp_log ( by exact div_pos ( mul_pos ( Real.exp_pos _ ) ( Nat.cast_pos.mpr ( by linarith ) ) ) ( Nat.cast_pos.mpr ( by linarith ) ) ) ] );
    -- By x_log_en_div_x_increasing, f is increasing on (0, n).
    have h_inc : k * Real.log (Real.exp 1 * n / k) ≤ 5 * c * n * Real.log (Real.exp 1 / (5 * c)) := by
      have h_inc : StrictMonoOn (fun x => x * Real.log (Real.exp 1 * n / x)) (Set.Ioo 0 (n : ℝ)) := by
        convert x_log_en_div_x_increasing ( show ( n : ℝ ) > 0 by norm_cast; linarith ) using 1;
        ext x; by_cases hx : x = 0 <;> simp +decide [ hx, mul_div_assoc ] ;
        rw [ Real.log_mul ( by positivity ) ( by aesop ), Real.log_exp ];
      have h_inc : k * Real.log (Real.exp 1 * n / k) ≤ 5 * c * n * Real.log (Real.exp 1 * n / (5 * c * n)) := by
        exact h_inc.le_iff_le ( by constructor <;> nlinarith [ show ( k : ℝ ) ≥ 1 by exact_mod_cast hk_ge_1, show ( k : ℝ ) < n by exact_mod_cast hk_lt_n, Nat.floor_le ( show 0 ≤ 5 * c * ( n : ℝ ) by positivity ) ] ) ( by constructor <;> nlinarith [ show ( k : ℝ ) ≥ 1 by exact_mod_cast hk_ge_1, show ( k : ℝ ) < n by exact_mod_cast hk_lt_n, Nat.floor_le ( show 0 ≤ 5 * c * ( n : ℝ ) by positivity ) ] ) |>.2 <| by nlinarith [ show ( k : ℝ ) ≤ 5 * c * ( n : ℝ ) by exact_mod_cast Nat.floor_le ( show 0 ≤ 5 * c * ( n : ℝ ) by positivity ) ] ;
      convert h_inc using 2 ; ring_nf ; norm_num [ show n ≠ 0 by linarith ];
    -- By entropy_inequality_simple, ln(e / 5c) ≤ 2 ln 2 ln(1/c).
    have h_entropy : Real.log (Real.exp 1 / (5 * c)) ≤ 2 * Real.log 2 * Real.log (1 / c) := by
      convert entropy_inequality_simple c hc ( by linarith ) using 1 ; norm_num [ Real.log_div, Real.log_mul, hc.ne' ] ; ring;
    refine le_trans h_binom_bound <| le_trans ( Real.exp_le_exp.mpr <| h_inc.trans <| mul_le_mul_of_nonneg_left h_entropy <| by positivity ) ?_;
    rw [ Real.rpow_def_of_pos ( by positivity ) ] ; ring_nf ; norm_num

/-
NextGraphs and Reachable definitions.
-/
noncomputable def NextGraphs {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ) (n : ℕ) (G : SimpleGraph V) : Finset (SimpleGraph V) :=
  letI := Classical.decRel G.Adj
  (G.eligibleFinset c n).image (fun e => SimpleGraph.fromEdgeSet (G.edgeSet ∪ {e}))

/-
Adding an edge increases the degree of the endpoints by 1 and leaves others unchanged.
-/
theorem degree_add_edge {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) (h_ne : u ≠ v) (h_not_adj : ¬G.Adj u v) :
  let G' := SimpleGraph.fromEdgeSet (G.edgeSet ∪ {Sym2.mk (u, v)})
  ∀ w, G'.degree w = if w = u ∨ w = v then G.degree w + 1 else G.degree w := by
    simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ]
    intro w; split_ifs <;> simp_all +decide [ Finset.filter_or, Finset.filter_and, Finset.filter_eq' ]
    · split_ifs <;> simp_all +decide
      · congr 1 with x
        aesop
      · rw [ Finset.card_insert_of_notMem ] <;> simp +decide [ *, Finset.filter_ne ]
        · exact congr_arg Finset.card ( by ext; aesop )
        · exact fun a => h_not_adj (id (SimpleGraph.adj_symm G a))
    · exact congr_arg Finset.card ( by ext; aesop )

/-
The set of graphs obtainable from G by adding an eligible edge with both endpoints in U.
-/
noncomputable def HitGraphs {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ) (n : ℕ) (G : SimpleGraph V) (U : Finset V) : Finset (SimpleGraph V) :=
  letI := Classical.decRel G.Adj
  (G.eligiblePairsIn c n U).image (fun e => SimpleGraph.fromEdgeSet (G.edgeSet ∪ {e}))

/-
Adding an eligible edge preserves triangle-freeness.
-/
theorem SimpleGraph.add_eligible_edge_triangle_free {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) (n : ℕ) (u v : V)
  (h_free : G.CliqueFree 3)
  (h_eligible : G.eligiblePair c n u v) :
  (SimpleGraph.fromEdgeSet (G.edgeSet ∪ {Sym2.mk (u, v)})).CliqueFree 3 := by
    intro t h;
    rcases h with ⟨ h₁, h₂ ⟩;
    -- Since $t$ is a clique of size 3 in the new graph, it must contain the edge $\{u, v\}$.
    have h_edge : u ∈ t ∧ v ∈ t := by
      have huv_in_t : ∃ x y : V, x ∈ t ∧ y ∈ t ∧ x ≠ y ∧ (G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
        rcases Finset.card_eq_three.mp h₂ with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; use x, y ; aesop;
      obtain ⟨ x, y, hx, hy, hxy, h | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ⟩ := huv_in_t <;> simp_all +decide [ SimpleGraph.CliqueFree ];
      contrapose! h_free;
      use t;
      simp_all +decide [ SimpleGraph.isNClique_iff ];
      intro a ha b hb hab; specialize h₁ ha hb; aesop;
    -- Since $t$ is a clique of size 3 in the new graph, it must contain another vertex $w$ such that $w$ is adjacent to both $u$ and $v$.
    obtain ⟨w, hw⟩ : ∃ w ∈ t, w ≠ u ∧ w ≠ v := by
      exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( t.erase u ) from by rw [ Finset.card_erase_of_mem h_edge.1, h₂ ] ; decide ) v );
    have := h₁ hw.1 h_edge.1; have := h₁ hw.1 h_edge.2; simp_all +decide [ SimpleGraph.fromEdgeSet ] ;
    exact h_eligible.2.2.2.2 w ⟨ by tauto, by tauto ⟩

/-
The set of graphs obtained by adding an eligible edge in U is a subset of the set of graphs obtained by adding any eligible edge.
-/
theorem hit_subset_next {V : Type*} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (G : SimpleGraph V) (U : Finset V) :
  HitGraphs c n G U ⊆ NextGraphs c n G := by
    unfold HitGraphs NextGraphs;
    simp +decide [ Finset.subset_iff ];
    unfold SimpleGraph.eligiblePairsIn SimpleGraph.eligibleFinset; aesop;

/-
The number of hit graphs equals the number of eligible pairs in U.
-/
theorem card_HitGraphs_eq {V : Type*} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
  (HitGraphs c n G U).card = (G.eligiblePairsIn c n U).card := by
    convert Finset.card_image_of_injOn _;
    intro e he e' he' h_eq;
    replace h_eq := congr_arg ( fun f => f.edgeSet ) h_eq ; simp_all +decide [ Set.ext_iff ];
    have := h_eq e; have := h_eq e'; simp_all +decide [ SimpleGraph.eligiblePairsIn ] ;
    cases e ; cases e' ; simp_all +decide [ SimpleGraph.eligibleFinset ];
    cases eq_or_ne ‹_› ‹_› <;> simp_all +decide [ SimpleGraph.eligiblePair ];
    grind +ring

/-
The number of next graphs equals the number of eligible pairs.
-/
theorem card_NextGraphs_eq {V : Type*} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] :
  (NextGraphs c n G).card = (G.eligibleFinset c n).card := by
    convert rfl;
    convert Set.ncard_coe_finset _;
    rw [ Set.ncard_coe_finset ];
    convert card_HitGraphs_eq c n G Finset.univ;
    · rw [ card_HitGraphs_eq ];
      unfold SimpleGraph.eligiblePairsIn; aesop;
    · convert card_HitGraphs_eq c n G Finset.univ;
      ext; simp [NextGraphs, HitGraphs];
      simp +decide [ SimpleGraph.eligiblePairsIn ]

/-
Probability of avoiding hits with an invariant.
-/
theorem prob_avoid_bound_with_invariant {State : Type} (P : Process State) (Hit : State → Finset State)
  (m : ℕ) (s : State) (p : ℝ) (I : State → Prop)
  (h_start : I s)
  (h_invariant : ∀ s' g, I s' → g ∈ P s' \ Hit s' → I g)
  (h_hit_subset : ∀ s, I s → Hit s ⊆ P s)
  (h_hit_ratio : ∀ s, I s → ((Hit s).card : ℝ) / (P s).card ≥ p)
  (h_progress : ∀ s, I s → (P s).card > 0)
  (hp1 : p ≤ 1) :
  prob_avoid P Hit m s ≤ (1 - p)^m := by
    -- We proceed by induction on $m$.
    induction' m with m ih generalizing s;
    · exact Std.IsPreorder.le_refl (prob_avoid P Hit 0 s);
    · -- By definition of prob_avoid, we have:
      have h_prob_succ : prob_avoid P Hit (m + 1) s = (∑ x ∈ (P s \ Hit s), prob_avoid P Hit m x) / (P s).card := by
        exact if_neg ( ne_of_gt ( h_progress s h_start ) );
      -- By the induction hypothesis, we have:
      have h_ind_step : (∑ x ∈ (P s \ Hit s), prob_avoid P Hit m x) / (P s).card ≤ (∑ x ∈ (P s \ Hit s), (1 - p) ^ m) / (P s).card := by
        gcongr ; aesop;
      simp_all +decide [ Finset.card_sdiff, pow_succ' ];
      refine le_trans h_ind_step ?_;
      rw [ Nat.cast_sub ( Finset.card_le_card ( Finset.inter_subset_right ) ) ];
      rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| h_progress s h_start ) ];
      rw [ Finset.inter_eq_left.mpr ( h_hit_subset s h_start ) ];
      have := h_hit_ratio s h_start; rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| Finset.card_pos.mpr <| h_progress s h_start ) ] at this; nlinarith [ pow_nonneg ( sub_nonneg.mpr hp1 ) m ] ;

/-
The state of the process consists of a graph and the number of edges added so far.
-/
def ProcessState (V : Type*) := SimpleGraph V × ℕ

/-
The set of possible next states and the set of "hit" states (where we add an edge in U).
-/
noncomputable def NextGraphsState {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ) (n : ℕ) (s : ProcessState V) : Finset (ProcessState V) :=
  (NextGraphs c n s.1).image (fun G' => (G', s.2 + 1))

noncomputable def HitGraphsState {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ) (n : ℕ) (U : Finset V) (s : ProcessState V) : Finset (ProcessState V) :=
  (HitGraphs c n s.1 U).image (fun G' => (G', s.2 + 1))

/-
If a graph is a next graph but not a hit graph, the added edge does not have both endpoints in U.
-/
theorem not_hit_implies_not_in_U {V : Type*} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V)
  (G' : SimpleGraph V)
  (h_next : G' ∈ NextGraphs c n G)
  (h_not_hit : G' ∉ HitGraphs c n G U) :
  ∀ e, e ∈ G'.edgeFinset \ G.edgeFinset → ¬(e.out.1 ∈ U ∧ e.out.2 ∈ U) := by
    unfold NextGraphs at h_next; unfold HitGraphs at *; simp_all +decide [ SimpleGraph.eligiblePairsIn ] ;
    obtain ⟨ a, ha, rfl ⟩ := h_next; simp_all +decide [ SimpleGraph.edgeSet ] ;
    specialize h_not_hit a ha ; simp_all +decide [ SimpleGraph.edgeSetEmbedding ];
    rcases a with ⟨ x, y ⟩ ; simp_all +decide [ Sym2.mem_iff ] ;
    cases h_not_hit <;> simp_all +decide [ Quot.out ];
    · have := Classical.choose_spec ( show ∃ p : V × V, Sym2.mk p = Quot.mk ( Sym2.Rel V ) ( x, y ) from ⟨ ( x, y ), rfl ⟩ ) ; aesop;
    · have := Classical.choose_spec ( Quot.exists_rep ( Quot.mk ( Sym2.Rel V ) ( x, y ) ) ) ; aesop;

/-
Adding an eligible edge preserves the maximum degree bound.
-/
theorem degree_bound_preserved {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) (n : ℕ) (u v : V)
  (h_eligible : G.eligiblePair c n u v)
  (h_bound : ∀ w, G.degree w ≤ Nat.ceil (2 * c * Real.sqrt n)) :
  let G' := SimpleGraph.fromEdgeSet (G.edgeSet ∪ {Sym2.mk (u, v)})
  ∀ w, G'.degree w ≤ Nat.ceil (2 * c * Real.sqrt n) := by
    unfold SimpleGraph.eligiblePair at h_eligible;
    intro G' w;
    by_cases hw : w = u ∨ w = v;
    · convert Nat.succ_le_of_lt ( Nat.lt_ceil.mpr _ ) using 1;
      rotate_left;
      exact if w = u then G.degree u else G.degree v;
      · grind;
      · convert degree_add_edge G u v h_eligible.1 h_eligible.2.1 w using 1;
        aesop;
    · convert h_bound w using 1;
      simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
      congr! 1 ; aesop

/-
Adding a new edge increases the size of the difference set by 1.
-/
theorem card_edge_diff_succ {V : Type*} [Fintype V] [DecidableEq V]
  (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
  (e : Sym2 V)
  (h_le : G₀ ≤ G)
  (h_not_mem : e ∉ G.edgeFinset)
  (h_not_diag : ¬e.IsDiag) :
  let G' := SimpleGraph.fromEdgeSet (G.edgeSet ∪ {e})
  haveI := Classical.decRel G'.Adj
  (G'.edgeFinset \ G₀.edgeFinset).card = (G.edgeFinset \ G₀.edgeFinset).card + 1 := by
    -- Since $G₀ \leq G$, $e$ is not in $G₀$.
    have h_not_in_G₀ : e ∉ G₀.edgeFinset := by
      contrapose! h_not_mem;
      cases e ; aesop;
    have h_new_edges : (SimpleGraph.fromEdgeSet (G.edgeSet ∪ {e})).edgeFinset = G.edgeFinset ∪ {e} := by
      ext ⟨ u, v ⟩ ; aesop;
    grind

set_option maxHeartbeats 0 in
/-
If a state is a next state but not a hit state, it corresponds to adding an eligible edge that is not in U.
-/
theorem mem_NextGraphsState_diff_HitGraphsState {V : Type*} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (U : Finset V) (s : ProcessState V) (g : ProcessState V)
  (h : g ∈ NextGraphsState c n s \ HitGraphsState c n U s) :
  ∃ e : Sym2 V, s.1.eligiblePair c n e.out.1 e.out.2 ∧
       g.1 = SimpleGraph.fromEdgeSet (s.1.edgeSet ∪ {e}) ∧
       g.2 = s.2 + 1 ∧
       ¬(e.out.1 ∈ U ∧ e.out.2 ∈ U) := by
         have := not_hit_implies_not_in_U c n s.1 U; simp_all +decide [ NextGraphsState, HitGraphsState ] ;
         rcases h with ⟨ ⟨ G', hG', rfl ⟩, hG'' ⟩ ; ( unfold NextGraphs HitGraphs at *; simp_all +decide [ Finset.mem_image ] ; );
         rcases hG' with ⟨ e, he, rfl ⟩ ; specialize this e he ; simp_all +decide [ SimpleGraph.fromEdgeSet ] ;
         refine' ⟨ e, _, rfl, _ ⟩ <;> simp_all +decide [ SimpleGraph.eligibleFinset, SimpleGraph.eligiblePairsIn ] ;
         · convert he using 1;
           constructor <;> intro h <;> simp_all +decide [ Sym2.fromRel ];
           convert he using 1;
           rw [ ← Quot.out_eq e ] ; simp +decide [ Sym2.lift ] ;
           rw [ ← Quot.out_eq e ] ; simp +decide
           rfl;
         · contrapose! this; simp_all +decide [ Sym2.fromRel ] ;
           cases e ; simp_all +decide [ Sym2.lift ] ;
           cases he ; aesop

/-
The number of next states equals the number of next graphs.
-/
theorem card_NextGraphsState_eq {V : Type*} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (s : ProcessState V) :
  (NextGraphsState c n s).card = (NextGraphs c n s.1).card := by
    -- The function that maps G' to (G', s.2 + 1) is injective because if (G1, k) = (G2, k), then G1 must equal G2.
    have h_inj : Function.Injective (fun G' : SimpleGraph V => (G', s.2 + 1)) := by
      exact fun x y hxy => by simpa using hxy;
    exact Finset.card_image_of_injective _ h_inj

/-
Adding an edge that does not have both endpoints in U preserves the independence of U.
-/
theorem SimpleGraph.IsIndepSet_add_edge_sym2 {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) (e : Sym2 V)
  (h_indep : G.IsIndepSet U)
  (h_not_in_U : ¬(e.out.1 ∈ U ∧ e.out.2 ∈ U)) :
  (SimpleGraph.fromEdgeSet (G.edgeSet ∪ {e})).IsIndepSet U := by
    simp_all +decide [ Set.Pairwise ];
    have := Quot.out_eq e;
    cases h' : Quot.out e ; aesop

/-
Definitions of the process, hit set, and invariant for the probabilistic argument.
-/
noncomputable def TheProcess {V : Type} [Fintype V] [DecidableEq V] (c : ℝ) (n : ℕ) (m : ℕ) : Process (ProcessState V) :=
  fun s => if s.2 < m then NextGraphsState c n s else {s}

noncomputable def TheHit {V : Type} [Fintype V] [DecidableEq V] (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V) : ProcessState V → Finset (ProcessState V) :=
  fun s => if s.2 < m then HitGraphsState c n U s else {s}

def MyInvariant {V : Type} [Fintype V] [DecidableEq V] (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V) (s : ProcessState V) : Prop :=
  G₀ ≤ s.1 ∧
  s.1.CliqueFree 3 ∧
  s.1.IsIndepSet U ∧
  (∀ v, s.1.degree v ≤ Nat.ceil (2 * c * Real.sqrt n)) ∧
  (s.1.edgeFinset \ G₀.edgeFinset).card = s.2 ∧
  s.2 ≤ m

/-
If a step is taken in the process (avoiding the hit set), then the current number of edges is less than m.
-/
theorem step_implies_lt_m {V : Type} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (s : ProcessState V) (g : ProcessState V)
  (h_step : g ∈ (TheProcess c n m s) \ (TheHit c n m U s)) :
  s.2 < m := by
    unfold TheProcess TheHit at h_step ; aesop

/-
Adding an eligible edge increases the edge count difference by exactly 1.
-/
theorem invariant_preservation_step_card {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (s : ProcessState V) (g : ProcessState V) (e : Sym2 V)
  (h_inv_le : G₀ ≤ s.1)
  (h_inv_card : (s.1.edgeFinset \ G₀.edgeFinset).card = s.2)
  (h_eligible : s.1.eligiblePair c n e.out.1 e.out.2)
  (h_g1 : g.1 = SimpleGraph.fromEdgeSet (s.1.edgeSet ∪ {e}))
  (h_g2 : g.2 = s.2 + 1) :
  (g.1.edgeFinset \ G₀.edgeFinset).card = g.2 := by
    have h_e_not_in_s : e ∉ s.1.edgeFinset := by
      have h_e_not_in_s : ¬s.1.Adj (Quot.out e).1 (Quot.out e).2 := by
        exact h_eligible.2.1;
      convert h_e_not_in_s using 1;
      rw [ ← SimpleGraph.mem_edgeSet ];
      cases e ; aesop
    have h_e_not_diag : ¬e.IsDiag := by
      -- Since $e.out.1 \neq e.out.2$, $e$ cannot be a diagonal.
      have h_not_diag : e.out.1 ≠ e.out.2 := by
        exact h_eligible.1;
      rw [ ← Quot.out_eq e ];
      exact h_not_diag
    have h_card_edge_diff_succ : (g.1.edgeFinset \ G₀.edgeFinset).card = (s.1.edgeFinset \ G₀.edgeFinset).card + 1 := by
      convert card_edge_diff_succ G₀ s.1 e h_inv_le h_e_not_in_s h_e_not_diag using 1;
      rw [ h_g1 ];
      convert rfl;
    grind

/-
If a state satisfies the invariant and we add an eligible edge not in U, the new state satisfies the invariant.
-/
theorem invariant_preservation_step {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (s : ProcessState V) (g : ProcessState V) (e : Sym2 V)
  (h_inv : MyInvariant G₀ c n m U s)
  (h_eligible : s.1.eligiblePair c n e.out.1 e.out.2)
  (h_g1 : g.1 = SimpleGraph.fromEdgeSet (s.1.edgeSet ∪ {e}))
  (h_g2 : g.2 = s.2 + 1)
  (h_not_in_U : ¬(e.out.1 ∈ U ∧ e.out.2 ∈ U))
  (h_lt_m : s.2 < m) :
  MyInvariant G₀ c n m U g := by
    have h_deg_bound : ∀ v, g.1.degree v ≤ Nat.ceil (2 * c * Real.sqrt n) := by
      convert degree_bound_preserved s.1 c n ( e.out.1 ) ( e.out.2 ) h_eligible ( fun v => ?_ ) using 1;
      · convert Iff.rfl using 3 ; aesop;
      · exact h_inv.2.2.2.1 v
    have h_card : (g.1.edgeFinset \ G₀.edgeFinset).card = g.2 := by
      have := invariant_preservation_step_card G₀ c n s g e h_inv.1 h_inv.2.2.2.2.1 h_eligible h_g1 h_g2; aesop;
    have h_le_m : g.2 ≤ m := by
      linarith [ h_inv.2.2.2.2.2 ]
    exact ⟨by
    exact h_g1 ▸ le_trans h_inv.1 ( by aesop_cat ), by
      convert SimpleGraph.add_eligible_edge_triangle_free s.1 c n ( Quot.out e ).1 ( Quot.out e ).2 h_inv.2.1 h_eligible using 1 ; aesop ( simp_config := { singlePass := true } ) ;, by
      convert SimpleGraph.IsIndepSet_add_edge_sym2 _ _ _ _ _ using 1;
      convert h_g1;
      · infer_instance;
      · infer_instance;
      · infer_instance;
      · exact h_inv.2.2.1;
      · exact h_not_in_U, h_deg_bound, h_card, h_le_m⟩

/-
The invariant is preserved by the process when avoiding the hit set.
-/
theorem invariant_preservation {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (s : ProcessState V) (g : ProcessState V)
  (h_inv : MyInvariant G₀ c n m U s)
  (h_step : g ∈ (TheProcess c n m s) \ (TheHit c n m U s)) :
  MyInvariant G₀ c n m U g := by
    -- Use `mem_NextGraphsState_diff_HitGraphsState` to find the edge `e`.
    obtain ⟨e, h_e1, h_e2, h_e3, h_e4⟩ : ∃ e : Sym2 V, s.1.eligiblePair c n e.out.1 e.out.2 ∧ g.1 = SimpleGraph.fromEdgeSet (s.1.edgeSet ∪ {e}) ∧ g.2 = s.2 + 1 ∧ ¬(e.out.1 ∈ U ∧ e.out.2 ∈ U) := by
      convert mem_NextGraphsState_diff_HitGraphsState c n U s g _;
      unfold TheProcess TheHit at h_step; aesop;
    apply invariant_preservation_step G₀ c n m U s g e h_inv h_e1 h_e2 h_e3 h_e4 (step_implies_lt_m c n m U s g h_step)

/-
The number of hit states equals the number of hit graphs.
-/
theorem card_HitGraphsState_eq {V : Type*} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (U : Finset V) (s : ProcessState V) :
  (HitGraphsState c n U s).card = (HitGraphs c n s.1 U).card := by
    refine' le_antisymm _ _;
    · exact Finset.card_image_le;
    · refine' le_trans _ ( Finset.card_le_card _ );
      rotate_left;
      exact Finset.image ( fun G' => ( G', s.2 + 1 ) ) ( HitGraphs c n s.1 U );
      · exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_image.mpr ⟨ x, hx, rfl ⟩;
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by injection hxy ]

/-
The set of hit states is a subset of the set of next states.
-/
theorem HitGraphsState_subset_NextGraphsState {V : Type*} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (U : Finset V) (s : ProcessState V) :
  HitGraphsState c n U s ⊆ NextGraphsState c n s := by
    -- Since HitGraphs is a subset of NextGraphs, applying the same function to both sides preserves the subset relationship.
    have h_subset : HitGraphs c n s.1 U ⊆ NextGraphs c n s.1 := by
      exact hit_subset_next c n s.1 U;
    exact Finset.image_subset_image h_subset

/-
The hit set is a subset of the process options.
-/
theorem TheHit_subset_TheProcess {V : Type} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V) (s : ProcessState V) :
  TheHit c n m U s ⊆ TheProcess c n m s := by
    by_cases h : s.2 < m <;> simp_all +decide [ TheHit, TheProcess ];
    · exact HitGraphsState_subset_NextGraphsState _ _ _ _;
    · grind

/-
Upper bound on common neighbor pairs using the ceiling of the degree bound.
-/
theorem common_neighbor_count_upper_bound_ceil {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (c : ℝ) (n : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_max_deg : ∀ v, G.degree v ≤ Nat.ceil (2 * c * Real.sqrt n)) :
  (G.commonNeighborPairsIn U).card ≤ n * Nat.choose (Nat.ceil (2 * c * Real.sqrt n)) 2 := by
    convert common_neighbor_bound G U |> le_trans <| Finset.sum_le_sum fun v _ => Nat.choose_le_choose _ <| h_max_deg v |> le_trans ( Finset.card_le_card <| show G.neighborFinset v ∩ U ⊆ G.neighborFinset v from Finset.inter_subset_left ) using 1 ; 
    subst h_n
    simp_all only [Finset.sum_const, Finset.card_univ, smul_eq_mul];

/-
Lower bound on the number of eligible pairs in U, using the ceiling degree bound.
-/
theorem eligible_pairs_count_lower_bound_ceil {V : Type*} [Fintype V] [DecidableEq V]
  (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
  (n : ℕ) (c : ℝ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_le : G₀ ≤ G)
  (h_indep : G.IsIndepSet U)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (h_G_max_deg : ∀ v, (G.degree v : ℝ) ≤ Nat.ceil (2 * c * Real.sqrt n))
  (h_edges_added : (G.edgeFinset \ G₀.edgeFinset).card ≤ Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_c_pos : c > 0)
  (h_n_large : n ≥ 1000)
  (h_c_lower : c * Real.sqrt n ≥ 4) :
  (G.eligiblePairsIn c n U).card ≥ Nat.floor (2 * c^2 * n^2) := by
    have h_subset : (G.eligiblePairsIn c n U).card ≥ (Nat.choose (Nat.floor (5 * c * n) - Nat.floor (2 * c * n)) 2 : ℝ) - (n : ℝ) * (Nat.choose (Nat.ceil (2 * c * Real.sqrt n)) 2 : ℝ) := by
      have h_subset : (G.eligiblePairsIn c n U).card ≥ (Nat.choose (U.card - (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)).card) 2 : ℝ) - (n : ℝ) * (Nat.choose (Nat.ceil (2 * c * Real.sqrt n)) 2 : ℝ) := by
        have h_subset : (G.eligiblePairsIn c n U).card ≥ (Nat.choose (U.card - (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)).card) 2 : ℝ) - (G.commonNeighborPairsIn U).card := by
          have h_subset : (G.eligiblePairsIn c n U).card ≥ (Nat.choose (U.card - (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)).card) 2 : ℝ) - (G.commonNeighborPairsIn U).card := by
            have h_subset : (G.eligiblePairsIn c n U).card ≥ (Nat.choose (U.card - (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)).card) 2 : ℝ) - (G.commonNeighborPairsIn U).card := by
              have h_subset : (G.eligiblePairsIn c n U).card ≥ (Finset.card (SimpleGraph.distinctPairsIn (U \ (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)))) - (G.commonNeighborPairsIn U).card) := by
                have h_subset : (G.eligiblePairsIn c n U).card ≥ (Finset.card (SimpleGraph.distinctPairsIn (U \ (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)))) - (G.commonNeighborPairsIn U).card) := by
                  have h_subset : (G.eligiblePairsIn c n U) ⊇ (SimpleGraph.distinctPairsIn (U \ (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)))) \ (G.commonNeighborPairsIn U) := by
                    apply subset_eligible_pairs G c n U (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)) h_indep;
                    grind
                  have h_card_subset : (G.eligiblePairsIn c n U).card ≥ ((SimpleGraph.distinctPairsIn (U \ (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)))) \ (G.commonNeighborPairsIn U)).card := by
                    exact Finset.card_le_card h_subset;
                  grind;
                convert h_subset using 1
              have h_subset : (Finset.card (SimpleGraph.distinctPairsIn (U \ (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)))) : ℝ) = (Nat.choose (U.card - (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)).card) 2 : ℝ) := by
                convert congr_arg ( ( ↑ ) : ℕ → ℝ ) ( card_distinctPairsIn ( U \ Finset.filter ( fun v => ( G.degree v : ℝ ) ≥ 2 * c * Real.sqrt n ) U ) ) using 1;
                grind;
              rw [ ← h_subset ];
              norm_cast;
              rw [ Int.subNatNat_eq_coe ] ; omega
            exact h_subset;
          convert h_subset using 1;
        refine' le_trans _ h_subset;
        gcongr;
        exact_mod_cast common_neighbor_count_upper_bound_ceil G c n U h_n ( fun v => Nat.cast_le.mp ( h_G_max_deg v ) );
      have h_card_S : (U.filter (fun v => (G.degree v : ℝ) ≥ 2 * c * Real.sqrt n)).card ≤ 2 * c * n := by
        convert high_degree_subset_bound G₀ G n c U h_le h_G₀_max_deg h_edges_added h_c_pos ( by linarith ) using 1;
      refine' le_trans _ h_subset;
      gcongr;
      rw [ h_U_card ];
      refine' Nat.choose_le_choose _ _;
      refine' Nat.sub_le_sub_left _ _;
      exact Nat.le_floor h_card_S;
    have h_bound : (Nat.choose (Nat.floor (5 * c * n) - Nat.floor (2 * c * n)) 2 : ℝ) - (n : ℝ) * (Nat.choose (Nat.ceil (2 * c * Real.sqrt n)) 2 : ℝ) ≥ 2 * c^2 * n^2 := by
      have := numeric_inequality_part1 n c h_n_large h_c_pos ( by linarith ) ; have := numeric_inequality_part2 n c ( by linarith ) h_c_pos ; have := numeric_inequality_final_step n c h_n_large h_c_pos h_c_lower ; norm_num at * ; linarith;
    exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.floor_le ( show 0 ≤ 2 * c ^ 2 * n ^ 2 by positivity ) ] ;

/-
The probability of picking an edge in U is at least p_val.
-/
noncomputable def p_val (n : ℕ) (c : ℝ) : ℝ :=
  (Nat.floor (2 * c^2 * n^2) : ℝ) / (n.choose 2)

theorem hit_ratio_bound_ceil {V : Type*} [Fintype V] [DecidableEq V]
  (G₀ G : SimpleGraph V) [DecidableRel G₀.Adj] [DecidableRel G.Adj]
  (n : ℕ) (c : ℝ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_le : G₀ ≤ G)
  (h_indep : G.IsIndepSet U)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (h_G_max_deg : ∀ v, (G.degree v : ℝ) ≤ Nat.ceil (2 * c * Real.sqrt n))
  (h_edges_added : (G.edgeFinset \ G₀.edgeFinset).card ≤ Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_c_pos : c > 0)
  (h_n_large : n ≥ 1000)
  (h_c_lower : c * Real.sqrt n ≥ 4) :
  ((HitGraphs c n G U).card : ℝ) / (NextGraphs c n G).card ≥ p_val n c := by
    -- By definition of `hit_ratio_bound_ceil`, we know that the ratio of eligible edges in U to all eligible edges is at least `p_val`.
    have h_hit_ratio_bound : (HitGraphs c n G U).card ≥ Nat.floor (2 * c^2 * n^2) := by
      convert eligible_pairs_count_lower_bound_ceil G₀ G n c U h_n h_le h_indep h_U_card h_G₀_max_deg h_G_max_deg h_edges_added h_c_pos h_n_large h_c_lower using 1;
      convert card_HitGraphs_eq c n G U using 1;
    refine' le_div_iff₀' _ |>.2 _;
    · rw [ card_NextGraphs_eq ];
      have h_card_pos : (G.eligibleFinset c n).card ≥ (Nat.floor (2 * c^2 * n^2) : ℝ) := by
        refine' le_trans ( Nat.cast_le.mpr h_hit_ratio_bound ) _;
        convert Set.ncard_le_ncard ( show ( G.eligiblePairsIn c n U : Set ( Sym2 V ) ) ⊆ G.eligibleFinset c n from ?_ ) using 1;
        · rw [ card_HitGraphs_eq ] ; norm_cast;
        · simp +decide [ Set.subset_def, SimpleGraph.eligiblePairsIn ];
          exact fun x hx hx' => hx;
      exact lt_of_lt_of_le ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, show ( c : ℝ ) ^ 2 * n ≥ 16 by nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, show ( c : ℝ ) * Real.sqrt n ≥ 4 by assumption, Real.mul_self_sqrt ( Nat.cast_nonneg n ) ] ] ) h_card_pos;
    · refine' le_trans _ ( Nat.cast_le.mpr h_hit_ratio_bound );
      refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr ( Finset.card_le_card ( Finset.image_subset_iff.mpr _ ) ) ) _ ) _;
      exact Finset.image ( fun e => SimpleGraph.fromEdgeSet ( G.edgeSet ∪ { e } ) ) ( Finset.filter ( fun e => ¬e.IsDiag ) ( Finset.univ : Finset ( Sym2 V ) ) );
      · simp +decide [ SimpleGraph.eligibleFinset ];
        rintro ⟨ a, b ⟩ ⟨ h₁, h₂ ⟩ ; use Sym2.mk ( a, b ) ; aesop;
      · exact div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
      · refine' le_trans ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_image_le ) <| _ ) _;
        · exact div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
        · unfold p_val; norm_num [ Finset.filter_not, Finset.card_sdiff ] ; ring_nf;
          rw [ Nat.cast_sub ];
          · rw [ show ( Finset.filter Sym2.IsDiag Finset.univ : Finset ( Sym2 V ) ) = Finset.image ( fun v => Sym2.mk ( v, v ) ) Finset.univ from ?_, Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] ; simp +decide [ Sym2.card ];
            · rw [ Nat.choose_two_right ];
              rw [ Nat.cast_div ] <;> norm_num;
              · rw [ Nat.choose_two_right ];
                rw [ Nat.cast_div ] <;> norm_num;
                · field_simp;
                  rw [ div_le_iff₀ ] <;> norm_num [ h_n ];
                  · rw [ Nat.cast_sub ] <;> push_cast <;> linarith;
                  · linarith;
                · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ );
              · exact Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] );
            · ext ⟨ x, y ⟩ ; aesop;
          · exact Finset.card_le_univ _

/-
p_val is at most 1.
-/
theorem p_val_le_one (n : ℕ) (c : ℝ) (h_n : n ≥ 1000) (h_c : c ≤ 1/10) (h_c_pos : c > 0) : p_val n c ≤ 1 := by
  -- We have p_val = floor(2c^2n^2) / n.choose 2.
  -- Since c <= 1/10, 2c^2 <= 2/100 = 1/50.
  -- So numerator <= n^2/50.
  -- Denominator = n(n-1)/2.
  -- Ratio is approx (n^2/50) / (n^2/2) = 1/25 <= 1.
  have h_ratio : (Nat.floor (2 * c^2 * n^2) : ℝ) ≤ n^2 / 50 := by
    exact le_trans ( Nat.floor_le ( by positivity ) ) ( by nlinarith [ show ( n : ℝ ) ^ 2 ≥ 1000 ^ 2 by exact_mod_cast Nat.pow_le_pow_left h_n 2, mul_le_mul_of_nonneg_left h_c ( by positivity : ( 0 :ℝ ) ≤ n ^ 2 ) ] );
  refine' div_le_one_of_le₀ _ ( Nat.cast_nonneg _ );
  rw [ Nat.choose_two_right ];
  rw [ Nat.cast_div ] <;> norm_num;
  · rw [ Nat.cast_sub ] <;> push_cast <;> nlinarith [ ( by norm_cast : ( 1000 : ℝ ) ≤ n ) ];
  · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ )

/-
If s.2 < m, the ratio of hit states to next states is at least p_val.
-/
theorem prob_avoid_ratio_condition_lt_m {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (s : ProcessState V)
  (h_inv : MyInvariant G₀ c n m U s)
  (h_lt : s.2 < m) :
  ((TheHit c n m U s).card : ℝ) / (TheProcess c n m s).card ≥ p_val n c := by
    rw [ show TheHit c n m U s = HitGraphsState c n U s from ?_, show TheProcess c n m s = NextGraphsState c n s from ?_ ];
    · rw [ card_HitGraphsState_eq, card_NextGraphsState_eq ];
      convert hit_ratio_bound_ceil G₀ s.1 n c U _ _ _ _ _ _ _ _ _ using 1;
      any_goals assumption;
      · exact ⟨ fun h => fun _ => h, fun h => h h_c_lower ⟩;
      · exact h_inv.1;
      · cases h_inv ; aesop;
      · exact_mod_cast h_inv.2.2.2.1;
      · cases h_inv ; aesop;
    · exact if_pos h_lt;
    · exact if_pos h_lt;

/-
The ratio of hit states to next states is at least p_val for all valid states.
-/
theorem prob_avoid_ratio_condition {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_small : c ≤ 1/10)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (s : ProcessState V)
  (h_inv : MyInvariant G₀ c n m U s) :
  ((TheHit c n m U s).card : ℝ) / (TheProcess c n m s).card ≥ p_val n c := by
    by_cases h_lt : s.2 < m;
    · convert prob_avoid_ratio_condition_lt_m G₀ c n m U h_n h_n_large h_c_pos h_c_lower h_U_card h_m h_G₀_max_deg s h_inv h_lt using 1;
    · -- Since $s.2 \geq m$, we have $s.2 = m$ by the invariant.
      have h_eq : s.2 = m := by
        exact le_antisymm ( h_inv.2.2.2.2.2 ) ( not_lt.mp h_lt );
      unfold TheHit TheProcess; simp +decide [ h_eq ] ;
      exact p_val_le_one n c h_n_large h_c_small h_c_pos

/-
The process always has at least one next state.
-/
theorem process_progress {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (s : ProcessState V)
  (h_inv : MyInvariant G₀ c n m U s) :
  (TheProcess c n m s).card > 0 := by
    by_cases h : s.2 < m <;> simp_all +decide [ TheProcess, NextGraphsState ];
    · -- By eligible_pairs_count_lower_bound_ceil, the number of eligible pairs in U is at least floor(2c^2n^2).
      have h_eligible_pairs : (s.1.eligiblePairsIn c n U).card ≥ Nat.floor (2 * c^2 * n^2) := by
        convert eligible_pairs_count_lower_bound_ceil G₀ s.1 n c U h_n _ _ _ _ _ _ _ _ _ using 1;
        all_goals try linarith;
        · exact h_inv.1;
        · exact h_inv.2.2.1;
        · exact h_G₀_max_deg;
        · exact_mod_cast h_inv.2.2.2.1;
        · cases h_inv ; aesop;
      -- Since there's at least one eligible pair, the NextGraphs is nonempty.
      have h_next_nonempty : ∃ e ∈ s.1.eligiblePairsIn c n U, True := by
        refine' Exists.elim ( Finset.card_pos.mp ( lt_of_lt_of_le _ h_eligible_pairs ) ) fun e he => ⟨ e, he, trivial ⟩;
        exact Nat.floor_pos.mpr ( by nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, show ( c : ℝ ) ^ 2 * n ≥ 16 by nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, Real.mul_self_sqrt ( Nat.cast_nonneg n ) ] ] );
      obtain ⟨ e, he₁, he₂ ⟩ := h_next_nonempty; exact ⟨ _, Finset.mem_image.mpr ⟨ e, by { unfold SimpleGraph.eligiblePairsIn at *; aesop }, rfl ⟩ ⟩ ;
    · split_ifs <;> simp_all +decide [ MyInvariant ];
      linarith

/-
The probability that U remains independent is at most (1 - p_val)^m.
-/
theorem prob_avoid_U_bound {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_inv_start : MyInvariant G₀ c n m U (G₀, 0))
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_small : c ≤ 1/10)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n) :
  prob_avoid (TheProcess c n m) (TheHit c n m U) m (G₀, 0) ≤ (1 - p_val n c)^m := by
    apply prob_avoid_bound_with_invariant;
    · exact h_inv_start
    · exact fun s' g a a_1 => invariant_preservation G₀ c n m U s' g a a_1
    · exact fun s a => TheHit_subset_TheProcess c n m U s
    · exact fun s a =>
      prob_avoid_ratio_condition G₀ c n m U h_n h_n_large h_c_pos h_c_small h_c_lower h_U_card
        h_m h_G₀_max_deg s a
    · exact fun s a =>
      process_progress G₀ c n m U h_n h_n_large h_c_pos h_c_lower h_U_card h_m h_G₀_max_deg s a
    · exact p_val_le_one n c h_n_large h_c_small h_c_pos

/-
p_val * m is at least 3 * c^4 * n^(3/2).
-/
theorem p_val_mul_m_ge (n : ℕ) (c : ℝ) (m : ℕ)
  (h_n : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ))) :
  p_val n c * m ≥ 3 * c^4 * n^(3/2 : ℝ) := by
    -- By simplifying, we can see that the inequality holds.
    have h_simplify : 2 * (2 * c^2 * n^2 - 1) * (c^2 * n^(3/2 : ℝ) - 1) ≥ 3 * c^4 * n^(5/2 : ℝ) * (n - 1) := by
      rw [ show ( 5 / 2 : ℝ ) = 2 + 1 / 2 by norm_num, Real.rpow_add ] <;> norm_num <;> try positivity;
      rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ] <;> norm_num <;> try positivity;
      rw [ ← Real.sqrt_eq_rpow ] at *;
      have h_simplify : c^2 * n ≥ 16 := by
        nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, Real.mul_self_sqrt ( Nat.cast_nonneg n ) ];
      nlinarith [ show 0 < c ^ 4 * n ^ 2 * Real.sqrt n by positivity, show 0 < c ^ 4 * n ^ 3 * Real.sqrt n by positivity, show 0 < c ^ 2 * n ^ 2 * Real.sqrt n by positivity, show 0 < c ^ 2 * n ^ 3 * Real.sqrt n by positivity, Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, pow_two_nonneg <| c ^ 2 * n - 4, pow_two_nonneg <| c ^ 2 * n ^ 2 - 4 * n ];
    -- By multiplying both sides of the inequality from h_simplify by the positive terms, we can derive the desired result.
    have h_final : (Nat.floor (2 * c^2 * n^2) : ℝ) * ⌊c^2 * n^(3/2 : ℝ)⌋₊ ≥ 3 * c^4 * n^(5/2 : ℝ) * (n - 1) / 2 := by
      field_simp;
      refine le_trans h_simplify ?_;
      gcongr <;> norm_num;
      · rw [ show ( n : ℝ ) ^ ( 3 / 2 : ℝ ) = n * Real.sqrt n by rw [ Real.sqrt_eq_rpow, ← Real.rpow_one_add' ] <;> norm_num ] ; nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, mul_le_mul_of_nonneg_left ( show ( n : ℝ ) ≥ 1000 by norm_cast ) <| sq_nonneg c ];
      · linarith [ Nat.lt_floor_add_one ( c ^ 2 * 2 * n ^ 2 ) ];
      · exact le_of_lt <| Nat.lt_floor_add_one _;
    rw [ show ( 5 / 2 : ℝ ) = 3 / 2 + 1 by norm_num, Real.rpow_add ] at * <;> norm_num at *;
    · rw [ show p_val n c = ( Nat.floor ( 2 * c ^ 2 * n ^ 2 ) : ℝ ) / ( n.choose 2 ) by rfl, h_m ];
      rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_num [ Nat.choose_two_right ] at *;
      · rw [ Nat.cast_div ] <;> norm_num;
        · rw [ Nat.cast_pred ] <;> linarith;
        · exact even_iff_two_dvd.mp ( Nat.even_mul_pred_self _ );
      · nlinarith only [ h_n, Nat.sub_add_cancel ( by linarith : 1 ≤ n ) ];
    · grind;
    · grind

/-
The probability that U remains independent is at most exp(-3c^4n^{3/2}).
-/
theorem prob_avoid_U_bound_explicit {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_inv_start : MyInvariant G₀ c n m U (G₀, 0))
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_small : c ≤ 1/10)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n) :
  prob_avoid (TheProcess c n m) (TheHit c n m U) m (G₀, 0) ≤ Real.exp (-3 * c^4 * n^(3/2 : ℝ)) := by
    have h_exp : (1 - p_val n c)^m ≤ Real.exp (-p_val n c * m) := by
      rw [ ← Real.rpow_natCast, Real.rpow_def_of_nonneg ] <;> norm_num;
      · split_ifs <;> norm_num at *;
        · norm_num [ ‹m = 0› ];
        · positivity;
        · exact le_trans ( mul_le_mul_of_nonneg_right ( Real.log_le_sub_one_of_pos ( show 0 < 1 - p_val n c from lt_of_le_of_ne ( sub_nonneg_of_le <| by exact p_val_le_one n c h_n_large h_c_small h_c_pos ) <| Ne.symm ‹_› ) ) <| Nat.cast_nonneg _ ) <| by linarith;
      · apply_rules [ p_val_le_one ];
    refine le_trans ( prob_avoid_U_bound G₀ c n m U h_n h_inv_start h_n_large h_c_pos h_c_small h_c_lower h_U_card h_m h_G₀_max_deg ) ?_;
    exact h_exp.trans ( Real.exp_le_exp.mpr <| by linarith [ p_val_mul_m_ge n c m h_n_large h_c_pos h_c_lower h_m ] )

/-
The product of the number of independent sets and the failure probability is less than 1.
-/
theorem union_bound_numeric (n : ℕ) (c : ℝ)
  (h_n : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_small : c ≤ 1/10)
  (h_c_lower_bound : c ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ))
  (h_binom_bound : (n.choose (Nat.floor (5 * c * n)) : ℝ) ≤ 2 ^ (10 * c * n * Real.log (1 / c))) :
  (n.choose (Nat.floor (5 * c * n)) : ℝ) * Real.exp (-3 * c^4 * n^(3/2 : ℝ)) < 1 := by
    have h_num_bound : Real.exp (10 * c * n * Real.log (1 / c) * Real.log 2 - 3 * c^4 * n^(3/2 : ℝ)) < 1 := by
      -- We'll use that $c \geq 2 (\log n)^{1/3} / n^{1/6}$ to show that $10 \ln(2) \log(1/c) < 3 c^3 n^{1/2}$.
      have h_ineq : 10 * Real.log 2 * Real.log (1 / c) < 3 * c^3 * (n : ℝ)^(1/2 : ℝ) := by
        -- Since $c \geq 2 (\log n)^{1/3} / n^{1/6}$, we have $c^3 \geq 8 \log n / n^{1/2}$.
        have h_cubed : c^3 ≥ 8 * Real.log n / (n : ℝ)^(1/2 : ℝ) := by
          have h_cubed : c^3 ≥ (2 * (Real.log n)^(1/3 : ℝ) / (n : ℝ)^(1/6 : ℝ))^3 := by
            gcongr;
          convert h_cubed using 1 ; ring_nf;
          field_simp;
          repeat rw [ ← Real.rpow_natCast ] ; repeat rw [ ← Real.rpow_mul ( by positivity ) ] ; norm_num ; ring_nf;
        -- Since $c \geq 2 (\log n)^{1/3} / n^{1/6}$, we have $\log(1/c) \leq (1/6) \log n$.
        have h_log_bound : Real.log (1 / c) ≤ (1 / 6) * Real.log n := by
          have h_log_bound : 1 / c ≤ (n : ℝ)^(1/6 : ℝ) := by
            rw [ div_le_iff₀ ] <;> try positivity;
            rw [ ge_iff_le, div_le_iff₀ ] at h_c_lower_bound <;> try positivity;
            nlinarith [ Real.one_le_rpow ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ) ( show ( 1 / 6 : ℝ ) ≥ 0 by norm_num ), Real.log_nonneg ( show ( n : ℝ ) ≥ 1 by norm_cast; linarith ), show ( Real.log n : ℝ ) ^ ( 1 / 3 : ℝ ) ≥ 1 by exact Real.one_le_rpow ( show ( Real.log n : ℝ ) ≥ 1 by rw [ ge_iff_le ] ; rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( n : ℝ ) ≥ 1000 by norm_cast ] ) ) ( by norm_num ) ];
          simpa [ Real.log_rpow ( by positivity : 0 < ( n : ℝ ) ) ] using Real.log_le_log ( by positivity ) h_log_bound;
        rw [ ge_iff_le, div_le_iff₀ ] at h_cubed <;> norm_num at *;
        · have := Real.log_two_lt_d9 ; norm_num at * ; nlinarith [ Real.log_pos one_lt_two, Real.log_le_sub_one_of_pos h_c_pos ];
        · positivity;
      rw [ show ( 3 / 2 : ℝ ) = 1 + 1 / 2 by norm_num, Real.rpow_add ] <;> norm_num <;> try positivity;
      field_simp;
      norm_num at * ; linarith;
    convert lt_of_le_of_lt ( mul_le_mul_of_nonneg_right h_binom_bound <| Real.exp_nonneg _ ) _ using 1;
    convert h_num_bound using 1 ; rw [ Real.rpow_def_of_pos ( by positivity ) ] ; rw [ ← Real.exp_add ] ; ring_nf

/-
There exists a next state x such that the sum of failure probabilities is less than 1.
-/
theorem exists_good_next_state {State : Type} (P : Process State) (Bad : Finset (State → Finset State)) (m : ℕ) (s : State)
  (h_progress : (P s).card > 0)
  (h_sum : ∑ H ∈ Bad, prob_avoid P H (m + 1) s < 1) :
  ∃ x ∈ P s, ∑ H ∈ Bad, (if x ∈ H s then 0 else prob_avoid P H m x) < 1 := by
    -- By expanding the definition of prob_avoid for m+1, we can rewrite the sum as (1/|P s|) * sum_{x in P s \ H s} prob_avoid P H m x.
    have h_expand : ∑ H ∈ Bad, prob_avoid P H (m + 1) s = (1 / (P s).card) * ∑ H ∈ Bad, ∑ x ∈ P s, (if x ∈ H s then 0 else prob_avoid P H m x) := by
      have h_expand : ∀ H ∈ Bad, prob_avoid P H (m + 1) s = (1 / (P s).card) * ∑ x ∈ P s, (if x ∈ H s then 0 else prob_avoid P H m x) := by
        intros H hH
        have h_expand : prob_avoid P H (m + 1) s = (∑ x ∈ P s \ H s, prob_avoid P H m x) / (P s).card := by
          exact if_neg ( by aesop );
        simp_all +decide [ div_eq_inv_mul, Finset.sum_ite ];
        exact Or.inl ( by rw [ Finset.sdiff_eq_filter ] );
      rw [ Finset.sum_congr rfl h_expand, Finset.mul_sum _ _ _ ];
    contrapose! h_sum;
    rw [ h_expand, div_mul_eq_mul_div, le_div_iff₀ ] <;> try positivity;
    rw [ Finset.sum_comm ];
    simpa using Finset.sum_le_sum h_sum

/-
Definitions of valid path and hitting condition.
-/
def IsValidPath {State : Type} (P : Process State) (m : ℕ) (s : State) (path : List State) : Prop :=
  match m, path with
  | 0, [x] => x = s
  | k + 1, x :: y :: rest => x = s ∧ y ∈ P x ∧ IsValidPath P k y (y :: rest)
  | _, _ => False

def Hits {State : Type} (H : State → Finset State) (path : List State) : Prop :=
  match path with
  | [] => False
  | [_] => False
  | x :: y :: rest => y ∈ H x ∨ Hits H (y :: rest)

/-
A valid path starting at s must have s as its head.
-/
theorem IsValidPath_eq_cons {State : Type} (P : Process State) (m : ℕ) (s : State) (path : List State)
  (h : IsValidPath P m s path) : ∃ tail, path = s :: tail := by
    -- By definition of IsValidPath, if m is 0, then the path must be [s], so the tail is empty. If m is greater than 0, then the path must start with s, so we can take the tail as the rest of the path.
    induction' m with m ih generalizing s path;
    · rcases path with ( _ | ⟨ x, _ | ⟨ y, path ⟩ ⟩ ) <;> tauto;
    · -- By definition of IsValidPath, if m is k+1, then the path must start with s and have at least two elements.
      obtain ⟨x, y, rest, hx, hy, hrest⟩ : ∃ x y rest, path = x :: y :: rest ∧ x = s ∧ y ∈ P x ∧ IsValidPath P m y (y :: rest) := by
        rcases path with ( _ | ⟨ x, _ | ⟨ y, rest ⟩ ⟩ ) <;> aesop;
      exact ⟨ y :: rest, by simpa [ hy ] using hx ⟩

/-
If y is a next state of s and we have a valid path from y, extending it with s yields a valid path from s.
-/
theorem IsValidPath_succ {State : Type} (P : Process State) (m : ℕ) (s : State) (y : State) (tail : List State)
  (h_mem : y ∈ P s) (h_valid : IsValidPath P m y (y :: tail)) :
  IsValidPath P (m + 1) s (s :: y :: tail) := by
    exact ⟨ rfl, h_mem, h_valid ⟩

/-
If a path hits H, extending it at the head also hits H.
-/
theorem Hits_cons {State : Type} (H : State → Finset State) (x y : State) (tail : List State)
  (h : Hits H (y :: tail)) : Hits H (x :: y :: tail) := by
    exact Or.inr h

/-
If the first edge of a path hits H, then the path hits H.
-/
theorem Hits_head {State : Type} (H : State → Finset State) (x y : State) (tail : List State)
  (h : y ∈ H x) : Hits H (x :: y :: tail) := by
    exact Or.inl h

/-
A valid path starting at s must have s as its head.
-/
theorem IsValidPath_cons {State : Type} (P : Process State) (m : ℕ) (s : State) (path : List State)
  (h : IsValidPath P m s path) : ∃ tail, path = s :: tail := by
    exact IsValidPath_eq_cons P m s path h

/-
If the sum of avoidance probabilities is less than 1, there exists a path hitting all sets.
-/
theorem exists_path_hitting_all {State : Type} (P : Process State) (Bad : Finset (State → Finset State)) (m : ℕ) (s : State)
  (h_progress : ∀ s, (P s).card > 0)
  (h_sum : ∑ H ∈ Bad, prob_avoid P H m s < 1) :
  ∃ path, IsValidPath P m s path ∧ ∀ H ∈ Bad, Hits H path := by
    induction' m with m ih generalizing s Bad P <;> simp_all +decide [ prob_avoid ];
    · exact ⟨ [ s ], by tauto ⟩;
    · -- By `exists_good_next_state`, there exists x in P s such that sum_{H in Bad} (if x in H s then 0 else prob_avoid P H m x) < 1.
      obtain ⟨x, hx_mem, hx_sum⟩ : ∃ x ∈ P s, ∑ H ∈ Bad, (if x ∈ H s then 0 else prob_avoid P H m x) < 1 := by
        convert exists_good_next_state P Bad m s _ _ using 1;
        · exact Finset.card_pos.mpr ( h_progress s );
        · convert h_sum using 1;
          exact Eq.symm ( by rw [ if_neg ( Finset.Nonempty.ne_empty ( h_progress s ) ) ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ prob_avoid ] ; aesop );
      -- Let Bad' = Bad.filter (fun H => x not in H s).
      set Bad' := Bad.filter (fun H => x ∉ H s) with hBad'';
      -- By `sum_filter_bound`, sum_{H in Bad'} prob_avoid P H m x < 1.
      have h_sum_Bad' : ∑ H ∈ Bad', prob_avoid P H m x < 1 := by
        convert hx_sum using 1;
        rw [ Finset.sum_filter ] ; congr ; ext ; aesop;
      obtain ⟨ path', hpath'_valid, hpath'_hits ⟩ := ih P Bad' x h_progress h_sum_Bad';
      -- By `IsValidPath_cons`, path' = x :: tail.
      obtain ⟨tail, ht⟩ : ∃ tail, path' = x :: tail := by
        exact IsValidPath_cons P m x path' hpath'_valid;
      use s :: x :: tail; simp_all +decide [ IsValidPath_succ ] ;
      intro H hH; by_cases hxH : x ∈ H s <;> simp_all +decide [ Hits_cons, Hits_head ] ;

/-
If a state is obtained by adding an edge in U, then U is not independent in that state.
-/
theorem mem_HitGraphsState_implies_not_indep {V : Type} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (U : Finset V) (s t : ProcessState V)
  (h : t ∈ HitGraphsState c n U s) :
  ¬ t.1.IsIndepSet U := by
    rcases Finset.mem_image.1 h with ⟨ e, he, rfl ⟩ ; simp_all +decide [ SimpleGraph.IsIndepSet ] ;
    obtain ⟨ u, hu ⟩ := Finset.mem_image.mp he;
    rcases u with ⟨ v, w ⟩ ; simp_all +decide [ SimpleGraph.fromEdgeSet ] ;
    unfold SimpleGraph.eligiblePairsIn at hu; simp_all +decide
    unfold SimpleGraph.eligibleFinset at hu; simp_all +decide [ SimpleGraph.eligiblePair ] ;
    exact fun h => h hu.1.2.1 hu.1.2.2 ( by aesop ) ( by aesop )

/-
A step in the process increases the graph (in the subgraph sense).
-/
theorem process_step_le {V : Type} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (m : ℕ) (s t : ProcessState V)
  (h : t ∈ TheProcess c n m s) :
  s.1 ≤ t.1 := by
    -- By definition of TheProcess, if t ∈ TheProcess c n m s, then either t = s or t is obtained by adding an edge to s.1.
    by_cases h_eq : s.2 < m;
    · have h_add : ∃ e ∈ s.1.eligibleFinset c n, t.1 = SimpleGraph.fromEdgeSet (s.1.edgeSet ∪ {e}) := by
        have h_next : t.1 ∈ NextGraphs c n s.1 := by
          -- By definition of TheProcess, if t is in TheProcess c n m s, then t.1 is in NextGraphsState c n s.
          have h_t1_next : t ∈ NextGraphsState c n s := by
            unfold TheProcess at h; aesop;
          unfold NextGraphsState at h_t1_next; aesop;
        unfold NextGraphs at h_next; aesop;
      obtain ⟨ e, he₁, he₂ ⟩ := h_add; rw [ he₂ ] ; exact by
        intro v w hvw; simp [SimpleGraph.fromEdgeSet] at hvw ⊢; aesop;;
    · unfold TheProcess at h; aesop;

/-
A "safe" version of the process that ensures there is always at least one next state. If there are valid next graphs, it chooses from them; otherwise, it stays in the current state.
-/
noncomputable def SafeProcess {V : Type} [Fintype V] [DecidableEq V] (c : ℝ) (n : ℕ) (m : ℕ) : Process (ProcessState V) :=
  fun s =>
    let next := if s.2 < m then NextGraphsState c n s else ∅
    if next.card > 0 then next else {s}

/-
A "safe" version of the hit set. If there are valid next graphs, it returns the hit graphs; otherwise, it returns empty.
-/
noncomputable def SafeHit {V : Type} [Fintype V] [DecidableEq V] (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V) : ProcessState V → Finset (ProcessState V) :=
  fun s =>
    let next := if s.2 < m then NextGraphsState c n s else ∅
    if next.card > 0 then HitGraphsState c n U s else ∅

/-
The safe process always has at least one next state (either a valid next graph or the current state itself).
-/
theorem SafeProcess_progress {V : Type} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (m : ℕ) (s : ProcessState V) :
  (SafeProcess c n m s).card > 0 := by
    unfold SafeProcess; aesop;

/-
If the number of edges is less than m, the safe process is identical to the original process (NextGraphsState).
-/
theorem SafeProcess_eq_NextGraphsState {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (s : ProcessState V)
  (h_inv : MyInvariant G₀ c n m U s)
  (h_lt : s.2 < m) :
  SafeProcess c n m s = NextGraphsState c n s := by
    -- Since there's at least one next graph, the safe process will choose from them.
    have h_next_graph : ∃ G' ∈ NextGraphs c n s.1, True := by
      have h_card : (NextGraphs c n s.1).card > 0 := by
        have h_next_nonempty : (HitGraphs c n s.1 U).card ≥ Nat.floor (2 * c^2 * n^2) := by
          convert eligible_pairs_count_lower_bound_ceil G₀ s.1 n c U h_n h_inv.1 h_inv.2.2.1 h_U_card h_G₀_max_deg ( show ∀ v, ( s.1.degree v : ℝ ) ≤ Nat.ceil ( 2 * c * Real.sqrt n ) from ?_ ) ( show ( s.1.edgeFinset \ G₀.edgeFinset ).card ≤ Nat.floor ( c^2 * n^(3/2 : ℝ)) from ?_ ) h_c_pos h_n_large h_c_lower using 1;
          · convert card_HitGraphs_eq c n s.1 U using 1;
          · exact_mod_cast h_inv.2.2.2.1;
          · cases h_inv ; aesop;
        refine' pos_of_gt ( lt_of_lt_of_le _ ( h_next_nonempty.trans ( Finset.card_mono <| hit_subset_next c n s.1 U ) ) );
        exact 0;
        exact Nat.floor_pos.mpr ( by nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, show ( c : ℝ ) ^ 2 * n ≥ 16 by nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, Real.mul_self_sqrt ( Nat.cast_nonneg n ) ] ] );
      exact Exists.elim ( Finset.card_pos.mp h_card ) fun x hx => ⟨ x, hx, trivial ⟩;
    -- Since there's at least one next graph, the safe process will choose from them, making it equal to the original process.
    unfold SafeProcess
    simp
    simp_all +decide [ NextGraphsState ]
    exact Finset.Nonempty.ne_empty ⟨ _, h_next_graph.choose_spec ⟩

/-
If the number of edges is less than m, the safe hit set is identical to the original hit set (HitGraphsState).
-/
theorem SafeHit_eq_HitGraphsState {V : Type} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V) (s : ProcessState V) (h_lt : s.2 < m) :
  SafeHit c n m U s = HitGraphsState c n U s := by
    -- Since $s.2 < m$, the safe process is just the next graphs state, and the hit set is just the hit graphs state. Therefore, they are equal.
    simp [SafeHit, h_lt];
    intro h_empty_next
    have h_empty_hit : HitGraphsState c n U s ⊆ ∅ := by
      exact h_empty_next ▸ HitGraphsState_subset_NextGraphsState c n U s |> fun h => h.trans ( by simp +decide ) ;
    exact Eq.symm (by
    exact Finset.Subset.antisymm h_empty_hit ( Finset.empty_subset _ ))

/-
The SafeProcess and TheProcess are identical on states satisfying the invariant.
-/
theorem SafeProcess_eq_TheProcess {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (s : ProcessState V)
  (h_inv : MyInvariant G₀ c n m U s) :
  SafeProcess c n m s = TheProcess c n m s := by
    -- By definition of SafeProcess and TheProcess, if s.2 < m, both are NextGraphsState. If s.2 ≥ m, both are {s}.
    by_cases h_lt : s.2 < m;
    · convert SafeProcess_eq_NextGraphsState G₀ c n m U h_n h_n_large h_c_pos h_c_lower h_U_card h_m h_G₀_max_deg s h_inv h_lt using 1;
      exact if_pos h_lt;
    · unfold SafeProcess TheProcess; simp +decide [ h_lt ] ;

/-
The avoidance probability is the same for the safe process and the original process, for any state satisfying the invariant and consistent with the remaining steps.
-/
theorem prob_avoid_eq_general {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_U_card : U.card = Nat.floor (5 * c * n))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n) :
  ∀ k, ∀ s, MyInvariant G₀ c n m U s → s.2 + k = m →
  prob_avoid (SafeProcess c n m) (SafeHit c n m U) k s = prob_avoid (TheProcess c n m) (TheHit c n m U) k s := by
    intro k s hs hk; induction' k with k ih generalizing s; simp_all +decide [ prob_avoid ] ;
    -- By definition of `prob_avoid`, we have:
    simp [prob_avoid];
    rw [ SafeProcess_eq_TheProcess, SafeHit_eq_HitGraphsState ] <;> try omega;
    congr! 2;
    refine' Finset.sum_congr _ _ <;> simp +contextual [ *, TheProcess, TheHit ];
    · grind;
    · intro x hx hx'; split_ifs at hx hx' <;> simp_all +decide [ TheProcess ] ;
      apply ih x _ _;
      · apply invariant_preservation;
        exact hs;
        unfold TheProcess TheHit; aesop;
      · -- Since $x$ is in the next graphs state of $s$, we have $x.2 = s.2 + 1$.
        have hx2 : x.2 = s.2 + 1 := by
          unfold NextGraphsState at hx; aesop;
        linarith

/-
The set of all subsets of vertices with size equal to floor(5cn).
-/
noncomputable def RelevantUs {V : Type} [Fintype V] (c : ℝ) (n : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun U => U.card = Nat.floor (5 * c * n))

/-
For any relevant U, the failure probability of the safe process is bounded by the exponential term.
-/
theorem prob_avoid_safe_bound {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (h_n : Fintype.card V = n)
  (h_inv_start : MyInvariant G₀ c n m U (G₀, 0))
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_small : c ≤ 1/10)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_c_lower_bound : c ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (h_U_mem : U ∈ RelevantUs c n) :
  prob_avoid (SafeProcess c n m) (SafeHit c n m U) m (G₀, 0) ≤ Real.exp (-3 * c^4 * n^(3/2 : ℝ)) := by
    convert prob_avoid_U_bound_explicit G₀ c n m U h_n h_inv_start h_n_large h_c_pos h_c_small h_c_lower _ h_m h_G₀_max_deg using 1;
    · convert prob_avoid_eq_general G₀ c n m U h_n h_n_large h_c_pos h_c_lower _ h_m h_G₀_max_deg m ( G₀, 0 ) h_inv_start ( by linarith ) using 1;
      exact Finset.mem_filter.mp h_U_mem |>.2;
    · unfold RelevantUs at h_U_mem; aesop;

/-
A base invariant that does not depend on a specific independent set U. It ensures the graph remains triangle-free, satisfies the degree bound, and tracks the number of added edges.
-/
def BaseInvariant {V : Type} [Fintype V] [DecidableEq V] (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (s : ProcessState V) : Prop :=
  G₀ ≤ s.1 ∧
  s.1.CliqueFree 3 ∧
  (∀ v, s.1.degree v ≤ Nat.ceil (2 * c * Real.sqrt n)) ∧
  (s.1.edgeFinset \ G₀.edgeFinset).card = s.2 ∧
  s.2 ≤ m

/-
Adding an eligible edge preserves the base invariant.
-/
theorem BaseInvariant_preserves_step {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ)
  (s : ProcessState V) (g : ProcessState V) (e : Sym2 V)
  (h_inv : BaseInvariant G₀ c n m s)
  (h_eligible : s.1.eligiblePair c n e.out.1 e.out.2)
  (h_g1 : g.1 = SimpleGraph.fromEdgeSet (s.1.edgeSet ∪ {e}))
  (h_g2 : g.2 = s.2 + 1)
  (h_lt_m : s.2 < m) :
  BaseInvariant G₀ c n m g := by
    refine' ⟨ _, _, _, _, _ ⟩;
    · exact h_g1 ▸ le_trans h_inv.1 ( by aesop_cat );
    · -- Since $e$ is eligible, adding it to $s.1$ does not create any new triangles.
      have h_triangle_free : ∀ (G : SimpleGraph V), G.CliqueFree 3 → ∀ (u v : V), G.eligiblePair c n u v → (SimpleGraph.fromEdgeSet (G.edgeSet ∪ {Sym2.mk (u, v)})).CliqueFree 3 := by
        intros G hG u v h_eligible;
        -- If there is a triangle in the new graph, it must involve the edge (u, v).
        intro T hT
        by_cases h_triangle : u ∈ T ∧ v ∈ T;
        · have h_triangle : T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → (x = u ∧ y = v) ∨ (x = v ∧ y = u) ∨ G.Adj x y := by
            have := hT.2; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
            intro x hx y hy hxy; have := hT hx hy hxy; aesop;
          have h_triangle : ∃ w ∈ T, w ≠ u ∧ w ≠ v := by
            exact Exists.imp ( by aesop ) ( Finset.exists_mem_ne ( show 1 < Finset.card ( T.erase u ) from by rw [ Finset.card_erase_of_mem ( by tauto ), h_triangle.1 ] ; decide ) v );
          obtain ⟨ w, hw₁, hw₂, hw₃ ⟩ := h_triangle;
          have := h_triangle.2 w hw₁ u ( by tauto ) ; have := h_triangle.2 w hw₁ v ( by tauto ) ; simp_all +decide [ SimpleGraph.eligiblePair ] ;
          exact h_eligible.2.2.2.2 w ( by tauto ) ( by tauto );
        · have h_triangle_free : ∀ (T : Finset V), T.card = 3 → (SimpleGraph.fromEdgeSet (G.edgeSet ∪ {Sym2.mk (u, v)})).IsNClique 3 T → u ∈ T ∧ v ∈ T := by
            intros T hT_card hT_clique
            have h_triangle_free : ∀ (x y z : V), x ≠ y → x ≠ z → y ≠ z → (SimpleGraph.fromEdgeSet (G.edgeSet ∪ {Sym2.mk (u, v)})).Adj x y → (SimpleGraph.fromEdgeSet (G.edgeSet ∪ {Sym2.mk (u, v)})).Adj x z → (SimpleGraph.fromEdgeSet (G.edgeSet ∪ {Sym2.mk (u, v)})).Adj y z → (u = x ∧ v = y) ∨ (u = x ∧ v = z) ∨ (u = y ∧ v = x) ∨ (u = y ∧ v = z) ∨ (u = z ∧ v = x) ∨ (u = z ∧ v = y) := by
              intros x y z hxy hxz hyz hxy_adj hxz_adj hyz_adj
              have h_triangle_free : ¬G.Adj x y ∨ ¬G.Adj x z ∨ ¬G.Adj y z := by
                contrapose! hG;
                simp_all +decide [ SimpleGraph.CliqueFree ];
                exact ⟨ { x, y, z }, by simp +decide [ *, SimpleGraph.isNClique_iff ] ⟩;
              cases h_triangle_free <;> simp_all +decide [ SimpleGraph.fromEdgeSet ];
              · grind +ring;
              · grind;
            rcases Finset.card_eq_three.mp hT_card with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; simp_all +decide [ SimpleGraph.isNClique_iff ];
            grind;
          exact h_triangle <| h_triangle_free T ( by simpa using hT.2 ) hT;
      convert h_triangle_free s.1 h_inv.2.1 _ _ h_eligible using 1;
      cases e using Quot.inductionOn ; aesop;
    · have := h_inv.2.2.1;
      convert degree_bound_preserved s.1 c n _ _ h_eligible _;
      · cases e using Sym2.inductionOn ; aesop;
      · assumption;
    · have := h_inv.2.2.2.1;
      convert invariant_preservation_step_card G₀ c n s g e _ _ h_eligible h_g1 h_g2 using 1;
      · exact h_inv.1;
      · exact this;
    · grind

/-
If a path hits a target set H, then there exists a step (x, y) in the path such that y is in H(x).
-/
theorem Hits_implies_exists_step {State : Type} (H : State → Finset State) (path : List State)
  (h_hits : Hits H path) :
  ∃ x y, List.IsInfix [x, y] path ∧ y ∈ H x := by
    induction' k : path.length using Nat.strong_induction_on with k ih generalizing path; rcases path with ( _ | ⟨ x, _ | ⟨ y, path ⟩ ⟩ ) <;> simp_all +decide [ List.IsInfix ] ;
    · cases h_hits;
    · cases h_hits;
    · by_cases h : y ∈ H x <;> simp_all +decide [ Hits ];
      · exact ⟨ x, y, ⟨ [ ], path, rfl ⟩, h ⟩;
      · grind

/-
A step in the safe process results in a graph that contains the original graph as a subgraph.
-/
theorem SafeProcess_step_le {V : Type} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (m : ℕ) (s t : ProcessState V)
  (h : t ∈ SafeProcess c n m s) :
  s.1 ≤ t.1 := by
    have h_subgraph : ∀ s t : ProcessState V, t ∈ SafeProcess c n m s → s.1 ≤ t.1 := by
      intros s t ht;
      by_cases h : t ∈ NextGraphsState c n s <;> simp_all +decide [ SafeProcess ];
      · convert process_step_le c n m s t _;
        unfold TheProcess; aesop;
      · split_ifs at ht <;> aesop;
    exact h_subgraph s t h

/-
If a path is valid with respect to a process P, then it forms a chain where each element is in the process of the previous element.
-/
theorem IsValidPath_implies_Chain {State : Type} (P : Process State) (m : ℕ) (s : State) (path : List State)
  (h : IsValidPath P m s path) :
  List.IsChain (fun a b => b ∈ P a) path := by
    induction' m with m ih generalizing s path <;> rcases path with ( _ | ⟨ x, _ | ⟨ y, path ⟩ ⟩ ) <;> simp_all +decide
    · cases h;
    · cases h ; aesop

/-
If a path is valid for the safe process, then the graphs in the path form a chain with respect to the subgraph relation.
-/
theorem List_Chain_le_of_SafeProcess {V : Type} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (m : ℕ) (path : List (ProcessState V))
  (G₀ : SimpleGraph V)
  (h_valid : IsValidPath (SafeProcess c n m) m (G₀, 0) path) :
  List.IsChain (fun s t => s.1 ≤ t.1) path := by
    have h_chain : List.IsChain (fun a b => b ∈ SafeProcess c n m a) path := by
      exact IsValidPath_implies_Chain (SafeProcess c n m) m (G₀, 0) path h_valid;
    have h_chain_le : ∀ {a b : ProcessState V}, b ∈ SafeProcess c n m a → a.1 ≤ b.1 := by
      exact fun {a b} a_1 => SafeProcess_step_le c n m a b a_1;
    exact List.IsChain.imp ( by tauto ) h_chain

/-
A valid path is never empty.
-/
theorem IsValidPath_ne_nil {State : Type} (P : Process State) (m : ℕ) (s : State) (path : List State)
  (h : IsValidPath P m s path) :
  path ≠ [] := by
    cases m <;> cases path <;> tauto

/-
In a list that forms a chain under a transitive and reflexive relation, every element is related to the last element.
-/
theorem Chain_rel_last {α : Type*} (r : α → α → Prop) (l : List α) (h_chain : List.IsChain r l) (x : α) (hx : x ∈ l) (h_ne : l ≠ []) (h_refl : Reflexive r) (h_trans : Transitive r) : r x (l.getLast h_ne) := by
  induction' l using List.reverseRecOn with l IH generalizing x; aesop;
  rw [ List.isChain_append ] at h_chain;
  cases l <;> aesop

/-
For any state x in a valid path, the graph in x is a subgraph of the final graph in the path.
-/
theorem Path_sublist_le {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (path : List (ProcessState V))
  (h_valid : IsValidPath (SafeProcess c n m) m (G₀, 0) path)
  (x : ProcessState V) (hx : x ∈ path) :
  x.1 ≤ (path.getLastD (G₀, 0)).1 := by
    have h_chain : List.IsChain (fun s t => s.1 ≤ t.1) path := by
      exact List_Chain_le_of_SafeProcess c n m path G₀ h_valid;
    have h_last : path ≠ [] := by
      exact IsValidPath_ne_nil (SafeProcess c n m) m (G₀, 0) path h_valid;
    have h_last : x.1 ≤ (path.getLast h_last).1 := by
      have h_chain_last : List.IsChain (fun s t => s.1 ≤ t.1) path := h_chain
      have h_x_in_path : x ∈ path := hx
      have h_last_ne : path ≠ [] := h_last
      apply Chain_rel_last (fun s t => s.1 ≤ t.1) path h_chain_last x h_x_in_path h_last_ne (by
      exact fun _ => le_rfl) (by
      exact fun a b c hab hbc => le_trans hab hbc);
    cases path <;> aesop

/-
The safe hit set is a subset of the original hit set.
-/
theorem SafeHit_subset_HitGraphsState {V : Type} [Fintype V] [DecidableEq V]
  (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V) (s : ProcessState V) :
  SafeHit c n m U s ⊆ HitGraphsState c n U s := by
    unfold SafeHit; aesop;

/-
If a set is independent in a graph H, it is also independent in any subgraph G of H.
-/
theorem SimpleGraph.IsIndepSet_of_le {V : Type*} (G H : SimpleGraph V) (s : Set V)
  (h_le : G ≤ H) (h_indep : H.IsIndepSet s) : G.IsIndepSet s := by
    intro u hu v hv huv; have := h_indep hu hv; aesop;

/-
If every set of vertices of size k is not an independent set, then the independence number of the graph is strictly less than k.
-/
theorem indepNum_lt_of_forall_not_indep {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ)
  (h : ∀ U : Finset V, U.card = k → ¬ G.IsIndepSet U) :
  G.indepNum < k := by
    have h_max : ∀ U : Set V, G.IsIndepSet U → U.Finite → U.ncard ≤ k - 1 := by
      intro U hU hU_fin
      by_contra h_contra;
      obtain ⟨U', hU'_card, hU'_subset⟩ : ∃ U' : Finset V, U'.card = k ∧ U' ⊆ hU_fin.toFinset := by
        have h_card : k ≤ hU_fin.toFinset.card := by
          rw [ ← Set.ncard_coe_finset, hU_fin.coe_toFinset ] ; omega;
        exact Exists.imp ( by aesop ) ( Finset.exists_subset_card_eq h_card );
      exact h U' hU'_card ( hU.mono fun x hx => by simpa using hU'_subset hx );
    contrapose! h_max;
    have := G.exists_isNIndepSet_indepNum;
    obtain ⟨ s, hs ⟩ := this;
    exact ⟨ s, hs.1, s.finite_toSet, by simpa [ hs.2 ] using Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) zero_lt_one |> LT.lt.trans_le <| h_max ⟩

/-
The SafeProcess preserves the BaseInvariant.
-/
theorem SafeProcess_preserves_BaseInvariant {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ)
  (s g : ProcessState V)
  (h_inv : BaseInvariant G₀ c n m s)
  (h_step : g ∈ SafeProcess c n m s) :
  BaseInvariant G₀ c n m g := by
    unfold SafeProcess at h_step;
    split_ifs at h_step <;> simp_all +decide [ NextGraphsState ];
    split_ifs at h_step <;> simp_all +decide [ NextGraphs ];
    rcases h_step with ⟨ e, he₁, rfl ⟩;
    apply_rules [ BaseInvariant_preserves_step ];
    · convert he₁ using 1;
      simp +decide [ SimpleGraph.eligibleFinset ];
      conv_rhs => rw [ ← Quot.out_eq e ] ;
      exact Eq.to_iff rfl;
    · ext; simp [SimpleGraph.fromEdgeSet]

/-
If a valid path hits the set of states adding an edge in U, then U is not an independent set in the final graph of the path.
-/
theorem Hits_implies_not_indep {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) (U : Finset V)
  (path : List (ProcessState V))
  (h_valid : IsValidPath (SafeProcess c n m) m (G₀, 0) path)
  (h_hit : Hits (SafeHit c n m U) path) :
  ¬ (path.getLastD (G₀, 0)).1.IsIndepSet U := by
    have h_exists := Hits_implies_exists_step (SafeHit c n m U) path h_hit
    rcases h_exists with ⟨x, y, h_infix, h_y_in_hit⟩
    have h_y_in_path : y ∈ path := by
      rcases h_infix with ⟨s, t, rfl⟩
      simp only [List.mem_append, List.mem_cons]
      tauto
    have h_y_le_last : y.1 ≤ (path.getLastD (G₀, 0)).1 := Path_sublist_le G₀ c n m path h_valid y h_y_in_path
    have h_y_not_indep : ¬ y.1.IsIndepSet U := by
      apply mem_HitGraphsState_implies_not_indep c n U x y
      apply SafeHit_subset_HitGraphsState c n m U x
      exact h_y_in_hit
    intro h_last_indep
    apply h_y_not_indep
    apply SimpleGraph.IsIndepSet_of_le y.1 (path.getLastD (G₀, 0)).1 U h_y_le_last h_last_indep

/-
If a path is valid and the process preserves an invariant, then the invariant holds for the last state of the path.
-/
theorem IsValidPath_preserves_BaseInvariant {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ)
  (path : List (ProcessState V))
  (h_valid : IsValidPath (SafeProcess c n m) m (G₀, 0) path)
  (h_start : BaseInvariant G₀ c n m (G₀, 0)) :
  BaseInvariant G₀ c n m (path.getLastD (G₀, 0)) := by
    -- By induction on the length of the valid path, we can show that the base invariant holds for all states in the path.
    have h_ind : ∀ (k : ℕ) (s : ProcessState V) (path : List (ProcessState V)), IsValidPath (SafeProcess c n m) k s path → BaseInvariant G₀ c n m s → BaseInvariant G₀ c n m (path.getLastD (G₀, 0)) := by
      intro k;
      induction' k with k ih generalizing V;
      · intro s path h_valid h_start; rcases path with ( _ | ⟨ x, _ | ⟨ y, path ⟩ ⟩ ) <;> simp_all +decide ;
        · cases h_valid ; aesop;
        · cases h_valid;
      · intro s path h_valid h_inv; rcases path with ( _ | ⟨ x, _ | ⟨ y, path ⟩ ⟩ ) <;> simp_all +decide ;
        · exact False.elim h_valid;
        · rcases h_valid with ⟨ rfl, hxy, hpath ⟩;
          exact ih G₀ _ h_valid h_start _ _ hpath ( SafeProcess_preserves_BaseInvariant G₀ c n m x y h_inv hxy );
    exact h_ind m _ _ h_valid h_start

/-
Defining the set of relevant independent sets in G0 and the corresponding hit sets.
-/
noncomputable def RelevantUsG0 {V : Type} [Fintype V] [DecidableEq V] (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) : Finset (Finset V) :=
  (Finset.univ.filter (fun U : Finset V => U.card = Nat.floor (5 * c * n) ∧ G₀.IsIndepSet U))

noncomputable def SafeAllHitsG0 {V : Type} [Fintype V] [DecidableEq V] (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ) : Finset (ProcessState V → Finset (ProcessState V)) :=
  (RelevantUsG0 G₀ c n).image (fun U => SafeHit c n m U)

/-
The sum of failure probabilities over all relevant independent sets in G0 is less than 1.
-/
theorem sum_relevant_G0_lt_one {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_small : c ≤ 1/10)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_c_lower_bound : c ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (h_clique_free : G₀.CliqueFree 3)
  (h_binom_bound : (n.choose (Nat.floor (5 * c * n)) : ℝ) ≤ 2 ^ (10 * c * n * Real.log (1 / c))) :
  ∑ H ∈ SafeAllHitsG0 G₀ c n m, prob_avoid (SafeProcess c n m) H m (G₀, 0) < 1 := by
    apply lt_of_le_of_lt;
    swap;
    rotate_right;
    exact ( Nat.choose n ( Nat.floor ( 5 * c * n ) ) : ℝ ) * Real.exp ( -3 * c ^ 4 * n ^ ( 3 / 2 : ℝ ) );
    · convert union_bound_numeric n c h_n_large h_c_pos h_c_small h_c_lower_bound using 1
      aesop
    · have h_sum_bound : ∀ U ∈ RelevantUsG0 G₀ c n, prob_avoid (SafeProcess c n m) (SafeHit c n m U) m (G₀, 0) ≤ Real.exp (-3 * c^4 * n^(3/2 : ℝ)) := by
        intros U hU;
        apply prob_avoid_safe_bound;
        all_goals norm_num [ RelevantUsG0 ] at *;
        all_goals try assumption;
        · constructor;
          · exact le_rfl;
          · exact ⟨ h_clique_free, hU.2, fun v => Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil ( 2 * c * Real.sqrt n ), Real.mul_self_sqrt ( Nat.cast_nonneg n ), h_G₀_max_deg v ], by simp +decide, by simp +decide [ h_m ] ⟩;
        · exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hU.1 ⟩;
      refine' le_trans _ ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| show Finset.card ( RelevantUsG0 G₀ c n ) ≤ Nat.choose n ( Nat.floor ( 5 * c * n ) ) from _ ) <| Real.exp_nonneg _ );
      · refine' le_trans ( Finset.sum_le_sum fun x hx => _ ) _;
        use fun x => Real.exp ( -3 * c ^ 4 * n ^ ( 3 / 2 : ℝ ) );
        · unfold SafeAllHitsG0 at hx; aesop;
        · simp +zetaDelta at *;
          exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_image_le ) ( Real.exp_nonneg _ );
      · have h_card_bound : Finset.card (RelevantUsG0 G₀ c n) ≤ Finset.card (Finset.powersetCard (Nat.floor (5 * c * n)) (Finset.univ : Finset V)) := by
          exact Finset.card_le_card fun x hx => by unfold RelevantUsG0 at hx; aesop;
        aesop

/-
There exists a valid path in the safe process starting from G0 that hits all safe hit sets corresponding to independent sets in G0.
-/
theorem exists_good_path_G0 {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_small : c ≤ 1/10)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_c_lower_bound : c ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ))
  (h_m : m = Nat.floor (c^2 * n^(3/2 : ℝ)))
  (h_G₀_max_deg : ∀ v, (G₀.degree v : ℝ) ≤ c * Real.sqrt n)
  (h_clique_free : G₀.CliqueFree 3)
  (h_binom_bound : (n.choose (Nat.floor (5 * c * n)) : ℝ) ≤ 2 ^ (10 * c * n * Real.log (1 / c))) :
  ∃ path, IsValidPath (SafeProcess c n m) m (G₀, 0) path ∧ ∀ H ∈ SafeAllHitsG0 G₀ c n m, Hits H path := by
    have h_sum_lt := sum_relevant_G0_lt_one G₀ c n m h_n h_n_large h_c_pos h_c_small h_c_lower h_c_lower_bound h_m h_G₀_max_deg h_clique_free h_binom_bound
    apply exists_path_hitting_all
    · intro s; apply SafeProcess_progress
    · exact h_sum_lt

/-
If a valid path hits all safe hit sets for G0, then the independence number of the final graph is less than 5cn.
-/
theorem final_graph_indepNum_bound_G0 {V : Type} [Fintype V] [DecidableEq V]
  (G₀ : SimpleGraph V) (c : ℝ) (n : ℕ) (m : ℕ)
  (path : List (ProcessState V))
  (h_valid : IsValidPath (SafeProcess c n m) m (G₀, 0) path)
  (h_hits_all : ∀ H ∈ SafeAllHitsG0 G₀ c n m, Hits H path) :
  (path.getLastD (G₀, 0)).1.indepNum < Nat.floor (5 * c * n) := by
    apply_rules [ indepNum_lt_of_forall_not_indep ];
    intro U hU_card
    by_cases hU_indep : G₀.IsIndepSet U;
    · apply Hits_implies_not_indep G₀ c n m U path h_valid (by
      exact h_hits_all _ <| Finset.mem_image.mpr ⟨ U, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hU_card, hU_indep ⟩, rfl ⟩);
    · contrapose! hU_indep;
      have h_subgraph : G₀ ≤ (path.getLastD (G₀, 0)).1 := by
        apply (Path_sublist_le G₀ c n m path h_valid (G₀, 0) (by
        obtain ⟨ tail, rfl ⟩ := IsValidPath_cons _ _ _ _ h_valid; simp +decide ;));
      exact SimpleGraph.IsIndepSet_of_le G₀ (path.getLastD (G₀, 0)).1 (↑U) h_subgraph hU_indep

/-
There exists a triangle-free supergraph G_m of G with independence number at most 5cn.
-/
theorem exists_Gm_bounded_indep {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (n : ℕ) (c : ℝ)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_small : c ≤ 1/10)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_c_lower_bound : c ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ))
  (h_max_deg : ∀ v, (G.degree v : ℝ) ≤ c * Real.sqrt n)
  (h_clique_free : G.CliqueFree 3)
  (h_binom_bound : (n.choose (Nat.floor (5 * c * n)) : ℝ) ≤ 2 ^ (10 * c * n * Real.log (1 / c))) :
  ∃ G_m : SimpleGraph V, G ≤ G_m ∧ G_m.CliqueFree 3 ∧ (G_m.indepNum : ℝ) ≤ 5 * c * n := by
    -- Convert the max degree hypothesis to use the Classical instance.
    have h_max_deg_classical : ∀ v, @SimpleGraph.degree V G v (@SimpleGraph.neighborSetFintype V G _ (Classical.decRel G.Adj) v) ≤ c * Real.sqrt n := by
      convert h_max_deg using 1;
      convert Iff.rfl;
    -- Apply `exists_good_path_G0` to obtain a valid path `path` hitting all safe hit sets.
    obtain ⟨path, h_valid, h_hits_all⟩ := exists_good_path_G0 G c n (Nat.floor (c^2 * n^(3/2 : ℝ))) h_n h_n_large h_c_pos h_c_small h_c_lower h_c_lower_bound rfl h_max_deg_classical h_clique_free h_binom_bound;
    -- By `IsValidPath_preserves_BaseInvariant`, `G_m` satisfies `BaseInvariant`, which implies `G ≤ G_m` and `G_m.CliqueFree 3`.
    have h_base_invariant : BaseInvariant G c n (Nat.floor (c^2 * n^(3/2 : ℝ))) (path.getLastD (G, 0)) := by
      apply IsValidPath_preserves_BaseInvariant G c n (Nat.floor (c^2 * n^(3/2 : ℝ))) path h_valid;
      refine' ⟨ le_rfl, h_clique_free, _, _, _ ⟩ <;> norm_num;
      exact fun v => Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ Nat.le_ceil ( 2 * c * Real.sqrt n ), Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, h_max_deg_classical v ] ;
    -- By `final_graph_indepNum_bound_G0`, `G_m.indepNum < floor(5cn)`.
    have h_indepNum_bound : (path.getLastD (G, 0)).1.indepNum < Nat.floor (5 * c * n) := by
      apply final_graph_indepNum_bound_G0 G c n (Nat.floor (c^2 * n^(3/2 : ℝ))) path h_valid h_hits_all;
    exact ⟨ _, h_base_invariant.1, h_base_invariant.2.1, le_trans ( Nat.cast_le.mpr h_indepNum_bound.le ) ( Nat.floor_le ( by positivity ) ) ⟩

/-
Theorem 1.2: Given a triangle-free graph G with bounded max degree, we can add edges to obtain a triangle-free graph of diameter 2 with a bounded number of edges.
-/
theorem theorem_1_2 {V : Type} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  (n : ℕ) (c : ℝ)
  (h_n : Fintype.card V = n)
  (h_n_large : n ≥ 1000)
  (h_c_pos : c > 0)
  (h_c_small : c ≤ 1/10)
  (h_c_lower : c * Real.sqrt n ≥ 4)
  (h_c_lower_bound : c ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ))
  (h_max_deg : ∀ v, (G.degree v : ℝ) ≤ c * Real.sqrt n)
  (h_clique_free : G.CliqueFree 3)
  (h_binom_bound : (n.choose (Nat.floor (5 * c * n)) : ℝ) ≤ 2 ^ (10 * c * n * Real.log (1 / c))) :
  ∃ G' : SimpleGraph V, G ≤ G' ∧ G'.CliqueFree 3 ∧
    (∀ x y : V, x ≠ y → G'.Adj x y ∨ ∃ z, G'.Adj x z ∧ G'.Adj z y) ∧
    (G'.edgeFinset.card : ℝ) ≤ 2.5 * c * n ^ 2 := by
      have := exists_Gm_bounded_indep G n c;
      specialize this h_n h_n_large h_c_pos h_c_small h_c_lower h_c_lower_bound h_max_deg h_clique_free h_binom_bound;
      exact SimpleGraph.deterministic_reduction G n c h_n this

theorem erdos_134
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 →
      (∀ v : Fin n, (G.degree v : ℝ) < Real.rpow (n : ℝ) ((1 : ℝ) / 2 - ε)) →
      ∃ H : SimpleGraph (Fin n),
        G ≤ H ∧
        H.CliqueFree 3 ∧
        (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
        ((H.edgeFinset \ G.edgeFinset).card : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
  revert @‹_›;
  intro hδ_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (n : ℝ) ^ (-ε) ≤ (min (1 / 10) (δ / 3)) ∧ (2 * (Real.log n) ^ (1 / 3 : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ)) ≤ (min (1 / 10) (δ / 3)) ∧ (min (1 / 10) (δ / 3)) * Real.sqrt n ≥ 4 := by
    have h_lim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n : ℕ => 2 * (Real.log n) ^ (1 / 3 : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun n : ℕ => (min (1 / 10) (δ / 3)) * Real.sqrt n) Filter.atTop Filter.atTop := by
      refine' ⟨ _, _, _ ⟩;
      · simpa using tendsto_rpow_neg_atTop hε |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop;
      · -- We can factor out the constant $2$ and use the fact that $\frac{(\log n)^{1/3}}{n^{1/6}}$ tends to $0$ as $n$ tends to infinity.
        have h_factor : Filter.Tendsto (fun n : ℕ => (Real.log n) ^ (1 / 3 : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
          -- Let $y = \log x$, therefore the expression becomes $\frac{y^{1/3}}{e^{y/6}}$.
          suffices h_log : Filter.Tendsto (fun y : ℝ => y ^ (1 / 3 : ℝ) / Real.exp (y / 6)) Filter.atTop (nhds 0) by
            have := h_log.comp Real.tendsto_log_atTop;
            refine this.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx ; norm_num [ Real.rpow_def_of_pos, mul_div, hx ];
          -- Let $z = \frac{y}{6}$, therefore the expression becomes $\frac{(6z)^{1/3}}{e^z}$.
          suffices h_z : Filter.Tendsto (fun z : ℝ => (6 * z) ^ (1 / 3 : ℝ) / Real.exp z) Filter.atTop (nhds 0) by
            convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 6⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
          -- We can factor out the constant $6^{1/3}$ and use the fact that $z^{1/3} / e^z$ tends to $0$ as $z$ tends to infinity.
          suffices h_factor : Filter.Tendsto (fun z : ℝ => z ^ (1 / 3 : ℝ) / Real.exp z) Filter.atTop (nhds 0) by
            have h_factor : Filter.Tendsto (fun z : ℝ => 6 ^ (1 / 3 : ℝ) * (z ^ (1 / 3 : ℝ) / Real.exp z)) Filter.atTop (nhds 0) := by
              simpa using h_factor.const_mul _;
            refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with z hz using by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring );
          have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
          refine' squeeze_zero_norm' _ this;
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ), Real.exp_neg ] ; exact mul_le_mul_of_nonneg_right ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show ( 1 : ℝ ) / 3 ≤ 1 by norm_num ) ) ( by norm_num ) ) ( by positivity ) ;
        simpa [ mul_div_assoc ] using h_factor.const_mul 2;
      · exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
    exact Filter.eventually_atTop.mp ( h_lim.1.eventually ( ge_mem_nhds <| by positivity ) |> Filter.Eventually.and <| h_lim.2.1.eventually ( ge_mem_nhds <| by positivity ) |> Filter.Eventually.and <| h_lim.2.2.eventually_ge_atTop 4 );
  use N + 1000;
  intro n hn G hG h_deg
  obtain ⟨G', hG'_sub, hG'_clique_free, hG'_diameter, hG'_edges⟩ : ∃ G' : SimpleGraph (Fin n), G ≤ G' ∧ G'.CliqueFree 3 ∧ (∀ x y : Fin n, x ≠ y → G'.Adj x y ∨ ∃ z, G'.Adj x z ∧ G'.Adj z y) ∧ (G'.edgeFinset.card : ℝ) ≤ 2.5 * (min (1 / 10) (δ / 3)) * n ^ 2 := by
    convert theorem_1_2 G n ( Min.min ( 1 / 10 ) ( δ / 3 ) ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ using 1;
    any_goals tauto;
    any_goals linarith [ hN n ( by linarith ) ];
    · have := binom_entropy_bound n ( Min.min ( 1 / 10 ) ( δ / 3 ) ) ( by positivity ) ( by
        nlinarith [ hN n ( by linarith ), show ( n : ℝ ) ≥ 1000 by norm_cast; linarith, min_le_left ( 1 / 10 ) ( δ / 3 ), min_le_right ( 1 / 10 ) ( δ / 3 ), Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ) ] ) ( by
        exact min_le_left _ _ );
      grind;
    · norm_num;
    · positivity;
    · exact min_le_left _ _;
    · intro v; specialize h_deg v; specialize hN n ( by linarith ) ; norm_num [ Real.sqrt_eq_rpow ] at *;
      rw [ show ( 1 / 2 - ε : ℝ ) = -ε + 1 / 2 by ring, Real.rpow_add ] at h_deg <;> norm_num at *;
      · exact h_deg.le.trans ( mul_le_mul_of_nonneg_right ( by cases min_cases ( 1 / 10 : ℝ ) ( δ / 3 ) <;> linarith ) ( by positivity ) );
      · linarith;
  refine' ⟨ G', hG'_sub, hG'_clique_free, hG'_diameter, _ ⟩;
  refine' le_trans _ ( hG'_edges.trans _ );
  · exact_mod_cast Finset.card_le_card fun x hx => by aesop;
  · exact mul_le_mul_of_nonneg_right ( by cases min_cases ( 1 / 10 : ℝ ) ( δ / 3 ) <;> linarith ) ( sq_nonneg _ )

/-- The maximum degree of a graph on `Fin n` (as a natural number). -/
noncomputable def maxDegreeFin {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Finset.univ.sup (fun v : Fin n => (G.neighborFinset v).card)

/-- For a graph `G` on `n` vertices, `h2 G` is the smallest number of edges that need
to be added to obtain a supergraph with diameter ≤ 2 that is still triangle-free
(expressed as `CliqueFree 3`). -/
noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  exact sInf {k : ℕ |
    ∃ H : SimpleGraph (Fin n),
      G ≤ H ∧
      H.CliqueFree 3 ∧
      (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
      ((H.edgeFinset \ G.edgeFinset).card = k)}

/-
Positive answer (asymptotic form):

For a family of triangle-free graphs `G n` on `n` vertices, if the maximum degree is `o(n^(1/2))`
then `h₂(G n)` is `o(n^2)`, where `h₂` counts the minimum number of edges to add to make the
graph triangle-free and of diameter ≤ 2.
-/
theorem erdos_618
    (G : ∀ n : ℕ, SimpleGraph (Fin n))
    (hTriangleFree : ∀ n : ℕ, (G n).CliqueFree 3)
    (hMaxDeg :
      (fun n : ℕ => (maxDegreeFin (G n) : ℝ))
        =o[Filter.atTop] (fun n : ℕ => Real.rpow (n : ℝ) ((1 : ℝ) / 2))) :
    (fun n : ℕ => (h2 (G n) : ℝ))
      =o[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (2 : ℕ)) := by
  rw [ Asymptotics.isLittleO_iff ] at *;
  intro c hc_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (maxDegreeFin (G n) : ℝ) ≤ (min (1 / 10) (c / 3)) * Real.sqrt n ∧ n ≥ 1000 ∧ (min (1 / 10) (c / 3)) * Real.sqrt n ≥ 4 ∧ (min (1 / 10) (c / 3)) ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ) := by
    have h_conds : ∀ᶠ n : ℕ in Filter.atTop,
      n ≥ 1000 ∧
      (min (1 / 10) (c / 3)) * Real.sqrt n ≥ 4 ∧
      (min (1 / 10) (c / 3)) ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ) := by
        have h_conds : Filter.Tendsto (fun n : ℕ => 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ)) Filter.atTop (nhds 0) := by
          -- We can factor out the constant $2$ and use the fact that $(\log n)^{1/3} / n^{1/6}$ tends to $0$ as $n$ tends to infinity.
          have h_log_div_n : Filter.Tendsto (fun n : ℕ => (Real.log n) ^ (1 / 3 : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
            -- Let $y = \log x$, therefore the expression becomes $\frac{y^{1/3}}{e^{y/6}}$.
            suffices h_log : Filter.Tendsto (fun y : ℝ => y ^ (1 / 3 : ℝ) / Real.exp (y / 6)) Filter.atTop (nhds 0) by
              have h_log : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) ^ (1 / 3 : ℝ) / Real.exp (Real.log (n : ℝ) / 6)) Filter.atTop (nhds 0) := by
                exact h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
              refine h_log.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hn ) ] ; ring_nf );
            -- Let $z = \frac{y}{6}$, therefore the expression becomes $\frac{(6z)^{1/3}}{e^z}$.
            suffices h_z : Filter.Tendsto (fun z : ℝ => (6 * z) ^ (1 / 3 : ℝ) / Real.exp z) Filter.atTop (nhds 0) by
              convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 6⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf;
            -- We can factor out the constant $6^{1/3}$ and use the fact that $z^{1/3} / e^z$ tends to $0$ as $z$ tends to infinity.
            suffices h_factor : Filter.Tendsto (fun z : ℝ => z ^ (1 / 3 : ℝ) / Real.exp z) Filter.atTop (nhds 0) by
              have h_factor : Filter.Tendsto (fun z : ℝ => 6 ^ (1 / 3 : ℝ) * (z ^ (1 / 3 : ℝ) / Real.exp z)) Filter.atTop (nhds 0) := by
                simpa using h_factor.const_mul _;
              refine h_factor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with z hz using by rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring );
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
            refine' squeeze_zero_norm' _ this;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ Real.exp_neg ] ; exact mul_le_mul_of_nonneg_right ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le hx.le <| show ( 1 : ℝ ) / 3 ≤ 1 by norm_num ) <| by norm_num ) <| by positivity;
          simpa [ mul_div_assoc ] using h_log_div_n.const_mul 2;
        have h_conds : ∀ᶠ n : ℕ in Filter.atTop, (min (1 / 10) (c / 3)) * Real.sqrt n ≥ 4 ∧ (min (1 / 10) (c / 3)) ≥ 2 * (Real.log n)^(1/3 : ℝ) / n^(1/6 : ℝ) := by
          have h_conds : ∀ᶠ n : ℕ in Filter.atTop, (min (1 / 10) (c / 3)) * Real.sqrt n ≥ 4 := by
            have h_conds : Filter.Tendsto (fun n : ℕ => (min (1 / 10) (c / 3)) * Real.sqrt n) Filter.atTop Filter.atTop := by
              exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
            exact h_conds.eventually_ge_atTop 4;
          filter_upwards [ h_conds, ‹Filter.Tendsto ( fun n : ℕ => 2 * Real.log ( n : ℝ ) ^ ( 1 / 3 : ℝ ) / ( n : ℝ ) ^ ( 1 / 6 : ℝ ) ) Filter.atTop ( nhds 0 ) ›.eventually ( ge_mem_nhds <| show 0 < Min.min ( 1 / 10 ) ( c / 3 ) by positivity ) ] with n hn hn' using ⟨ hn, hn' ⟩;
        filter_upwards [ h_conds, Filter.eventually_ge_atTop 1000 ] with n hn hn' using ⟨ hn', hn ⟩;
    have := hMaxDeg ( show 0 < Min.min ( 1 / 10 ) ( c / 3 ) by positivity );
    norm_num [ Real.sqrt_eq_rpow ] at *;
    exact ⟨ Max.max this.choose h_conds.choose, fun n hn => ⟨ by simpa only [ abs_of_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ] using this.choose_spec n ( le_trans ( le_max_left _ _ ) hn ), h_conds.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) ⟩ ⟩;
  filter_upwards [ Filter.eventually_ge_atTop N ] with n hn;
  obtain ⟨h_max_deg, h_n_large, h_c_sqrt, h_c_lower⟩ := hN n hn;
  have h_binom : (n.choose (Nat.floor (5 * (min (1 / 10) (c / 3)) * n)) : ℝ) ≤ 2 ^ (10 * (min (1 / 10) (c / 3)) * n * Real.log (1 / (min (1 / 10) (c / 3)))) := by
    apply binom_entropy_bound n (min (1 / 10) (c / 3)) (by
    positivity) (by
    nlinarith [ show ( n : ℝ ) ≥ 1000 by norm_cast, Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ), min_le_left ( 1 / 10 ) ( c / 3 ), min_le_right ( 1 / 10 ) ( c / 3 ) ]) (by
    exact min_le_left _ _);
  obtain ⟨G', h_le, h_free', h_diam, h_edges⟩ := theorem_1_2 (G n) n (min (1 / 10) (c / 3)) (by
  norm_num +zetaDelta at *) h_n_large (by
  positivity) (by
  exact min_le_left _ _) (by
  exact h_c_sqrt) (by
  exact h_c_lower) (by
  exact fun v => le_trans ( Nat.cast_le.mpr ( Finset.le_sup ( f := fun v => ( G n |> SimpleGraph.neighborFinset |> fun s => s v |> Finset.card ) ) ( Finset.mem_univ v ) ) ) h_max_deg) (by
  exact hTriangleFree n) (by
  convert h_binom using 1);
  have h2_le_k : h2 (G n) ≤ (G'.edgeFinset \ (G n).edgeFinset).card := by
    exact csInf_le ⟨ 0, fun k hk => Nat.zero_le _ ⟩ ⟨ G', h_le, h_free', h_diam, rfl ⟩;
  norm_num [ Norm.norm ] at *;
  exact le_trans ( Nat.cast_le.mpr h2_le_k ) ( le_trans ( Nat.cast_le.mpr ( Finset.card_le_card ( Finset.sdiff_subset ) ) ) ( by norm_num at *; nlinarith [ min_le_left ( 1 / 10 ) ( c / 3 ), min_le_right ( 1 / 10 ) ( c / 3 ) ] ) )

#print axioms erdos_134
-- 'erdos_134' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos_618
-- 'erdos_618' depends on axioms: [propext, Classical.choice, Quot.sound]
