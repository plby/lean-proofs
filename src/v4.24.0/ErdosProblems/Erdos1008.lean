/-

This is a Lean formalization of a solution to Erdős Problem 1008.
https://www.erdosproblems.com/forum/thread/1008

The original proofs were found by: Conlon, Fox, & Sudakov and Hunter

[CFS14b] D. Conlon, J. Fox, and B. Sudakov, Large subgraphs without
complete bipartite graphs. arXiv:1401.6711 (2014).


A proof of ChatGPT's choice was auto-formalized by Aristotle (from
Harmonic).  The final theorem statement was written by Aristotle.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We formalized the definitions of $C_4$, edge count, and $C_4$ count. We proved Lemma 25 (bounding $c_4(G)$), Lemma 26 (existence of a $C_4$-free subgraph with many edges via deletion), and Theorem 27 (every graph with $m$ edges contains a $C_4$-free subgraph with at least $\frac{15}{32}m^{2/3}$ edges) using the probabilistic method.
-/

import Mathlib

namespace Erdos1008

set_option linter.mathlibStandardSet false

set_option maxHeartbeats 0

open Classical SimpleGraph

/-
Definitions of C4, edge_count, c4_count, and is_C4_free.
-/
def C4 : SimpleGraph (Fin 4) := SimpleGraph.cycleGraph 4

def edge_count {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := G.edgeFinset.card

noncomputable def c4_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Fintype.card { H : G.Subgraph // Nonempty (H.coe ≃g C4) }

def is_C4_free {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  c4_count G = 0

/-
Two edges are disjoint if they have no common endpoint.
-/
def DisjointEdges {V : Type*} (e f : Sym2 V) : Prop :=
  ∀ v, v ∈ e → v ∉ f

/-
DisjointEdges is symmetric and decidable.
-/
lemma DisjointEdges_symm {V : Type*} (e f : Sym2 V) : DisjointEdges e f ↔ DisjointEdges f e := by
  simp [DisjointEdges]
  constructor
  · intro h v hv he
    exact h v he hv
  · intro h v hv hf
    exact h v hf hv

instance DisjointEdges_decidable {V : Type*} [Fintype V] [DecidableEq V] (e f : Sym2 V) : Decidable (DisjointEdges e f) :=
  Fintype.decidableForallFintype

/-
Definition of disjoint edge pairs.
-/
def is_disjoint_pair {V : Type*} [Fintype V] [DecidableEq V] : Sym2 (Sym2 V) → Bool :=
  Sym2.lift ⟨fun e f => decide (DisjointEdges e f), fun e f => by
    simp only [decide_eq_decide]
    exact DisjointEdges_symm e f
  ⟩

def disjoint_edge_pairs {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Sym2 (Sym2 V)) :=
  G.edgeFinset.sym2.filter (fun p => is_disjoint_pair p)

/-
The number of disjoint edge pairs is at most $\binom{m}{2}$.
-/
lemma disjoint_edge_pairs_card_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  (disjoint_edge_pairs G).card ≤ (edge_count G).choose 2 := by
    -- The number of disjoint edge pairs is at most the total number of edge pairs, which is $\binom{m}{2}$, where $m$ is the number of edges.
    have h_card_pairs : (disjoint_edge_pairs G).card ≤ (G.edgeFinset).card.choose 2 := by
      -- The set of edges is a finite set, and we can define a function from pairs of edges to pairs of their endpoints.
      have h_edges : (disjoint_edge_pairs G) ⊆ Finset.sym2 G.edgeFinset := by
        exact Finset.filter_subset _ _;
      -- The cardinality of the sym2 of a finite set is exactly Nat.choose (Finset.card S) 2.
      have h_sym2_card : ∀ (S : Finset (Sym2 V)), (Finset.sym2 S).card = Nat.choose (Finset.card S) 2 + Finset.card S := by
        intro S;
        rw [ Finset.card_sym2 ];
        simp +arith +decide [ Nat.choose ];
      have h_filter : (disjoint_edge_pairs G).card ≤ Finset.card (Finset.sym2 G.edgeFinset) - Finset.card (Finset.filter (fun p => ¬is_disjoint_pair p) (Finset.sym2 G.edgeFinset)) := by
        refine' Nat.le_sub_of_add_le _;
        rw [ ← Finset.card_union_of_disjoint ];
        · exact Finset.card_le_card ( Finset.union_subset h_edges ( Finset.filter_subset _ _ ) );
        · simp +contextual [ Finset.disjoint_left ];
          unfold disjoint_edge_pairs; aesop;
      have h_filter_card : Finset.card (Finset.filter (fun p => ¬is_disjoint_pair p) (Finset.sym2 G.edgeFinset)) ≥ Finset.card G.edgeFinset := by
        have h_filter_card : Finset.image (fun e => Sym2.mk (e, e)) G.edgeFinset ⊆ Finset.filter (fun p => ¬is_disjoint_pair p) (Finset.sym2 G.edgeFinset) := by
          simp +decide [ Finset.subset_iff ];
          intro p hp; unfold is_disjoint_pair; simp +decide [ hp ] ;
          rcases p with ⟨ v, w ⟩ ; simp +decide [ DisjointEdges ];
        exact le_trans ( by rw [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] ) ( Finset.card_mono h_filter_card );
      exact h_filter.trans ( Nat.sub_le_of_le_add <| by linarith [ h_sym2_card G.edgeFinset ] );
    exact h_card_pairs

/-
Definition of a(e,f).
-/
noncomputable def count_C4_containing_pair {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Sym2 (Sym2 V) → ℕ :=
  Sym2.lift ⟨fun e f => Fintype.card { H : G.Subgraph // Nonempty (H.coe ≃g C4) ∧ e ∈ H.edgeSet ∧ f ∈ H.edgeSet }, fun e f => by
    simp only [and_comm]
  ⟩

/-
If a C4 subgraph contains two disjoint edges, its vertex set is the union of the vertices of those edges.
-/
lemma C4_vertices_of_disjoint_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (H : G.Subgraph) (hH : Nonempty (H.coe ≃g C4))
  (e f : Sym2 V) (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet) (hdisj : DisjointEdges e f) :
  H.verts = (e.toFinset ∪ f.toFinset : Finset V) := by
    -- Since $H \cong C_4$, $|V(H)| = 4$.
    have h_card : (H.verts : Set V).ncard = 4 := by
      obtain ⟨ h ⟩ := hH;
      have h_card : (Finset.image (fun v => v : H.verts → V) (Finset.univ : Finset H.verts)).card = 4 := by
        rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ];
        exact Fintype.card_congr h.toEquiv;
      convert h_card using 1;
      rw [ ← Set.ncard_coe_finset ] ; aesop;
    have h_card_eq : (e.toFinset ∪ f.toFinset : Finset V).card = 4 := by
      rcases e with ⟨ u, v ⟩ ; rcases f with ⟨ w, x ⟩ ; simp_all +decide
      simp_all +decide [ Sym2.toFinset ];
      simp_all +decide [ Sym2.toMultiset ];
      rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp +decide [ *, Finset.mem_insert, Finset.mem_singleton ];
      · exact Subgraph.Adj.ne he;
      · exact ⟨ fun h => hdisj x ( by aesop ) ( by aesop ), fun h => hdisj x ( by aesop ) ( by aesop ) ⟩;
      · have := hf.ne; aesop;
    have h_subset : (e.toFinset ∪ f.toFinset : Finset V) ⊆ H.verts.toFinset := by
      simp_all +decide [ Finset.subset_iff ];
      rintro x ( hx | hx ) <;> [ exact Subgraph.mem_verts_of_mem_edge he hx; exact Subgraph.mem_verts_of_mem_edge hf hx ];
    have h_eq : (e.toFinset ∪ f.toFinset : Finset V) = H.verts.toFinset := by
      exact Finset.eq_of_subset_of_card_le h_subset ( by rw [ h_card_eq, Set.ncard_eq_toFinset_card' ] at *; aesop );
    aesop

/-
Helper definitions for possible C4 edges.
-/
noncomputable def edges_from_pairs {V : Type*} (p1 p2 : V × V) : Finset (Finset (Sym2 V)) :=
  let u := p1.1; let v := p1.2
  let x := p2.1; let y := p2.2
  {
    {s(u, v), s(x, y), s(u, x), s(v, y)},
    {s(u, v), s(x, y), s(u, y), s(v, x)}
  }

lemma edges_from_pairs_swap_left {V : Type*} (p1 p2 : V × V) :
  edges_from_pairs (p1.swap) p2 = edges_from_pairs p1 p2 := by
    unfold edges_from_pairs;
    ext; simp +decide [ Sym2.eq_swap ] ;
    grind

lemma edges_from_pairs_swap_right {V : Type*} (p1 p2 : V × V) :
  edges_from_pairs p1 (p2.swap) = edges_from_pairs p1 p2 := by
    -- By definition of edges_from_pairs, we can show that it is invariant under swapping the vertices in p2.
    simp [edges_from_pairs, Sym2.eq_swap];
    exact
      Finset.pair_comm {Sym2.mk p1, Sym2.mk p2, s(p1.1, p2.2), s(p2.1, p1.2)}
        {Sym2.mk p1, Sym2.mk p2, s(p1.1, p2.1), s(p1.2, p2.2)}

/-
Inner definition for possible C4 edges.
-/
noncomputable def possible_C4_edges_inner {V : Type*} (p1 : V × V) (f : Sym2 V) : Finset (Finset (Sym2 V)) :=
  Sym2.lift ⟨fun x y => edges_from_pairs p1 (x, y), fun x y => by
    simp only
    rw [←edges_from_pairs_swap_right]
    rfl
  ⟩ f

/-
Definition of possible C4 edge sets.
-/
noncomputable def possible_C4_edges {V : Type*} (e f : Sym2 V) : Finset (Finset (Sym2 V)) :=
  Sym2.lift ⟨fun u v => possible_C4_edges_inner (u, v) f, fun u v => by
    -- By definition of `possible_C4_edges_inner`, we have:
    simp [possible_C4_edges_inner];
    congr! 2;
    unfold edges_from_pairs; ext; simp +decide [ Sym2.eq_swap ] ;
    grind
  ⟩ e

/-
In a C4 with disjoint edges {u,v} and {x,y}, u is adjacent to x or y.
-/
lemma C4_u_neighbor_x_or_y {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (H : G.Subgraph) (hH : Nonempty (H.coe ≃g C4))
  (e f : Sym2 V) (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet) (hdisj : DisjointEdges e f)
  (u v x y : V) (hue : e = s(u, v)) (huf : f = s(x, y)) :
  H.Adj u x ∨ H.Adj u y := by
    -- Since H is isomorphic to C4, which is 2-regular, every vertex in H must have degree 2. Therefore, u must be adjacent to exactly two other vertices in H.
    have h_deg_u : H.degree u = 2 := by
      obtain ⟨f, hf⟩ := hH
      have h_deg_u : ∀ v : H.verts, (H.coe.degree v) = 2 := by
        intro v
        have h_deg_u : (C4.degree (f v)) = 2 := by
          simp +decide [ SimpleGraph.degree, SimpleGraph.neighborFinset_def ];
          simp +decide [ C4 ];
          rcases f v with ⟨ _ | _ | _ | _ | n ⟩ <;> simp +decide [ SimpleGraph.cycleGraph ];
          linarith;
        convert h_deg_u using 1;
        rw [ SimpleGraph.degree, SimpleGraph.degree ];
        rw [ Finset.card_eq_sum_ones, Finset.card_eq_sum_ones ];
        refine' Finset.sum_bij ( fun x hx => f ⟨ x, _ ⟩ ) _ _ _ _ <;> simp_all +decide [ SimpleGraph.neighborFinset ];
        intro b hb; obtain ⟨ a, ha ⟩ := f.surjective b; use a; aesop;
      by_cases hu : u ∈ H.verts;
      · simpa using h_deg_u ⟨ u, hu ⟩;
      · simp_all +decide [ SimpleGraph.Subgraph.mem_edgeSet ];
        exact False.elim ( hu ( H.edge_vert he ) );
    contrapose! h_deg_u;
    have h_deg_u : H.degree u = 1 := by
      refine' Finset.card_eq_one.mpr _;
      simp_all +decide [ Finset.eq_singleton_iff_unique_mem ];
      have h_deg_u : ∀ w, H.Adj u w → w = v := by
        intro w hw
        have h_w_in_H : w ∈ H.verts := by
          exact H.edge_vert hw.symm;
        have h_w_in_H : H.verts = (e.toFinset ∪ f.toFinset : Finset V) := by
          have := C4_vertices_of_disjoint_edges G H hH e f; aesop;
        simp_all +decide [ Set.ext_iff ];
        rcases ‹ ( w = u ∨ w = v ) ∨ w = x ∨ w = y › with ( ( rfl | rfl ) | rfl | rfl ) <;> simp_all +decide
        exact absurd hw ( by have := H.loopless w; aesop );
      exact ⟨ v, he, h_deg_u ⟩;
    linarith

/-
Structure of C4 with disjoint edges.
-/
lemma C4_disjoint_edges_structure {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (H : G.Subgraph) (hH : Nonempty (H.coe ≃g C4))
  (e f : Sym2 V) (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet) (hdisj : DisjointEdges e f)
  (u v x y : V) (hue : e = s(u, v)) (huf : f = s(x, y)) :
  H.edgeSet = {s(u, v), s(x, y), s(u, x), s(v, y)} ∨ H.edgeSet = {s(u, v), s(x, y), s(u, y), s(v, x)} := by
    have := hH.some.symm;
    cases' this with h1 h2;
    have := Fintype.card_congr h1; simp +decide at this;
    obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl⟩ : ∃ i j k l : V, i ∈ H.verts ∧ j ∈ H.verts ∧ k ∈ H.verts ∧ l ∈ H.verts ∧ i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ H.Adj i j ∧ H.Adj j k ∧ H.Adj k l ∧ H.Adj l i ∧ ¬H.Adj i k ∧ ¬H.Adj j l := by
      obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl⟩ : ∃ i j k l : Fin 4, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧ C4.Adj i j ∧ C4.Adj j k ∧ C4.Adj k l ∧ C4.Adj l i ∧ ¬C4.Adj i k ∧ ¬C4.Adj j l := by
        simp +decide [ C4 ];
      use h1 i, h1 j, h1 k, h1 l;
      simp_all +decide
      exact ⟨ fun h => hij <| h1.injective <| Subtype.ext h, fun h => hik <| h1.injective <| Subtype.ext h, fun h => hil <| h1.injective <| Subtype.ext h, fun h => hjk <| h1.injective <| Subtype.ext h, fun h => hjl <| h1.injective <| Subtype.ext h, fun h => hkl.1 <| h1.injective <| Subtype.ext h ⟩;
    have h_edges : H.edgeSet = {s(i, j), s(j, k), s(k, l), s(l, i)} := by
      have h_edges : ∀ v ∈ H.verts, ∀ w ∈ H.verts, H.Adj v w → v = i ∧ w = j ∨ v = j ∧ w = i ∨ v = j ∧ w = k ∨ v = k ∧ w = j ∨ v = k ∧ w = l ∨ v = l ∧ w = k ∨ v = l ∧ w = i ∨ v = i ∧ w = l := by
        have h_edges : H.verts = {i, j, k, l} := by
          rw [ eq_comm ] at this;
          have h_card : Finset.card ({i, j, k, l} : Finset V) = 4 := by
            rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton ] <;> aesop;
          have h_card : Finset.filter (fun v => v ∈ H.verts) Finset.univ = {i, j, k, l} := by
            apply Finset.eq_of_subset_of_card_le;
            · intro v hv; have := Finset.eq_of_subset_of_card_le ( show { i, j, k, l } ⊆ Finset.filter ( fun v => v ∈ H.verts ) Finset.univ from by aesop_cat ) ; aesop;
            · linarith;
          simp_all +decide [ Finset.ext_iff, Set.ext_iff ];
        simp_all +decide [ SimpleGraph.Subgraph.adj_comm ];
        exact ⟨ fun h => by have := H.loopless _ h; contradiction, fun h => by have := H.loopless _ h; contradiction, fun h => by have := H.loopless _ h; contradiction, fun h => by have := H.loopless _ h; contradiction ⟩;
      ext e;
      constructor;
      · rcases e with ⟨ v, w ⟩;
        intro hvw; specialize h_edges v ( H.edge_vert hvw ) w ( H.edge_vert hvw.symm ) hvw; aesop;
      · rintro ( rfl | rfl | rfl | rfl ) <;> simp +decide [ * ];
    have h_cases : e = s(i, j) ∧ f = s(k, l) ∨ e = s(j, k) ∧ f = s(l, i) ∨ e = s(k, l) ∧ f = s(i, j) ∨ e = s(l, i) ∧ f = s(j, k) := by
      simp_all +decide [ Sym2.eq_swap ];
      rcases he with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) ) <;> rcases hf with ( ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) | ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) ) <;> simp +decide at hdisj ⊢;
      all_goals unfold DisjointEdges at hdisj; simp +decide [ *, Sym2.eq_swap ] at hdisj ⊢;
    rcases h_cases with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp_all +decide [ Sym2.eq_swap ];
    · grind +ring;
    · rcases hue with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> rcases huf with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp +decide [ Sym2.eq_swap ];
      · grind;
      · grind;
      · grind;
      · exact Or.inl ( by ext; simp +decide [ or_comm, or_left_comm ] );
    · rcases huf with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> rcases hue with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp +decide [ Sym2.eq_swap ] at hdisj ⊢;
      · grind;
      · exact Or.inl ( by ext; simp +decide [ or_comm, or_left_comm, or_assoc ] );
      · exact Or.inl ( by ext; simp +decide [ or_comm, or_left_comm, or_assoc ] );
      · grind;
    · rcases hue with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> rcases huf with ( ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩ ) <;> simp +decide [ Sym2.eq_swap ];
      · grind;
      · grind;
      · grind;
      · grind

/-
For any disjoint pair of edges in G, the number of C4 subgraphs containing both edges is at most 2.
-/
lemma count_C4_containing_pair_le_two {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (p : Sym2 (Sym2 V)) (hp : p ∈ disjoint_edge_pairs G) :
  count_C4_containing_pair G p ≤ 2 := by
    unfold count_C4_containing_pair;
    rcases p with ⟨ e, f ⟩;
    rcases e with ⟨ u, v ⟩ ; rcases f with ⟨ x, y ⟩ ;
    unfold disjoint_edge_pairs at hp;
    -- Since $e$ and $f$ are disjoint, any $C4$ subgraph containing both $e$ and $f$ must have vertex set $\{u, v, x, y\}$.
    have h_vertex_set : ∀ H : G.Subgraph, Nonempty (H.coe ≃g C4) → H.Adj u v → H.Adj x y → H.verts = {u, v, x, y} := by
      intros H hH hu hv;
      have h_disjoint : DisjointEdges (Sym2.mk (u, v)) (Sym2.mk (x, y)) := by
        unfold is_disjoint_pair at hp; aesop;
      have := C4_vertices_of_disjoint_edges G H hH ( Sym2.mk ( u, v ) ) ( Sym2.mk ( x, y ) ) ?_ ?_ h_disjoint <;> aesop;
    -- Since $e$ and $f$ are disjoint, any $C4$ subgraph containing both $e$ and $f$ must have edge set $\{e, f, \{u, x\}, \{v, y\}\}$ or $\{e, f, \{u, y\}, \{v, x\}\}$.
    have h_edge_set : ∀ H : G.Subgraph, Nonempty (H.coe ≃g C4) → H.Adj u v → H.Adj x y → H.edgeSet = {s(u, v), s(x, y), s(u, x), s(v, y)} ∨ H.edgeSet = {s(u, v), s(x, y), s(u, y), s(v, x)} := by
      intros H hH hu hv
      apply C4_disjoint_edges_structure G H hH (s(u, v)) (s(x, y)) hu hv (by
      unfold is_disjoint_pair at hp; aesop;) u v x y rfl rfl;
    have h_subgraph_count : ∀ H₁ H₂ : G.Subgraph, Nonempty (H₁.coe ≃g C4) → Nonempty (H₂.coe ≃g C4) → H₁.Adj u v → H₁.Adj x y → H₂.Adj u v → H₂.Adj x y → H₁.edgeSet = H₂.edgeSet → H₁ = H₂ := by
      intros H₁ H₂ hH₁ hH₂ h₁ h₂ h₃ h₄ h₅;
      ext v;
      · grind;
      · replace h₅ := congr_arg ( fun s => s.toFinset ) h₅ ; simp_all +decide [ Finset.ext_iff ];
        specialize h₅ ( Sym2.mk ( v, ‹_› ) ) ; aesop;
    have h_subgraph_count : Finset.card (Finset.image (fun H : G.Subgraph => H.edgeSet) (Finset.filter (fun H : G.Subgraph => Nonempty (H.coe ≃g C4) ∧ H.Adj u v ∧ H.Adj x y) (Finset.univ : Finset (G.Subgraph)))) ≤ 2 := by
      exact le_trans ( Finset.card_le_card ( Finset.image_subset_iff.mpr fun H hH => show H.edgeSet ∈ { { s(u, v), s(x, y), s(u, x), s(v, y) }, { s(u, v), s(x, y), s(u, y), s(v, x) } } by simpa using h_edge_set H ( Finset.mem_filter.mp hH |>.2.1 ) ( Finset.mem_filter.mp hH |>.2.2.1 ) ( Finset.mem_filter.mp hH |>.2.2.2 ) ) ) ( Finset.card_insert_le _ _ );
    rw [ Finset.card_image_of_injOn ] at h_subgraph_count;
    · simpa only [ Fintype.card_subtype ] using h_subgraph_count;
    · exact fun H₁ h₁ H₂ h₂ h => ‹∀ H₁ H₂ : G.Subgraph, Nonempty (H₁.coe ≃g C4) → Nonempty (H₂.coe ≃g C4) → H₁.Adj u v → H₁.Adj x y → H₂.Adj u v → H₂.Adj x y → H₁.edgeSet = H₂.edgeSet → H₁ = H₂› H₁ H₂ ( Finset.mem_filter.mp h₁ |>.2.1 ) ( Finset.mem_filter.mp h₂ |>.2.1 ) ( Finset.mem_filter.mp h₁ |>.2.2.1 ) ( Finset.mem_filter.mp h₁ |>.2.2.2 ) ( Finset.mem_filter.mp h₂ |>.2.2.1 ) ( Finset.mem_filter.mp h₂ |>.2.2.2 ) h

/-
Every C4 subgraph has exactly two disjoint pairs of edges.
-/
noncomputable def disjoint_pairs_in_subgraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (H : G.Subgraph) : Finset (Sym2 (Sym2 V)) :=
  H.edgeSet.toFinset.sym2.filter (fun p => is_disjoint_pair p)

lemma C4_has_two_disjoint_pairs {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (H : G.Subgraph) (hH : Nonempty (H.coe ≃g C4)) :
  (disjoint_pairs_in_subgraph G H).card = 2 := by
    rcases hH with ⟨ e ⟩;
    -- Let's denote the vertices of $C4$ as $u, v, x, y$.
    obtain ⟨u, v, x, y, hu, hv, hx, hy, huv, hvx, hxy, hyu⟩ : ∃ u v x y : H.verts, u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y ∧ H.Adj u v ∧ H.Adj v x ∧ H.Adj x y ∧ H.Adj y u := by
      have := e.symm;
      rcases this with ⟨ f, hf ⟩;
      use f 0, f 1, f 2, f 3;
      simp_all +decide [ C4 ];
    -- Let's denote the edges of $C4$ as $\{u,v\}$, $\{v,x\}$, $\{x,y\}$, and $\{y,u\}$.
    have h_edges : H.edgeSet = {s(u.val, v.val), s(v.val, x.val), s(x.val, y.val), s(y.val, u.val)} := by
      have h_edges : H.edgeSet ⊇ {s(u.val, v.val), s(v.val, x.val), s(x.val, y.val), s(y.val, u.val)} := by
        simp_all +decide [ Set.subset_def ];
      have h_card : H.edgeSet.ncard = 4 := by
        have h_card : (H.coe.edgeSet).ncard = 4 := by
          have h_card : (C4.edgeSet).ncard = 4 := by
            simp +decide [ Set.ncard_eq_toFinset_card' ];
            simp +decide [ C4 ];
            simp +decide [ Finset.card, SimpleGraph.edgeSet ];
            simp +decide [ edgeSetEmbedding ];
          rw [ ← h_card, Set.ncard_def, Set.ncard_def, Set.encard_congr ];
          exact e.mapEdgeSet;
        convert h_card using 1;
        rw [ ← Set.ncard_image_of_injective _ ( show Function.Injective ( fun e : Sym2 H.verts => Sym2.map ( fun x : H.verts => x.val ) e ) from ?_ ) ];
        · congr with e ; simp +decide [ Sym2.map ];
          constructor;
          · rcases e with ⟨ u, v ⟩;
            intro huv;
            use s(⟨u, by
              exact H.edge_vert huv |> fun h => by aesop;⟩, ⟨v, by
              exact Subgraph.Adj.snd_mem huv⟩);
            exact ⟨ huv, rfl ⟩;
          · aesop;
        · intro e₁ e₂ h; induction e₁ using Sym2.inductionOn ; induction e₂ using Sym2.inductionOn ; aesop;
      have h_card : ({s(u.val, v.val), s(v.val, x.val), s(x.val, y.val), s(y.val, u.val)} : Set (Sym2 V)).ncard = 4 := by
        rw [ Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_singleton ] <;> simp +decide [ * ];
        · aesop;
        · aesop;
        · grind;
      exact Set.eq_of_subset_of_ncard_le h_edges ( by aesop ) ▸ rfl;
    unfold disjoint_pairs_in_subgraph;
    simp +decide [ *, Finset.filter ];
    simp +decide [ *, is_disjoint_pair ];
    rw [ Multiset.ndinsert_of_notMem, Multiset.ndinsert_of_notMem, Multiset.ndinsert_of_notMem ] <;> simp +decide [ *, DisjointEdges ];
    · rw [ Multiset.sym2 ];
      erw [ Quotient.liftOn_mk ] ; simp +decide [ *, Sym2.lift ];
      simp +decide [ List.sym2, List.filter_cons ];
      grind;
    · aesop;
    · aesop;
    · aesop

/-
The sum of the number of C4s containing each disjoint pair of edges equals twice the total number of C4s.
-/
lemma sum_count_C4_containing_pair_eq_two_mul_c4_count {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∑ p ∈ disjoint_edge_pairs G, count_C4_containing_pair G p = 2 * c4_count G := by
    -- By definition of $count_C4_containing_pair$, each C4 subgraph $H$ contributes exactly 2 to the sum $\sum_{p \in \text{disjoint\_edge\_pairs } G} count_C4_containing_pair G p$.
    have h_contribution : ∀ H : G.Subgraph, Nonempty (H.coe ≃g C4) → ∑ p ∈ disjoint_edge_pairs G, (if p ∈ disjoint_pairs_in_subgraph G H then 1 else 0) = 2 := by
      intro H hH
      have h_disjoint_pairs : Finset.filter (fun p => p ∈ disjoint_pairs_in_subgraph G H) (disjoint_edge_pairs G) = disjoint_pairs_in_subgraph G H := by
        ext p
        simp [disjoint_edge_pairs, disjoint_pairs_in_subgraph];
        intro hp hp';
        exact ⟨ fun a ha => H.edgeSet_subset ( hp a ha ), hp' ⟩;
      simp_all +decide
      rw [ ← Finset.filter_mem_eq_inter, h_disjoint_pairs, C4_has_two_disjoint_pairs G H hH ];
    -- By definition of $count_C4_containing_pair$, we can rewrite the left-hand side of the equation.
    have h_rewrite : ∑ p ∈ disjoint_edge_pairs G, count_C4_containing_pair G p = ∑ p ∈ disjoint_edge_pairs G, ∑ H ∈ Finset.univ.filter (fun H : G.Subgraph => Nonempty (H.coe ≃g C4)), (if p ∈ disjoint_pairs_in_subgraph G H then 1 else 0) := by
      unfold count_C4_containing_pair;
      refine' Finset.sum_congr rfl fun p hp => _;
      rcases p with ⟨ e, f ⟩;
      simp +zetaDelta at *;
      rw [ Fintype.subtype_card ];
      congr 1 with H ; simp +decide [ disjoint_pairs_in_subgraph ];
      unfold disjoint_edge_pairs at hp; aesop;
    rw [ h_rewrite, Finset.sum_comm ];
    rw [ Finset.sum_congr rfl fun H hH => h_contribution H <| Finset.mem_filter.mp hH |>.2 ] ; simp +decide [ mul_comm, c4_count ];
    rw [ Fintype.subtype_card ]

/-
The number of C4 subgraphs is at most m choose 2.
-/
lemma c4_count_le_choose_two {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  c4_count G ≤ (edge_count G).choose 2 := by
    -- By Lemma 25, $2 c_4(G) \le \sum_{p \in \mathcal{P}} a(p) \le \sum_{p \in \mathcal{P}} 2 = 2 |\mathcal{P}|$.
    have h_le : 2 * c4_count G ≤ 2 * (disjoint_edge_pairs G).card := by
      -- By Lemma 25, $2 c_4(G) = \sum_{p \in \mathcal{P}} a(p)$.
      have h_sum : 2 * c4_count G = ∑ p ∈ disjoint_edge_pairs G, count_C4_containing_pair G p := by
        exact Eq.symm (sum_count_C4_containing_pair_eq_two_mul_c4_count G);
      rw [ h_sum, mul_comm ];
      exact Finset.sum_le_card_nsmul _ _ _ fun p hp => count_C4_containing_pair_le_two G p hp;
    linarith [ disjoint_edge_pairs_card_le G ]

/-
The edge count of G minus an edge e is the edge count of G minus 1.
-/
lemma edge_count_delete_edge {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (e : Sym2 V) (he : e ∈ G.edgeSet) :
  edge_count (G.deleteEdges {e}) = edge_count G - 1 := by
    -- The edge count of $G \setminus \{e\}$ is the edge count of $G$ minus the edge count of $\{e\}$.
    have h_edge_count : Finset.card (SimpleGraph.deleteEdges G {e}).edgeFinset = Finset.card (Finset.filter (fun e' => e' ≠ e) G.edgeFinset) := by
      congr with e' ; simp +decide [ SimpleGraph.deleteEdges ];
    have h_edge_count : Finset.card (Finset.filter (fun e' => e' ≠ e) G.edgeFinset) = G.edgeFinset.card - 1 := by
      rw [ Finset.filter_ne' ] ; aesop;
    unfold edge_count; aesop;

/-
If we delete an edge from a C4 subgraph, the C4 count decreases by at least 1.
-/
lemma c4_count_delete_edge_of_C4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (H : G.Subgraph) (hH : Nonempty (H.coe ≃g C4))
  (e : Sym2 V) (he : e ∈ H.edgeSet) :
  c4_count (G.deleteEdges {e}) ≤ c4_count G - 1 := by
    -- Let $H$ be a copy of $C_4$ in $G$ containing the edge $e$.
    obtain ⟨H', hH'⟩ : ∃ H' : G.Subgraph, Nonempty (H'.coe ≃g C4) ∧ e ∈ H'.edgeSet := by
      use H;
    -- The chosen copy of $C_4$ in $H_i$ is destroyed, and deleting edges cannot create new $4$-cycles, so $c_4(H_{i+1})\le c_4(H_i)-1$.
    have h_destroyed : ∀ H'' : (G.deleteEdges {e}).Subgraph, ¬Nonempty (H''.coe ≃g C4) ∨ e ∉ H''.edgeSet := by
      intro H''; by_cases h : e ∈ H''.edgeSet <;> simp_all +decide ;
      have := H''.edgeSet_subset h; simp_all +decide [ SimpleGraph.deleteEdges ] ;
    -- Therefore, the number of C4 subgraphs in $G.deleteEdges {e}$ is at most the number of C4 subgraphs in $G$ minus one.
    have h_card_le : Fintype.card { H'' : (G.deleteEdges {e}).Subgraph // Nonempty (H''.coe ≃g C4) } ≤ Fintype.card { H'' : G.Subgraph // Nonempty (H''.coe ≃g C4) ∧ e ∉ H''.edgeSet } := by
      refine' Fintype.card_le_of_injective _ _;
      refine' fun H'' => ⟨ _, _ ⟩;
      exact H''.val.map ( SimpleGraph.Hom.ofLE ( by simp +decide [ SimpleGraph.deleteEdges ] ) );
      refine' ⟨ _, _ ⟩;
      all_goals norm_num [ Function.Injective ];
      · obtain ⟨ f ⟩ := H''.2;
        refine' ⟨ _ ⟩;
        refine' { Equiv.trans _ f.toEquiv with .. };
        refine' Equiv.ofBijective ( fun x => ⟨ x, _ ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩;
        all_goals norm_num [ Subgraph.map ];
        exact x.2.choose_spec.2.symm ▸ x.2.choose_spec.1;
        · aesop;
        · exact fun a b a_2 b_2 => f.map_rel_iff';
      · grind;
      · intro a ha b hb hab;
        ext v; replace hab := congr_arg ( fun f => f.verts ) hab; aesop;
        replace hab := congr_arg ( fun f => f.Adj v ‹_› ) hab ; aesop;
    refine' Nat.le_sub_one_of_lt ( lt_of_le_of_lt h_card_le _ );
    refine' Fintype.card_lt_of_injective_of_notMem _ _ _;
    use fun x => ⟨ x.val, x.property.1 ⟩;
    refine' fun x y hxy => _;
    grind;
    exact ⟨ H', hH'.1 ⟩;
    aesop

/-
For every graph G, there exists a C4-free subgraph H with at least e(G) - c4(G) edges.
-/
lemma exists_C4_free_subgraph_with_min_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∃ H : SimpleGraph V, H ≤ G ∧ is_C4_free H ∧ edge_count H ≥ edge_count G - c4_count G := by
    unfold is_C4_free;
    induction' h : c4_count G using Nat.strong_induction_on with k ih generalizing G;
    by_cases h_exists_C4 : ∃ H : G.Subgraph, Nonempty (H.coe ≃g C4);
    · obtain ⟨H, hH⟩ := h_exists_C4
      obtain ⟨e, he⟩ : ∃ e ∈ H.edgeSet, True := by
        obtain ⟨ e, he ⟩ := hH.some.symm;
        simp_all +decide [ C4 ];
        exact ⟨ Sym2.mk ( e 0, e 1 ), by simpa [ Sym2.mk ] using he.mpr ( by decide ) ⟩;
      -- By deleting the edge $e$ from $G$, we obtain a graph $G'$ with $c4_count(G') \leq k - 1$.
      have h_delete_edge : c4_count (G.deleteEdges {e}) ≤ k - 1 := by
        have := c4_count_delete_edge_of_C4 G H hH e he.1; aesop;
      -- By the induction hypothesis, there exists a C4-free subgraph $H'$ of $G'$ with $e(H') \geq e(G') - (k - 1)$.
      obtain ⟨H', hH'_sub, hH'_C4_free, hH'_edge_count⟩ : ∃ H' ≤ G.deleteEdges {e}, c4_count H' = 0 ∧ edge_count H' ≥ edge_count (G.deleteEdges {e}) - (k - 1) := by
        specialize ih (c4_count (G.deleteEdges {e})) (by
        rcases k with ( _ | k ) <;> simp_all +decide;
        · contrapose! h;
          exact ne_of_gt ( Fintype.card_pos_iff.mpr ⟨ ⟨ H, hH ⟩ ⟩ );
        · linarith) (G.deleteEdges {e}) (by
        rfl);
        exact ⟨ ih.choose, ih.choose_spec.1, ih.choose_spec.2.1, le_trans ( Nat.sub_le_sub_left h_delete_edge _ ) ih.choose_spec.2.2 ⟩;
      refine' ⟨ H', _, hH'_C4_free, _ ⟩;
      · exact hH'_sub.trans ( SimpleGraph.deleteEdges_le _ );
      · have h_edge_count_delete : edge_count (G.deleteEdges {e}) = edge_count G - 1 := by
          apply edge_count_delete_edge;
          exact H.edgeSet_subset he.1;
        rcases k with ( _ | k ) <;> simp_all +decide;
        · contrapose! h;
          exact ne_of_gt ( Fintype.card_pos_iff.mpr ⟨ H, hH ⟩ );
        · grind;
    · unfold c4_count at *;
      simp_all +decide [ Fintype.card_eq_zero_iff ];
      refine' ⟨ G, le_rfl, _, _ ⟩ <;> simp_all +decide [ edge_count ];
      · exact ⟨ fun x => h_exists_C4 x.1 |> fun h => h.elim x.2.some ⟩;
      · grind

def prob_subgraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) (s : Finset (Sym2 V)) : ℝ :=
  p ^ s.card * (1 - p) ^ (G.edgeFinset.card - s.card)

def expectation_subgraph {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) (f : Finset (Sym2 V) → ℝ) : ℝ :=
  ∑ s ∈ G.edgeFinset.powerset, f s * prob_subgraph G p s

/-
The sum of probabilities of all subgraphs is 1.
-/
lemma sum_prob_subgraph_eq_one {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) :
  ∑ s ∈ G.edgeFinset.powerset, prob_subgraph G p s = 1 := by
    -- The sum of probabilities of all subgraphs is 1 by the binomial theorem.
    have h_binom : ∑ s ∈ G.edgeFinset.powerset, p ^ s.card * (1 - p) ^ (G.edgeFinset.card - s.card) = (p + (1 - p)) ^ G.edgeFinset.card := by
      rw [ add_pow ];
      rw [ Finset.sum_powerset ];
      exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun t ht => by rw [ Finset.mem_powersetCard.mp ht |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, Finset.card_powersetCard ] ;
    convert h_binom using 1;
    norm_num

/-
There exists a subgraph with value at least the expectation.
-/
lemma exists_subgraph_ge_expectation {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) (f : Finset (Sym2 V) → ℝ)
  (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1) :
  ∃ s ∈ G.edgeFinset.powerset, f s ≥ expectation_subgraph G p f := by
    have h_exists_max : ∃ s ∈ G.edgeFinset.powerset, ∀ t ∈ G.edgeFinset.powerset, f s ≥ f t := by
      apply_rules [ Finset.exists_max_image ] ; aesop;
    obtain ⟨ s, hs₁, hs₂ ⟩ := h_exists_max;
    use s;
    simp +zetaDelta at *;
    refine' ⟨ hs₁, _ ⟩;
    refine' le_trans ( Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_right ( hs₂ t _ ) _ ) _;
    · exact fun x hx => by simpa using Finset.mem_powerset.mp ht hx;
    · exact mul_nonneg ( pow_nonneg hp_nonneg _ ) ( pow_nonneg ( sub_nonneg.2 hp_le_one ) _ );
    · rw [ ← Finset.mul_sum _ _ _, sum_prob_subgraph_eq_one ] ; norm_num

/-
X is the number of edges in the random subgraph, and Y is the number of C4 copies.
-/
def X_rv {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Sym2 V) → ℝ :=
  fun s => s.card

noncomputable def Y_rv {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Sym2 V) → ℝ :=
  fun s => (@c4_count V _ _ (SimpleGraph.fromEdgeSet s) (Classical.decRel _))

/-
The expectation of the number of edges in a random subgraph is p times the number of edges in the original graph.
-/
lemma expectation_X {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) :
  expectation_subgraph G p (X_rv G) = p * edge_count G := by
    -- Let's simplify the expression by factoring out common terms.
    have h_simp : ∑ t ∈ G.edgeFinset.powerset, t.card * p ^ t.card * (1 - p) ^ (G.edgeFinset.card - t.card) = p * ∑ t ∈ G.edgeFinset.powerset, t.card * p ^ (t.card - 1) * (1 - p) ^ (G.edgeFinset.card - t.card) := by
      rw [ Finset.mul_sum _ _ _ ];
      refine' Finset.sum_congr rfl fun t ht => _;
      cases t using Finset.induction <;> simp +decide [ *, pow_succ' ] ; ring;
    -- Let's simplify the expression by factoring out common terms and using the binomial theorem.
    have h_binom : ∑ t ∈ G.edgeFinset.powerset, t.card * p ^ (t.card - 1) * (1 - p) ^ (G.edgeFinset.card - t.card) = G.edgeFinset.card * (p + (1 - p)) ^ (G.edgeFinset.card - 1) := by
      have h_binom : ∑ t ∈ G.edgeFinset.powerset, t.card * p ^ (t.card - 1) * (1 - p) ^ (G.edgeFinset.card - t.card) = ∑ k ∈ Finset.range (G.edgeFinset.card + 1), k * p ^ (k - 1) * (1 - p) ^ (G.edgeFinset.card - k) * Nat.choose (G.edgeFinset.card) k := by
        rw [ Finset.sum_powerset ];
        refine' Finset.sum_congr rfl fun i hi => _;
        rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, Finset.card_powersetCard ];
      rw [ h_binom, add_pow ];
      rw [ Finset.sum_range_succ' ];
      rcases n : G.edgeFinset.card with ( _ | n ) <;> simp_all +decide [ Finset.mul_sum _ _ _ ];
      refine' Finset.sum_congr rfl fun i hi => _;
      rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith [ Finset.mem_range.mp hi ];
      field_simp;
      rw [ Nat.factorial_succ, Nat.factorial_succ ] ; push_cast [ Nat.succ_sub ( Finset.mem_range_succ_iff.mp hi ) ] ; ring;
    convert h_simp using 1;
    · exact Finset.sum_congr rfl fun _ _ => by unfold X_rv prob_subgraph; ring;
    · rw [ h_binom, edge_count ] ; norm_num

/-
Recall that c4_count is the cardinality of the set of C4 subgraphs.
-/
noncomputable def C4s {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : Finset G.Subgraph :=
  Finset.univ.filter (fun H => Nonempty (H.coe ≃g C4))

lemma c4_count_eq_card_C4s {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  c4_count G = (C4s G).card := by
    unfold c4_count C4s;
    rw [ Fintype.subtype_card ]

/-
Y is the sum of indicators of C4 subgraphs being contained in the random edge set.
-/
lemma Y_rv_eq_sum_indicators {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset (Sym2 V))
  (hs : s ⊆ G.edgeFinset) :
  Y_rv G s = ∑ H ∈ C4s G, if H.edgeSet.toFinset ⊆ s then 1 else 0 := by
    unfold Y_rv;
    simp +decide [ c4_count, C4s ];
    rw [ Fintype.card_subtype ];
    refine' Finset.card_bij _ _ _ _;
    use fun a ha => a.map ( SimpleGraph.Hom.ofLE ( show fromEdgeSet ↑s ≤ G from by
                                                    intro v w hvw;
                                                    exact hvw.elim fun h => by have := hs h; aesop; ) );
    · simp +zetaDelta at *;
      all_goals generalize_proofs at *;
      intro a ha
      generalize_proofs at *;
      refine' ⟨ ⟨ _ ⟩, _ ⟩;
      · refine' { Equiv.trans _ ha.toEquiv with .. };
        refine' Equiv.ofBijective ( fun x => ⟨ x, _ ⟩ ) ⟨ fun x y h => _, fun x => _ ⟩;
        all_goals simp_all +decide [ Equiv.trans_apply ];
        all_goals norm_num [ ha.map_adj_iff ];
        · aesop;
        · aesop;
      · exact fun e he => by have := a.edgeSet_subset he; aesop;
    · simp +decide [ Subgraph.map, Subgraph.ext_iff ];
    · simp +decide [ Subgraph.map ];
      intro b a ha;
      refine' ⟨ _, _, _ ⟩;
      exact ⟨ b.verts, fun v w => b.Adj v w ∧ s(v, w) ∈ s, by
        exact fun { v w } h => by have := hs h.2; aesop;, by
        exact fun { v w } h => b.edge_vert h.1, by
        exact fun v w h => ⟨ h.1.symm, by simpa only [ Sym2.eq_swap ] using ha h.1 ⟩ ⟩
      all_goals generalize_proofs at *;
      · refine' ⟨ _ ⟩;
        refine' { Equiv.ofBijective ( fun v => a v ) ⟨ _, _ ⟩ with .. };
        all_goals norm_num [ Function.Injective, Function.Surjective ];
        · exact fun x => ⟨ a.symm x |>.1, a.symm x |>.2, a.apply_symm_apply x ⟩;
        · intro v hv w hw; exact ⟨ fun h => by
            exact ⟨ by simpa using a.symm.map_rel_iff.mpr h, ha <| by simpa using a.symm.map_rel_iff.mpr h ⟩, fun h => by
            exact a.map_adj_iff.mpr h.1 ⟩;
      · aesop

/-
The sum of probabilities of subgraphs containing a fixed set of edges A is p^|A|.
-/
lemma prob_contains_edges {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ)
  (A : Finset (Sym2 V)) (hA : A ⊆ G.edgeFinset) :
  ∑ s ∈ G.edgeFinset.powerset, (if A ⊆ s then 1 else 0) * prob_subgraph G p s = p ^ A.card := by
    -- Let $s = A \cup t$ where $t \subseteq G.edgeFinset \setminus A$.
    have h_sum_subset : ∑ s ∈ Finset.powerset (G.edgeFinset \ A), (prob_subgraph G p (A ∪ s)) = p ^ A.card * ∑ t ∈ Finset.powerset (G.edgeFinset \ A), (p ^ t.card * (1 - p) ^ ((G.edgeFinset \ A).card - t.card)) := by
      rw [ Finset.mul_sum _ _ _ ];
      refine' Finset.sum_congr rfl fun s hs => _;
      unfold prob_subgraph; simp +decide [ Finset.card_sdiff, * ] ; ring_nf;
      rw [ ← pow_add, Finset.card_union_of_disjoint ];
      · rw [ Nat.sub_sub, Finset.inter_eq_left.mpr hA ];
      · exact Finset.disjoint_left.mpr fun x hx hx' => Finset.mem_sdiff.mp ( Finset.mem_powerset.mp hs hx' ) |>.2 hx;
    -- The sum $\sum_{t \subseteq G.edgeFinset \setminus A} p^t.card * (1 - p)^{(G.edgeFinset \ A).card - t.card}$ is equal to $(p + (1 - p))^{(G.edgeFinset \ A).card} = 1$.
    have h_sum_one : ∑ t ∈ Finset.powerset (G.edgeFinset \ A), p ^ t.card * (1 - p) ^ ((G.edgeFinset \ A).card - t.card) = (p + (1 - p)) ^ (G.edgeFinset \ A).card := by
      exact Finset.sum_pow_mul_eq_add_pow p (1 - p) (G.edgeFinset \ A);
    convert h_sum_subset using 1;
    · simp +decide [ Finset.subset_iff ];
      rw [ ← Finset.sum_filter ];
      refine' Finset.sum_bij ( fun s hs => s \ A ) _ _ _ _ <;> simp +contextual [ Finset.subset_iff ];
      · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; ext x; by_cases hx : x ∈ A <;> simp_all +decide [ Finset.ext_iff ] ;
      · exact fun b hb => ⟨ b ∪ A, ⟨ fun x hx => by aesop, fun x hx => by aesop ⟩, by aesop ⟩;
      · intro s hs hs'; rw [ Finset.union_eq_right.mpr hs' ] ;
    · aesop

/-
A C4 subgraph has 4 edges.
-/
lemma card_edgeSet_of_C4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (H : G.Subgraph) (hH : Nonempty (H.coe ≃g C4)) :
  H.edgeSet.toFinset.card = 4 := by
    have := hH.some;
    replace := this.card_edgeFinset_eq;
    convert this;
    · convert rfl;
      fapply Finset.card_bij;
      use fun a ha => Sym2.map ( fun x => x.val ) a;
      · aesop;
      · intro a₁ ha₁ a₂ ha₂ h; induction a₁ using Sym2.inductionOn ; induction a₂ using Sym2.inductionOn ; aesop;
      · rintro ⟨ u, v ⟩ huv;
        simp_all +decide [ SimpleGraph.Subgraph.edgeSet ];
        exact ⟨ Sym2.mk ( ⟨ u, H.edge_vert huv ⟩, ⟨ v, H.edge_vert huv.symm ⟩ ), by aesop ⟩;
    · simp +decide [ C4 ];
      simp +decide [ Finset.card ];
      simp +decide [ SimpleGraph.edgeSet ]

/-
The expectation of the number of C4 copies in a random subgraph is p^4 times the number of C4 copies in the original graph.
-/
lemma expectation_Y {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) :
  expectation_subgraph G p (Y_rv G) = p ^ 4 * (c4_count G : ℝ) := by
    -- Applying the definition of expectation_subgraph and Y_rv.
    have h_exp : expectation_subgraph G p (Y_rv G) = ∑ H ∈ C4s G, p ^ 4 := by
      -- By Fubini's theorem, we can interchange the order of summation.
      have h_fubini : ∑ s ∈ G.edgeFinset.powerset, (∑ H ∈ C4s G, (if H.edgeSet.toFinset ⊆ s then 1 else 0)) * prob_subgraph G p s = ∑ H ∈ C4s G, ∑ s ∈ G.edgeFinset.powerset, (if H.edgeSet.toFinset ⊆ s then 1 else 0) * prob_subgraph G p s := by
        rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_mul _ _ _ ];
      convert h_fubini using 1;
      · refine' Finset.sum_congr rfl fun s hs => _;
        rw [ Y_rv_eq_sum_indicators G s ( Finset.mem_powerset.mp hs ) ];
      · refine' Finset.sum_congr rfl fun H hH => _;
        convert prob_contains_edges G p ( H.edgeSet.toFinset ) _ |> Eq.symm using 1;
        · rw [ card_edgeSet_of_C4 G H ( Finset.mem_filter.mp hH |>.2 ) ];
        · simp +decide [ Finset.subset_iff ];
          exact fun x hx => H.edgeSet_subset hx;
    simp_all +decide [ mul_comm, c4_count_eq_card_C4s ]

/-
Expectation is linear.
-/
lemma expectation_linear {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ)
  (f g : Finset (Sym2 V) → ℝ) :
  expectation_subgraph G p (fun s => f s - g s) = expectation_subgraph G p f - expectation_subgraph G p g := by
    unfold expectation_subgraph;
    simp +decide only [sub_mul, Finset.sum_sub_distrib]

/-
The expectation of X - Y is pm - p^4 c4(G).
-/
lemma expectation_X_sub_Y {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (p : ℝ) :
  expectation_subgraph G p (fun s => X_rv G s - Y_rv G s) = p * edge_count G - p ^ 4 * c4_count G := by
    simp [expectation_subgraph, X_rv, Y_rv];
    rw [ Finset.sum_congr rfl fun s hs => by rw [ sub_mul ] ];
    rw [ Finset.sum_sub_distrib, ← expectation_X, ← expectation_Y ];
    rfl

/-
Every graph with m edges contains a C4-free subgraph with at least (15/32) * m^(2/3) edges.
-/
theorem erdos_1008 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∃ H : SimpleGraph V, H ≤ G ∧ is_C4_free H ∧ (edge_count H : ℝ) ≥ 15/32 * (edge_count G : ℝ) ^ ((2 : ℝ) / 3) := by
    -- Apply the provided solution to obtain the existence of such a subgraph $H$.
    obtain ⟨s, hs⟩ : ∃ s ∈ G.edgeFinset.powerset, (s.card : ℝ) - (Y_rv G s : ℝ) ≥ (15 / 32 : ℝ) * (edge_count G : ℝ) ^ (2 / 3 : ℝ) := by
      -- By Lemma `expectation_X_sub_Y`, we know that the expectation of $X - Y$ is at least $(15/32) * m^{2/3}$.
      have h_expectation : expectation_subgraph G (1 / 2 * (edge_count G : ℝ) ^ (-1 / 3 : ℝ)) (fun s => (X_rv G s : ℝ) - (Y_rv G s : ℝ)) ≥ (15 / 32 : ℝ) * (edge_count G : ℝ) ^ (2 / 3 : ℝ) := by
        -- Substitute the expectation formula from `expectation_X_sub_Y`.
        have h_subst : (1 / 2 : ℝ) * (edge_count G : ℝ) ^ (2 / 3 : ℝ) - (1 / 2 : ℝ) ^ 4 * (edge_count G : ℝ) ^ (-4 / 3 : ℝ) * (c4_count G : ℝ) ≥ (15 / 32 : ℝ) * (edge_count G : ℝ) ^ (2 / 3 : ℝ) := by
          -- Using the inequality $c4_count G \leq \binom{edge_count G}{2} \leq \frac{edge_count G^2}{2}$, we get:
          have h_c4_bound : (c4_count G : ℝ) ≤ (edge_count G : ℝ) ^ 2 / 2 := by
            have := c4_count_le_choose_two G;
            rw [ le_div_iff₀ ] <;> norm_cast;
            exact le_trans ( Nat.mul_le_mul_right _ this ) ( by induction' edge_count G with n ih <;> norm_num [ Nat.choose ] at * ; nlinarith );
          by_cases h : edge_count G = 0 <;> norm_num [ h ];
          rw [ show ( - ( 4 / 3 : ℝ ) ) = ( 2 / 3 : ℝ ) - 2 by norm_num, Real.rpow_sub ] <;> norm_num <;> try positivity;
          nlinarith [ show ( edge_count G : ℝ ) ^ ( 2 / 3 : ℝ ) > 0 by positivity, show ( edge_count G : ℝ ) ^ 2 > 0 by positivity, mul_div_cancel₀ ( ( edge_count G : ℝ ) ^ ( 2 / 3 : ℝ ) ) ( by positivity : ( edge_count G : ℝ ) ^ 2 ≠ 0 ) ];
        convert h_subst using 1;
        rw [ expectation_X_sub_Y ] ; ring_nf;
        rw [ ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num ; ring_nf;
        rw [ ← Real.rpow_add_one' ] <;> norm_num ; ring;
      have := exists_subgraph_ge_expectation G ( 1 / 2 * ( edge_count G : ℝ ) ^ ( -1 / 3 : ℝ ) ) ( fun s => ( s.card : ℝ ) - ( Y_rv G s : ℝ ) ) ?_ ?_ <;> norm_num at *;
      · exact ⟨ this.choose, this.choose_spec.1, h_expectation.trans this.choose_spec.2 ⟩;
      · positivity;
      · rcases k : edge_count G with ( _ | _ | k ) <;> norm_num [ k ] at *;
        exact le_trans ( mul_le_mul_of_nonneg_left ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show ( - ( 1 / 3 ) : ℝ ) ≤ 0 by norm_num ) ) ( by norm_num ) ) ( by norm_num );
    obtain ⟨H, hH₁, hH₂⟩ : ∃ H : SimpleGraph V, H ≤ SimpleGraph.fromEdgeSet s ∧ is_C4_free H ∧ edge_count H ≥ (s.card : ℝ) - (Y_rv G s : ℝ) := by
      have hC4_free_subgraph : ∀ (G : SimpleGraph V), ∃ H : SimpleGraph V, H ≤ G ∧ is_C4_free H ∧ edge_count H ≥ edge_count G - c4_count G := by
        exact fun G => exists_C4_free_subgraph_with_min_edges G;
      convert hC4_free_subgraph _;
      unfold edge_count Y_rv c4_count;
      simp +decide [ SimpleGraph.edgeFinset ];
      rw [ Finset.sdiff_eq_self_of_disjoint ] <;> norm_cast;
      simp +decide [ Finset.disjoint_left, Sym2.IsDiag ];
      rintro ⟨ u, v ⟩ hu hv; have := Finset.mem_powerset.mp hs.1 hu; simp_all +decide [ SimpleGraph.edgeFinset ] ;
    refine' ⟨ H, hH₁.trans _, hH₂.1, hH₂.2.trans' hs.2 ⟩;
    rintro v w ⟨ hvw, hvw' ⟩;
    exact G.mem_edgeSet.mp ( by simpa using Finset.mem_powerset.mp hs.1 ( by simpa using hvw ) )

#print axioms erdos_1008
-- 'erdos_1008' depends on axioms: [propext, Classical.choice, Quot.sound]
