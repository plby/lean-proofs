/-

This is a Lean formalization of a solution to Erdős Problem 794.
https://www.erdosproblems.com/forum/thread/794

It seems likely that the problem was mis-stated.  This file formalizes
a simple explicit counterexample due to Phillip Harris.

Aristotle and ChatGPT were used.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We construct a counterexample to the conjecture that every 3-uniform hypergraph on $3n$ vertices with at least $n^3+1$ edges contains a subgraph on 4 vertices with 3 edges or on 5 vertices with 7 edges.
For $n=3$, we consider a hypergraph on 9 vertices partitioned into three sets $S_1, S_2, S_3$ of size 3. The edges are all triples with exactly one vertex in each $S_i$, plus one additional edge contained entirely in $S_1$.
This hypergraph has $3^3 + 1 = 28$ edges.
We verify computationally that this hypergraph does not contain any subgraph on 4 vertices with 3 edges, nor any subgraph on 5 vertices with 7 edges.
-/

import Mathlib

/-
The hypergraph on 9 vertices with edges defined by a tripartite construction plus one extra edge is a counterexample to the claim. Specifically, it has 28 edges but contains no subgraph on 4 vertices with 3 edges and no subgraph on 5 vertices with 7 edges.
-/
def n_val : ℕ := 3

def V_set : Finset ℕ := Finset.Icc 1 9

def S1 : Finset ℕ := {1, 2, 3}
def S2 : Finset ℕ := {4, 5, 6}
def S3 : Finset ℕ := {7, 8, 9}

def multipartite_edges : Finset (Finset ℕ) :=
  (S1.product S2).product S3 |>.image (fun ((x, y), z) => {x, y, z})

def extra_edge : Finset ℕ := {1, 2, 3}

def counterexample_edges : Finset (Finset ℕ) := multipartite_edges ∪ {extra_edge}

def has_subgraph (E : Finset (Finset ℕ)) (v_count e_count : ℕ) : Prop :=
  ∃ s, s ⊆ V_set ∧ s.card = v_count ∧ (E.filter (fun e => e ⊆ s)).card ≥ e_count

set_option maxRecDepth 4000 in
theorem counterexample_disproves_conjecture :
  (∀ e ∈ counterexample_edges, e.card = 3) ∧
  counterexample_edges.card ≥ n_val^3 + 1 ∧
  ¬ has_subgraph counterexample_edges 4 3 ∧
  ¬ has_subgraph counterexample_edges 5 7 := by
    unfold has_subgraph;
    decide

def erdos_794 : Prop :=
  ∀ (n : ℕ) (V : Finset ℕ) (E : Finset (Finset ℕ)),
    V.card = 3 * n →
    (∀ e ∈ E, e.card = 3) →
    E.card ≥ n^3 + 1 →
      has_subgraph E 4 3 ∨ has_subgraph E 5 7

theorem not_erdos_794 : ¬erdos_794 := by
  intro h
  have hce := counterexample_disproves_conjecture
  have hinst :
      has_subgraph counterexample_edges 4 3 ∨ has_subgraph counterexample_edges 5 7 :=
    h n_val (Finset.range (3 * n_val)) counterexample_edges (by simp) hce.1 hce.2.1
  simp_all only [ge_iff_le, or_self]

#print axioms not_erdos_794
-- 'not_erdos_794' depends on axioms: [propext, Classical.choice, Quot.sound]
