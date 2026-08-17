/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos58.Arithmetic
import ErdosProblems.Erdos58.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

/-!
# The sharp endgame for Erdős Problem 58

This file isolates two parts of the sharp argument which are independent of
the geometric construction of the cycles.

* `unequal_endpoint_exception` and `equal_endpoint_exception` are the exact
  natural-number case splits at the end of Gyárfás's proof.  Thus the
  endpoint-counting lemma leaves only the three boundary configurations dealt
  with by Lemmas 6--8 of the paper.
* `index_eq_of_complete_iso_and_minDegree` and
  `complete_iso_impossible_of_strict_minDegree` are the critical-graph
  endgame.  Once the structural theorem identifies a critical induced graph
  with `K_(2*j+2)`, its minimum degree determines whether `j = k` (the sharp
  equality case) or gives an immediate contradiction (the upper bound).

There are no graph-theoretic assumptions hidden in these statements: the
geometric structural theorem must provide an actual graph isomorphism, and
the critical-subgraph argument must provide the displayed degree bound.
-/

namespace Erdos58.AlternativeSharp

open SimpleGraph

universe u

/-! ## The final arithmetic case split -/

/-- In the unequal-neighborhood case, the endpoint lower bound
`ceilHalf p + q` is already strictly larger than `j`, except at the unique
boundary pair `p = 2*j, q = 0`.

This is the numerical content behind the invocation of Gyárfás's Lemma 8.
-/
theorem unequal_endpoint_exception {j p q : ℕ} (hj : 0 < j) (hp : 0 < p)
    (hdegree : 2 * j ≤ p + q)
    (hcount : Arithmetic.ceilHalf p + q ≤ j) :
    q = 0 ∧ p = 2 * j := by
  unfold Arithmetic.ceilHalf at hcount
  omega

/-- Contrapositive, conclusion-oriented form of
`unequal_endpoint_exception`. -/
theorem unequal_endpoint_strict_or_boundary {j p q : ℕ} (hj : 0 < j)
    (hp : 0 < p) (hdegree : 2 * j ≤ p + q) :
    j < Arithmetic.ceilHalf p + q ∨ (q = 0 ∧ p = 2 * j) := by
  by_cases h : j < Arithmetic.ceilHalf p + q
  · exact Or.inl h
  · exact Or.inr (unequal_endpoint_exception hj hp hdegree (by omega))

/-- In the equal-neighborhood case, the endpoint argument is applied after
discarding one common cycle neighbor.  Failure of strictness leaves exactly
the configurations handled by Gyárfás's Lemmas 6 and 7:

* `q = 1, p = 2*j-1`;
* `q = 0, p = 2*j`;
* `q = 0, p = 2*j+1`.
-/
theorem equal_endpoint_exception {j p q : ℕ} (hj : 0 < j) (hp : 0 < p)
    (hdegree : 2 * j ≤ p + q)
    (hcount : Arithmetic.ceilHalf (p - 1) + q ≤ j) :
    (q = 1 ∧ p = 2 * j - 1) ∨
      (q = 0 ∧ (p = 2 * j ∨ p = 2 * j + 1)) := by
  unfold Arithmetic.ceilHalf at hcount
  omega

/-- Contrapositive, conclusion-oriented form of `equal_endpoint_exception`.
-/
theorem equal_endpoint_strict_or_boundary {j p q : ℕ} (hj : 0 < j)
    (hp : 0 < p) (hdegree : 2 * j ≤ p + q) :
    j < Arithmetic.ceilHalf (p - 1) + q ∨
      (q = 1 ∧ p = 2 * j - 1) ∨
      (q = 0 ∧ (p = 2 * j ∨ p = 2 * j + 1)) := by
  by_cases h : j < Arithmetic.ceilHalf (p - 1) + q
  · exact Or.inl h
  · exact Or.inr (equal_endpoint_exception hj hp hdegree (by omega))

/-! ## Critical complete graphs -/

variable {X : Type u} [Fintype X]
variable (H : SimpleGraph X) [DecidableRel H.Adj]

/-- An isomorphism with `K_(2*j+2)` fixes the number of vertices of the
graph. -/
theorem card_eq_of_complete_iso {j : ℕ}
    (e : H ≃g SimpleGraph.completeGraph (Fin (2 * j + 2))) :
    Fintype.card X = 2 * j + 2 := by
  simpa using Fintype.card_congr e.toEquiv

/-- The sharp critical-graph calculation.

If `H ≅ K_(2*j+2)`, `j ≤ k`, and every vertex of `H` has degree at
least `2*k+1`, then necessarily `j = k`.  Notice that only the universal
bound `degree < |V|` is used; no completeness calculation is smuggled into
the proof.
-/
theorem index_eq_of_complete_iso_and_minDegree {j k : ℕ} (hjk : j ≤ k)
    (e : H ≃g SimpleGraph.completeGraph (Fin (2 * j + 2)))
    (hdegree : ∀ v : X, 2 * k + 1 ≤ H.degree v) :
    j = k := by
  let v : X := e.symm 0
  have hcard : Fintype.card X = 2 * j + 2 := card_eq_of_complete_iso H e
  have hlt : H.degree v < Fintype.card X := H.degree_lt_card_verts v
  have hkj : k ≤ j := by
    have := hdegree v
    omega
  exact Nat.le_antisymm hjk hkj

/-- A critical graph whose minimum degree is one larger than the degree of
`K_(2*k+2)` cannot be a smaller complete graph from the structural theorem.
This is the contradiction used for the `2*k+2`-color upper bound.
-/
theorem complete_iso_impossible_of_strict_minDegree {j k : ℕ} (hjk : j ≤ k)
    (hdegree : ∀ v : X, 2 * k + 2 ≤ H.degree v) :
    ¬Nonempty (H ≃g SimpleGraph.completeGraph (Fin (2 * j + 2))) := by
  rintro ⟨e⟩
  let v : X := e.symm 0
  have hcard : Fintype.card X = 2 * j + 2 := card_eq_of_complete_iso H e
  have hlt : H.degree v < Fintype.card X := H.degree_lt_card_verts v
  have := hdegree v
  omega

/-! ## Transport from a critical induced subgraph -/

variable {V : Type u} (G : SimpleGraph V)

/-- If an induced subgraph is isomorphic to the complete graph, then the
ambient graph contains that complete graph.  This is the exact containment
notion used in the equality statement of Problem 58.
-/
theorem completeGraph_isContained_of_induce_iso {s : Set V} {m : ℕ}
    (e : G.induce s ≃g SimpleGraph.completeGraph (Fin m)) :
    SimpleGraph.completeGraph (Fin m) ⊑ G := by
  exact e.isContained'.trans
    (SimpleGraph.Embedding.induce s).toCopy.isContained

/-- The two numerical conclusions of the sharp critical endgame, bundled in
the form used after applying the structural theorem to an induced graph.
-/
theorem sharp_critical_endgame {s : Set V} {j k : ℕ}
    [Fintype s] [DecidableRel (G.induce s).Adj]
    (hjk : j ≤ k)
    (e : G.induce s ≃g SimpleGraph.completeGraph (Fin (2 * j + 2)))
    (hdegree : ∀ v : s, 2 * k + 1 ≤ (G.induce s).degree v) :
    j = k ∧ SimpleGraph.completeGraph (Fin (2 * k + 2)) ⊑ G := by
  have hjk' : j = k :=
    index_eq_of_complete_iso_and_minDegree (H := G.induce s) hjk e hdegree
  subst j
  exact ⟨rfl, completeGraph_isContained_of_induce_iso G e⟩

end Erdos58.AlternativeSharp
