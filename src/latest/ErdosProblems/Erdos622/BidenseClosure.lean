/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.DiracStability

/-!
# Closure obstructions for the bi-dense case of Erdős Problem 622

This file isolates everything that follows directly from the
Bondy--Chvátal closure theorem in the near-Dirac range.  In particular, a
non-Hamiltonian graph has two distinct nonadjacent vertices in its closure
whose closure degrees have sum below the order of the graph.  The closure
non-neighbourhood of either endpoint is large in a near-Dirac graph, and all
of its vertices have closure degree at most its cardinality.

These facts are useful input to a stability proof, but deliberately do not
claim that bi-density alone makes the Ore inequality hold pointwise.  The
passage from these local closure obstructions to the large independent or
sparse-pair alternatives is the substantive stability argument.
-/

open Finset
open scoped SimpleGraph

namespace Erdos622
namespace BidenseClosure

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Ore's theorem with the customary restriction to *distinct* nonadjacent
vertices.  The locally vendored statement of `SimpleGraph.ore_theorem` also
tests a vertex against itself; the closure proof gives the standard version
without that extra hypothesis. -/
theorem ore_of_distinct_nonadjacent_degree_sum
    (hV : 3 ≤ Fintype.card V)
    (hOre : ∀ ⦃u v : V⦄, u ≠ v → ¬ G.Adj u v →
      Fintype.card V ≤ G.degree u + G.degree v) :
    G.IsHamiltonian := by
  have htop : G.closure = (⊤ : SimpleGraph V) := by
    rw [SimpleGraph.eq_top_iff_forall_ne_adj]
    intro u v huv
    by_cases hadj : G.Adj u v
    · exact SimpleGraph.self_le_closure G hadj
    · apply SimpleGraph.closure_spec G huv
      calc
        Fintype.card V ≤ G.degree u + G.degree v := hOre huv hadj
        _ ≤ G.closure.degree u + G.closure.degree v :=
          add_le_add
            (G.degree_le_of_le (v := u) (SimpleGraph.self_le_closure G))
            (G.degree_le_of_le (v := v) (SimpleGraph.self_le_closure G))
  apply SimpleGraph.from_closure_iff.mp
  rw [htop]
  apply SimpleGraph.dirac_theorem hV
  intro u
  simp only [SimpleGraph.complete_graph_degree]
  omega

/-- A non-Hamiltonian graph has a genuine (distinct-vertex) Ore obstruction
in its Bondy--Chvátal closure. -/
theorem exists_closure_ore_obstruction
    (hV : 3 ≤ Fintype.card V) (hNonHam : ¬ G.IsHamiltonian) :
    ∃ u v : V, u ≠ v ∧ ¬ G.closure.Adj u v ∧
      G.closure.degree u + G.closure.degree v < Fintype.card V := by
  have hClosureNonHam : ¬ G.closure.IsHamiltonian := by
    exact fun h ↦ hNonHam (SimpleGraph.from_closure_iff.mp h)
  have hClosureNotTop : G.closure ≠ (⊤ : SimpleGraph V) := by
    intro htop
    apply hClosureNonHam
    rw [htop]
    apply SimpleGraph.dirac_theorem hV
    intro u
    simp only [SimpleGraph.complete_graph_degree]
    omega
  have hMissing : ∃ u v : V, u ≠ v ∧ ¬ G.closure.Adj u v := by
    by_contra h
    push Not at h
    exact hClosureNotTop
      (SimpleGraph.eq_top_iff_forall_ne_adj.mpr fun u v huv ↦ h u v huv)
  obtain ⟨u, v, huv, hadj⟩ := hMissing
  refine ⟨u, v, huv, hadj, ?_⟩
  have hnot : ¬ Fintype.card V ≤
      G.closure.degree u + G.closure.degree v := by
    intro hsum
    exact hadj (SimpleGraph.closure_spec G huv hsum)
  omega

/-- The vertices other than `u` which remain nonadjacent to `u` after taking
the Bondy--Chvátal closure. -/
noncomputable def closureNonneighbors (G : SimpleGraph V) (u : V) : Finset V :=
  G.closureᶜ.neighborFinset u

@[simp] theorem mem_closureNonneighbors {u v : V} :
    v ∈ closureNonneighbors G u ↔ u ≠ v ∧ ¬ G.closure.Adj u v := by
  simp [closureNonneighbors, SimpleGraph.mem_neighborFinset,
    SimpleGraph.compl_adj]

theorem card_closureNonneighbors (G : SimpleGraph V) (u : V) :
    (closureNonneighbors G u).card =
      Fintype.card V - 1 - G.closure.degree u := by
  rw [closureNonneighbors, SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.degree_compl]

/-- Every closure non-neighbour of `u` has closure degree at most the number
of closure non-neighbours of `u`.  This is the basic degree-sequence
constraint supplied by saturation of the Bondy--Chvátal closure. -/
theorem closure_degree_le_card_nonneighbors {u v : V}
    (hv : v ∈ closureNonneighbors G u) :
    G.closure.degree v ≤ (closureNonneighbors G u).card := by
  have hmem := (mem_closureNonneighbors (G := G)).mp hv
  have hsum : G.closure.degree u + G.closure.degree v < Fintype.card V := by
    have hnot : ¬ Fintype.card V ≤
        G.closure.degree u + G.closure.degree v := by
      intro hge
      exact hmem.2 (SimpleGraph.closure_spec G hmem.1 hge)
    omega
  rw [card_closureNonneighbors]
  omega

/-- At an Ore obstruction, each endpoint belongs to the other endpoint's
closure non-neighbourhood. -/
theorem obstruction_endpoints_mem_nonneighbors {u v : V}
    (huv : u ≠ v) (hadj : ¬ G.closure.Adj u v) :
    v ∈ closureNonneighbors G u ∧ u ∈ closureNonneighbors G v := by
  constructor
  · exact mem_closureNonneighbors.mpr ⟨huv, hadj⟩
  · exact mem_closureNonneighbors.mpr ⟨huv.symm, fun h ↦ hadj h.symm⟩

/-- If `u,v` are an Ore obstruction, the closure non-neighbourhood of either
endpoint is at least as large as the closure degree of the other endpoint. -/
theorem obstruction_degrees_le_nonneighbor_cards {u v : V}
    (hsum : G.closure.degree u + G.closure.degree v < Fintype.card V) :
    G.closure.degree v ≤ (closureNonneighbors G u).card ∧
      G.closure.degree u ≤ (closureNonneighbors G v).card := by
  rw [card_closureNonneighbors, card_closureNonneighbors]
  omega

/-- A doubled near-Dirac lower bound is inherited by the closure. -/
theorem closure_nearDirac_of_nearDirac (r : ℕ)
    (hmin : ∀ w : V, Fintype.card V ≤ 2 * (G.degree w + r)) :
    ∀ w : V, Fintype.card V ≤ 2 * (G.closure.degree w + r) := by
  intro w
  have hmono : G.degree w ≤ G.closure.degree w :=
    G.degree_le_of_le (v := w) (SimpleGraph.self_le_closure G)
  have hbase := hmin w
  omega

/-- In a graph within `r` of the Dirac degree threshold, both closure
non-neighbourhoods exposed by an Ore obstruction are themselves within `r`
of half the vertex set.  This is the strongest large-set conclusion obtained
from the single closure obstruction without the separate stability
argument. -/
theorem obstruction_nonneighbor_cards_near_half (r : ℕ)
    (hmin : ∀ w : V, Fintype.card V ≤ 2 * (G.degree w + r))
    {u v : V}
    (hsum : G.closure.degree u + G.closure.degree v < Fintype.card V) :
    Fintype.card V ≤ 2 * ((closureNonneighbors G u).card + r) ∧
      Fintype.card V ≤ 2 * ((closureNonneighbors G v).card + r) := by
  have hclosure := closure_nearDirac_of_nearDirac (G := G) r hmin
  have hcards := obstruction_degrees_le_nonneighbor_cards (G := G) hsum
  constructor
  · exact (hclosure v).trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hcards.1 r))
  · exact (hclosure u).trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hcards.2 r))

/-- Packaged consequence for a non-Hamiltonian near-Dirac graph: a distinct
closure nonedge with sub-Ore degree sum and two large closure
non-neighbourhoods. -/
theorem exists_large_closure_obstruction
    (hV : 3 ≤ Fintype.card V) (r : ℕ)
    (hmin : ∀ w : V, Fintype.card V ≤ 2 * (G.degree w + r))
    (hNonHam : ¬ G.IsHamiltonian) :
    ∃ u v : V,
      u ≠ v ∧ ¬ G.closure.Adj u v ∧
      G.closure.degree u + G.closure.degree v < Fintype.card V ∧
      Fintype.card V ≤ 2 * ((closureNonneighbors G u).card + r) ∧
      Fintype.card V ≤ 2 * ((closureNonneighbors G v).card + r) := by
  obtain ⟨u, v, huv, hadj, hsum⟩ :=
    exists_closure_ore_obstruction (G := G) hV hNonHam
  obtain ⟨hu, hv⟩ :=
    obstruction_nonneighbor_cards_near_half (G := G) r hmin hsum
  exact ⟨u, v, huv, hadj, hsum, hu, hv⟩

omit [DecidableEq V] in
/-- Bi-density at the minimum-degree scale gives a three-edge connector
between every ordered pair of vertices: choose one neighbour of each endpoint
from an edge between their two neighbourhoods.  This is the local robust
connectivity fact used after the closure reduction in standard proofs of the
Dirac stability lemma. -/
theorem exists_three_edge_connector_of_biDenseAbove
    {k b : ℕ} (hDense : DiracStability.BiDenseAbove G k b)
    {u v : V} (hu : k ≤ G.degree u) (hv : k ≤ G.degree v) :
    ∃ x y : V, G.Adj u x ∧ G.Adj x y ∧ G.Adj y v := by
  have hmany := hDense (G.neighborFinset u) (G.neighborFinset v)
    (by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hu)
    (by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hv)
  have hpos : 0 < (G.interedges (G.neighborFinset u)
      (G.neighborFinset v)).card := by
    exact (Nat.zero_le b).trans_lt hmany
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  have he' :
      (e.1 ∈ G.neighborFinset u ∧ e.2 ∈ G.neighborFinset v) ∧
        G.Adj e.1 e.2 := by
    simpa [SimpleGraph.interedges_def] using he
  exact ⟨e.1, e.2,
    (G.mem_neighborFinset u e.1).mp he'.1.1,
    he'.2,
    ((G.mem_neighborFinset v e.2).mp he'.1.2).symm⟩

end BidenseClosure
end Erdos622
