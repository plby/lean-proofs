import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Set.PowersetCard
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-!
# The uniform fixed-edge random-graph model

This file gives an exact finite model of `G(n, m)`.  A sample is an
`m`-element subset of the edge type of the complete graph on `Fin n`; its
probability is the corresponding finite count divided by the total number of
samples.  We also give the deterministic part of the usual random-order
coupling: revealing a prefix of one ordering of all edges produces nested
graphs, so every increasing graph property (in particular Hamiltonicity) is
preserved as more edges are revealed.
-/

namespace Erdos746

open Filter

noncomputable section

/-- The set of all possible (non-loop) edges on `Fin n`. -/
def completeEdgeSet (n : ℕ) : Set (Sym2 (Fin n)) :=
  (⊤ : SimpleGraph (Fin n)).edgeSet

/-- The finite type of possible edges on `Fin n`, presented as the subtype of
the complete graph's edge finset. -/
abbrev Edge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeFinset

/-- The number of possible edges on `n` labelled vertices. -/
def edgeCount (n : ℕ) : ℕ := n.choose 2

/-- The inclusion of the edge type into unordered pairs of vertices. -/
def edgeEmbedding (n : ℕ) : Edge n ↪ Sym2 (Fin n) :=
  Function.Embedding.subtype
    (fun e => e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset)

/-- The complete graph on `Fin n` has exactly `n.choose 2` possible edges. -/
@[simp]
theorem card_edge (n : ℕ) : Fintype.card (Edge n) = edgeCount n := by
  change Fintype.card ↥((⊤ : SimpleGraph (Fin n)).edgeFinset) = edgeCount n
  rw [Fintype.card_coe, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp [edgeCount]

/-- Turn a finite set of possible edges into the corresponding simple graph. -/
def graphOfEdges {n : ℕ} (s : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (s.map (edgeEmbedding n) : Set (Sym2 (Fin n)))

theorem coe_map_edgeEmbedding_subset_complete {n : ℕ} (s : Finset (Edge n)) :
    (s.map (edgeEmbedding n) : Set (Sym2 (Fin n))) ⊆ completeEdgeSet n := by
  intro e he
  simp only [Finset.mem_coe, Finset.mem_map] at he
  obtain ⟨e, _he, rfl⟩ := he
  exact SimpleGraph.mem_edgeFinset.mp e.property

theorem map_edgeEmbedding_disjoint_diag {n : ℕ} (s : Finset (Edge n)) :
    Disjoint (s.map (edgeEmbedding n) : Set (Sym2 (Fin n))) Sym2.diagSet := by
  rw [Set.disjoint_left]
  intro e hes hediag
  have hecomplete := coe_map_edgeEmbedding_subset_complete s hes
  have hnondiag : e ∉ Sym2.diagSet := by
    simpa [completeEdgeSet, SimpleGraph.edgeSet_top] using hecomplete
  exact hnondiag hediag

/-- No edge is lost when a set of elements of `Edge n` is converted to a
simple graph. -/
@[simp]
theorem edgeSet_graphOfEdges {n : ℕ} (s : Finset (Edge n)) :
    (graphOfEdges s).edgeSet = (s.map (edgeEmbedding n) : Set (Sym2 (Fin n))) := by
  rw [graphOfEdges, SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left]
  exact map_edgeEmbedding_disjoint_diag s

@[simp]
theorem ncard_edgeSet_graphOfEdges {n : ℕ} (s : Finset (Edge n)) :
    (graphOfEdges s).edgeSet.ncard = s.card := by
  rw [edgeSet_graphOfEdges, Set.ncard_coe_finset, Finset.card_map]

theorem graphOfEdges_mono {n : ℕ} {s t : Finset (Edge n)} (hst : s ⊆ t) :
    graphOfEdges s ≤ graphOfEdges t := by
  rw [← SimpleGraph.edgeSet_subset_edgeSet]
  simp only [edgeSet_graphOfEdges, Finset.coe_subset]
  exact Finset.map_subset_map.mpr hst

/-- The exact sample space for the uniform model `G(n, m)`. -/
abbrev FixedEdgeGraph (n m : ℕ) := Set.powersetCard (Edge n) m

namespace FixedEdgeGraph

/-- The simple graph represented by a sample from `G(n, m)`. -/
def graph {n m : ℕ} (G : FixedEdgeGraph n m) : SimpleGraph (Fin n) :=
  graphOfEdges G.1

@[simp]
theorem edgeSet_graph {n m : ℕ} (G : FixedEdgeGraph n m) :
    (FixedEdgeGraph.graph G).edgeSet =
      (G.1.map (edgeEmbedding n) : Set (Sym2 (Fin n))) := by
  simp [graph]

/-- Every sample in `G(n, m)` really has exactly `m` edges. -/
@[simp]
theorem ncard_edgeSet_graph {n m : ℕ} (G : FixedEdgeGraph n m) :
    (FixedEdgeGraph.graph G).edgeSet.ncard = m := by
  rw [edgeSet_graph, Set.ncard_coe_finset, Finset.card_map,
    Set.powersetCard.card_eq]

theorem graph_injective {n m : ℕ} :
    Function.Injective (graph : FixedEdgeGraph n m → SimpleGraph (Fin n)) := by
  intro G H hGH
  apply Subtype.ext
  have hEdges : (FixedEdgeGraph.graph G).edgeSet =
      (FixedEdgeGraph.graph H).edgeSet := congrArg SimpleGraph.edgeSet hGH
  simpa only [edgeSet_graph, Finset.coe_inj, Finset.map_inj] using hEdges

end FixedEdgeGraph

/-- The sample-space cardinality is the expected binomial coefficient. -/
@[simp]
theorem card_fixedEdgeGraph (n m : ℕ) :
    Fintype.card (FixedEdgeGraph n m) = (edgeCount n).choose m := by
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card,
    ← Fintype.card_eq_nat_card, card_edge]

theorem card_fixedEdgeGraph_choose (n m : ℕ) :
    Fintype.card (FixedEdgeGraph n m) = (n.choose 2).choose m := by
  simpa [edgeCount] using card_fixedEdgeGraph n m

/-- The fixed-edge sample space is inhabited whenever `m` does not exceed
the number of possible edges. -/
theorem nonempty_fixedEdgeGraph {n m : ℕ} (hm : m ≤ edgeCount n) :
    Nonempty (FixedEdgeGraph n m) := by
  rw [← Fintype.card_pos_iff]
  rw [card_fixedEdgeGraph]
  exact Nat.choose_pos hm

theorem nonempty_fixedEdgeGraph_iff {n m : ℕ} :
    Nonempty (FixedEdgeGraph n m) ↔ m ≤ edgeCount n := by
  constructor
  · intro h
    by_contra hmn
    have hlt : edgeCount n < m := Nat.lt_of_not_ge hmn
    have hpos : 0 < Fintype.card (FixedEdgeGraph n m) := Fintype.card_pos
    rw [card_fixedEdgeGraph, Nat.choose_eq_zero_of_lt hlt] at hpos
    exact Nat.lt_asymm hpos hpos
  · exact nonempty_fixedEdgeGraph

/-- Uniform probability of an event on an arbitrary finite sample space.
For an empty sample space it is, by the field convention `0 / 0 = 0`, equal
to zero. -/
def uniformProbability {Ω : Type*} [Fintype Ω] (event : Ω → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter event).card : ℝ) / Fintype.card Ω

theorem uniformProbability_nonneg {Ω : Type*} [Fintype Ω]
    (event : Ω → Prop) : 0 ≤ uniformProbability event := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem uniformProbability_le_one {Ω : Type*} [Fintype Ω]
    (event : Ω → Prop) : uniformProbability event ≤ 1 := by
  classical
  cases isEmpty_or_nonempty Ω with
  | inl h => simp [uniformProbability]
  | inr h =>
      rw [uniformProbability, div_le_one (by exact_mod_cast Fintype.card_pos)]
      exact_mod_cast Finset.card_filter_le (Finset.univ : Finset Ω) event

theorem uniformProbability_mono {Ω : Type*} [Fintype Ω]
    {event₁ event₂ : Ω → Prop} (h : ∀ ω, event₁ ω → event₂ ω) :
    uniformProbability event₁ ≤ uniformProbability event₂ := by
  classical
  rw [uniformProbability, uniformProbability]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω)

@[simp]
theorem uniformProbability_false {Ω : Type*} [Fintype Ω] :
    uniformProbability (fun _ : Ω => False) = 0 := by
  simp [uniformProbability]

@[simp]
theorem uniformProbability_true {Ω : Type*} [Fintype Ω] [Nonempty Ω] :
    uniformProbability (fun _ : Ω => True) = 1 := by
  simp [uniformProbability, ne_of_gt (show (0 : ℝ) < Fintype.card Ω by exact_mod_cast Fintype.card_pos)]

/-- The (real-valued) probability that a uniform `m`-edge graph on `Fin n`
is Hamiltonian. -/
def hamiltonianProbability (n m : ℕ) : ℝ :=
  uniformProbability (fun G : FixedEdgeGraph n m =>
    (FixedEdgeGraph.graph G).IsHamiltonian)

/-- The number of Hamiltonian samples in the exact fixed-edge sample space. -/
def hamiltonianCount (n m : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun G : FixedEdgeGraph n m =>
      (FixedEdgeGraph.graph G).IsHamiltonian)).card

theorem hamiltonianProbability_eq_count_div_choose (n m : ℕ) :
    hamiltonianProbability n m =
      (hamiltonianCount n m : ℝ) /
        ((edgeCount n).choose m : ℕ) := by
  classical
  simp only [hamiltonianProbability, hamiltonianCount, uniformProbability,
    card_fixedEdgeGraph]

theorem hamiltonianCount_le_choose (n m : ℕ) :
    hamiltonianCount n m ≤ (edgeCount n).choose m := by
  classical
  rw [← card_fixedEdgeGraph]
  exact Finset.card_filter_le (Finset.univ : Finset (FixedEdgeGraph n m)) _

theorem hamiltonianProbability_nonneg (n m : ℕ) :
    0 ≤ hamiltonianProbability n m :=
  uniformProbability_nonneg _

theorem hamiltonianProbability_le_one (n m : ℕ) :
    hamiltonianProbability n m ≤ 1 :=
  uniformProbability_le_one _

theorem hamiltonianProbability_mem_Icc (n m : ℕ) :
    hamiltonianProbability n m ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hamiltonianProbability_nonneg n m, hamiltonianProbability_le_one n m⟩

/-- A sequence of edge counts has Hamiltonicity with high probability when
the exact `G(n,m(n))` probabilities tend to one. -/
def HamiltonianWithHighProbability (m : ℕ → ℕ) : Prop :=
  Tendsto (fun n => hamiltonianProbability n (m n)) atTop (nhds 1)

/-! ## Deterministic random-order coupling interface -/

/-- An ordering of all possible edges of the complete graph.  A uniformly
random element of this finite type is the standard random-order coupling. -/
abbrev EdgeOrdering (n : ℕ) := Fin (edgeCount n) ≃ Edge n

/-- There is an edge ordering for every `n`, including the degenerate cases. -/
def canonicalEdgeOrdering (n : ℕ) : EdgeOrdering n :=
  (Fintype.equivFinOfCardEq (card_edge n)).symm

/-- The first `m` edges in an ordering.  If `m` exceeds the total number of
edges, this is simply the full edge set. -/
def prefixEdges {n : ℕ} (order : EdgeOrdering n) (m : ℕ) : Finset (Edge n) :=
  (Finset.univ.filter (fun i : Fin (edgeCount n) => (i : ℕ) < m)).map order.toEmbedding

@[simp]
theorem card_prefixEdges {n : ℕ} (order : EdgeOrdering n) (m : ℕ) :
    (prefixEdges order m).card = min (edgeCount n) m := by
  simp [prefixEdges, Fin.card_filter_val_lt]

theorem prefixEdges_mono {n : ℕ} (order : EdgeOrdering n) {m k : ℕ} (hmk : m ≤ k) :
    prefixEdges order m ⊆ prefixEdges order k := by
  rw [prefixEdges, prefixEdges, Finset.map_subset_map]
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact lt_of_lt_of_le hi hmk

/-- The graph obtained after revealing the first `m` edges in an ordering. -/
def orderedGraph {n : ℕ} (order : EdgeOrdering n) (m : ℕ) : SimpleGraph (Fin n) :=
  graphOfEdges (prefixEdges order m)

@[simp]
theorem ncard_edgeSet_orderedGraph {n : ℕ} (order : EdgeOrdering n) (m : ℕ) :
    (orderedGraph order m).edgeSet.ncard = min (edgeCount n) m := by
  rw [orderedGraph, ncard_edgeSet_graphOfEdges, card_prefixEdges]

theorem orderedGraph_mono {n : ℕ} (order : EdgeOrdering n) {m k : ℕ} (hmk : m ≤ k) :
    orderedGraph order m ≤ orderedGraph order k :=
  graphOfEdges_mono (prefixEdges_mono order hmk)

/-- Hamiltonicity is increasing along every edge-ordering coupling. -/
theorem orderedGraph_isHamiltonian_mono {n : ℕ} (order : EdgeOrdering n)
    {m k : ℕ} (hmk : m ≤ k) (hham : (orderedGraph order m).IsHamiltonian) :
    (orderedGraph order k).IsHamiltonian :=
  hham.mono (orderedGraph_mono order hmk)

/-- For a valid edge count, a prefix is canonically a sample from `G(n,m)`. -/
def prefixFixedEdgeGraph {n m : ℕ} (order : EdgeOrdering n) (hm : m ≤ edgeCount n) :
    FixedEdgeGraph n m :=
  ⟨prefixEdges order m, by simp [Nat.min_eq_right hm]⟩

@[simp]
theorem graph_prefixFixedEdgeGraph {n m : ℕ} (order : EdgeOrdering n)
    (hm : m ≤ edgeCount n) :
    FixedEdgeGraph.graph (prefixFixedEdgeGraph order hm) = orderedGraph order m :=
  rfl

/-- Pointwise coupling statement in the exact fixed-edge sample types. -/
theorem prefixFixedEdgeGraph_isHamiltonian_mono {n m k : ℕ}
    (order : EdgeOrdering n) (hm : m ≤ edgeCount n) (hk : k ≤ edgeCount n)
    (hmk : m ≤ k)
    (hham : (FixedEdgeGraph.graph (prefixFixedEdgeGraph order hm)).IsHamiltonian) :
    (FixedEdgeGraph.graph (prefixFixedEdgeGraph order hk)).IsHamiltonian := by
  simpa only [graph_prefixFixedEdgeGraph] using
    orderedGraph_isHamiltonian_mono order hmk hham

end

end Erdos746
