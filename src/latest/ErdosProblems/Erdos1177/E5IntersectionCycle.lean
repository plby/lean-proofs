-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E5Obstructions

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Induced cycles in the edge-intersection graph

This file gives a second, graph-theoretic finite endpoint for the
Hajnal--Komjáth E5 argument.  The vertices of the edge-intersection graph are
host hyperedges, with two distinct hyperedges adjacent when they meet.  In a
linear triple system, an induced seven-cycle in this graph is automatically a
clean loose seven-cycle in the hypergraph.
-/

namespace Erdos1177

universe u

variable {W : Type u}

/-- The intersection graph (line graph) of a hypergraph.  Its vertices are
host edges; distinct vertices are adjacent exactly when the corresponding
hyperedges intersect. -/
def edgeIntersectionGraph (H : Hypergraph W) : SimpleGraph H.edges :=
  SimpleGraph.fromRel (fun e f => (e.1 ∩ f.1).Nonempty)

/-
Two host edges are adjacent in the intersection graph exactly when they
are distinct and have a common vertex.
-/
theorem edgeIntersectionGraph_adj_iff (H : Hypergraph W) (e f : H.edges) :
    (edgeIntersectionGraph H).Adj e f ↔ e ≠ f ∧ (e.1 ∩ f.1).Nonempty := by
  constructor;
  · intro h;
    cases h.2 <;> simp_all +decide [ edgeIntersectionGraph ];
    rwa [ Set.inter_comm ];
  · simp +contextual [ edgeIntersectionGraph ]

/-- Data for a chordless seven-cycle in the edge-intersection graph. -/
structure InducedEdgeIntersectionSevenCycle (H : Hypergraph W) where
  edge : Fin 7 → H.edges
  injective : Function.Injective edge
  consecutive : ∀ i, (edgeIntersectionGraph H).Adj (edge i) (edge (i + 1))
  induced : ∀ i j, (edgeIntersectionGraph H).Adj (edge i) (edge j) →
    j = i + 1 ∨ i = j + 1

/-- Choose the common vertex at each join of an induced edge cycle. -/
noncomputable def InducedEdgeIntersectionSevenCycle.core
    {H : Hypergraph W} (c : InducedEdgeIntersectionSevenCycle H) (i : Fin 7) : W :=
  Classical.choose ((edgeIntersectionGraph_adj_iff H (c.edge (i - 1)) (c.edge i)).mp
    (by simpa using! c.consecutive (i - 1))).2

/-
The chosen join vertex belongs to the edge on its right.
-/
theorem InducedEdgeIntersectionSevenCycle.core_mem_right
    {H : Hypergraph W} (c : InducedEdgeIntersectionSevenCycle H) (i : Fin 7) :
    c.core i ∈ (c.edge i).1 := by
  exact Classical.choose_spec ( _ : ∃ x, x ∈ ( c.edge ( i - 1 ) ).1 ∩ ( c.edge i ).1 ) |>.2

/-
The chosen join vertex belongs to the edge on its left.
-/
theorem InducedEdgeIntersectionSevenCycle.core_mem_left
    {H : Hypergraph W} (c : InducedEdgeIntersectionSevenCycle H) (i : Fin 7) :
    c.core (i + 1) ∈ (c.edge i).1 := by
  convert! Classical.choose_spec ( ( edgeIntersectionGraph_adj_iff H ( c.edge i ) ( c.edge ( i + 1 ) ) ).mp ( by simpa using! c.consecutive i ) |>.2 ) |>.1 using 1;
  fin_cases i <;> rfl

/-
In an induced cycle of length seven, the seven chosen intersection
vertices are distinct.  Linearity rules out two different edge pairs sharing
two points, while inducedness rules out a point lying on nonconsecutive cycle
edges.
-/
set_option maxHeartbeats 800000 in
theorem InducedEdgeIntersectionSevenCycle.core_injective
    (H : Hypergraph W)
    (c : InducedEdgeIntersectionSevenCycle H) :
    Function.Injective c.core := by
  intro i j hij
  by_contra h_neq;
  -- By the properties of the core vertices and the induced cycle, we have that $c.core i \in (c.edge (i - 1)).1$ and $c.core i \in (c.edge i).1$.
  have h_core_i : c.core i ∈ (c.edge (i - 1)).1 ∧ c.core i ∈ (c.edge i).1 := by
    exact ⟨ Classical.choose_spec ( ( edgeIntersectionGraph_adj_iff H ( c.edge ( i - 1 ) ) ( c.edge i ) ).mp ( by simpa using! c.consecutive ( i - 1 ) ) |>.2 ) |>.1, c.core_mem_right i ⟩
  have h_core_j : c.core j ∈ (c.edge (j - 1)).1 ∧ c.core j ∈ (c.edge j).1 := by
    exact ⟨ by simpa using! c.core_mem_left ( j - 1 ), by simpa using! c.core_mem_right j ⟩;
  have := c.induced ( i - 1 ) j; simp_all +decide [ Fin.ext_iff ] ;
  have := c.induced i ( j - 1 ) ; simp_all +decide [ edgeIntersectionGraph ] ;
  by_cases hi : c.edge ( i - 1 ) = c.edge j <;> by_cases hj : c.edge i = c.edge ( j - 1 ) <;> simp_all +decide [ Set.Nonempty ];
  · have := c.injective hi; have := c.injective hj; fin_cases i <;> fin_cases j <;> trivial;
  · fin_cases i <;> fin_cases j <;> simp +decide at h_neq this ⊢;
    all_goals have := c.injective hi; simp_all +decide ;
  · have := c.injective hj; simp_all +decide [ Fin.ext_iff ] ;
    fin_cases j <;> simp_all +decide;
  · fin_cases i <;> fin_cases j <;> simp +decide at h_neq hi hj this ⊢;
    all_goals simp_all +decide

/-
A cycle edge contains no chosen core vertex except its two cyclic
endpoints.
-/
theorem InducedEdgeIntersectionSevenCycle.core_mem_iff
    (H : Hypergraph W)
    (c : InducedEdgeIntersectionSevenCycle H) (i j : Fin 7) :
    c.core j ∈ (c.edge i).1 ↔ j = i ∨ j = i + 1 := by
  constructor;
  · intro hj
    by_cases h_eq : j = i ∨ j = i + 1;
    · exact h_eq;
    · have h_adj : (edgeIntersectionGraph H).Adj (c.edge i) (c.edge j) := by
        have h_adj : (c.edge i).1 ∩ (c.edge j).1 ≠ ∅ := by
          exact Set.Nonempty.ne_empty ⟨ c.core j, hj, c.core_mem_right j ⟩;
        simp_all +decide [ Set.ext_iff, edgeIntersectionGraph ];
        exact ⟨ by intro h; have := c.injective h; aesop, Or.inl ⟨ _, h_adj.choose_spec.1, h_adj.choose_spec.2 ⟩ ⟩;
      have := c.induced i j h_adj; simp_all +decide [ Fin.ext_iff ] ;
      have h_adj : (edgeIntersectionGraph H).Adj (c.edge i) (c.edge (j - 1)) := by
        have h_adj : c.core j ∈ (c.edge i).1 ∧ c.core j ∈ (c.edge (j - 1)).1 := by
          exact ⟨ hj, by simpa using! c.core_mem_left ( j - 1 ) ⟩;
        exact ⟨ by
          intro h; have := c.injective h; fin_cases i <;> fin_cases j <;> trivial;, by
          exact Or.inl ⟨ c.core j, h_adj.1, h_adj.2 ⟩ ⟩;
      fin_cases i <;> fin_cases j <;> simp +decide at this h_adj ⊢;
      all_goals have := c.induced _ _ h_adj; simp_all +decide;
  · rintro ( rfl | rfl ) <;> simp +decide [ InducedEdgeIntersectionSevenCycle.core_mem_right, InducedEdgeIntersectionSevenCycle.core_mem_left ]

/-
Two distinct edges of an induced edge-intersection cycle can meet only in
one of the seven chosen core vertices.
-/
theorem InducedEdgeIntersectionSevenCycle.inter_subset_core
    (H : Hypergraph W) (hlin : H.Linear)
    (c : InducedEdgeIntersectionSevenCycle H)
    {i j : Fin 7} (hij : i ≠ j) :
    (c.edge i).1 ∩ (c.edge j).1 ⊆ Set.range c.core := by
  intro x hx; by_cases h_cases : j = i + 1 ∨ i = j + 1 <;> simp_all +decide;
  · cases' h_cases with h_cases h_cases;
    · use i + 1;
      apply hlin;
      exact c.edge i |>.2;
      exact c.edge ( i + 1 ) |>.2;
      · exact fun h => by have := c.injective ( Subtype.ext h ) ; fin_cases i <;> trivial;
      · exact ⟨ c.core_mem_left i, c.core_mem_right ( i + 1 ) ⟩;
      · aesop;
    · have h_core_eq : x = c.core (j + 1) := by
        apply hlin;
        exact c.edge i |>.2;
        exact c.edge j |>.2;
        · exact fun h => hij <| c.injective <| Subtype.ext h;
        · exact ⟨ hx.1, hx.2 ⟩;
        · simp +decide [ *, InducedEdgeIntersectionSevenCycle.core_mem_left, InducedEdgeIntersectionSevenCycle.core_mem_right ];
      exact ⟨ _, h_core_eq.symm ⟩;
  · have := c.induced i j; simp_all +decide [ edgeIntersectionGraph ] ;
    exact False.elim ( this ( by intro h; have := c.injective h; fin_cases i <;> fin_cases j <;> trivial ) |>.1 ⟨ x, hx ⟩ )

/-- An induced seven-cycle in the edge-intersection graph determines a clean
seven-edge loose cycle. -/
noncomputable def InducedEdgeIntersectionSevenCycle.toClean
    (H : Hypergraph W) (hlin : H.Linear)
    (c : InducedEdgeIntersectionSevenCycle H) : CleanLoose7EdgeCycle H where
  core := c.core
  edge := fun i => (c.edge i).1
  core_injective := c.core_injective H
  edge_mem := fun i => (c.edge i).2
  left_mem := c.core_mem_right
  right_mem := c.core_mem_left
  core_mem_iff := c.core_mem_iff H
  inter_subset_core := fun {i j} hij =>
    InducedEdgeIntersectionSevenCycle.inter_subset_core H hlin c (i := i) (j := j) hij

/-- A clean loose seven-edge cycle gives a chordless cycle in the host's
edge-intersection graph.  Thus the two finite endpoints are equivalent in a
linear host. -/
noncomputable def CleanLoose7EdgeCycle.toInduced
    (H : Hypergraph W) (c : CleanLoose7EdgeCycle H) :
    InducedEdgeIntersectionSevenCycle H where
  edge := fun i => ⟨c.edge i, c.edge_mem i⟩
  injective := fun i j h => cleanEdgeCycle_edge_injective H c (Subtype.ext_iff.mp h)
  consecutive := by
    intro i
    rw [edgeIntersectionGraph_adj_iff]
    refine ⟨?_, ⟨c.core (i + 1), c.right_mem i, c.left_mem (i + 1)⟩⟩
    intro h
    have hi : i = i + 1 :=
      cleanEdgeCycle_edge_injective H c (Subtype.ext_iff.mp h)
    have hne : i ≠ i + 1 := by
      fin_cases i <;> decide
    exact hne hi
  induced := by
    intro i j hij
    rw [edgeIntersectionGraph_adj_iff] at hij
    obtain ⟨x, hxi, hxj⟩ := hij.2
    obtain ⟨k, rfl⟩ := c.inter_subset_core
      (fun h => hij.1 (congrArg (fun k => (⟨c.edge k, c.edge_mem k⟩ : H.edges)) h))
      ⟨hxi, hxj⟩
    have hi := (c.core_mem_iff i k).mp hxi
    have hj := (c.core_mem_iff j k).mp hxj
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- Existence of a clean loose seven-edge cycle is equivalent to existence of
an induced seven-cycle in the edge-intersection graph of a linear host. -/
theorem nonempty_cleanLoose7_iff_inducedEdgeIntersectionSeven
    (H : Hypergraph W) (hlin : H.Linear) :
    Nonempty (CleanLoose7EdgeCycle H) ↔
      Nonempty (InducedEdgeIntersectionSevenCycle H) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.toInduced H⟩
  · rintro ⟨c⟩
    exact ⟨c.toClean H hlin⟩

/-- **Finite intersection-graph endpoint for E5.**  Every induced seven-cycle
in the edge-intersection graph of a linear triple system is a copy of the loose
triple-system seven-cycle. -/
theorem looseCycle7_embeds_of_induced_edgeIntersection_cycle
    (H : Hypergraph W) (htri : H.IsTripleSystem) (hlin : H.Linear)
    (c : InducedEdgeIntersectionSevenCycle H) :
    looseCycle7.Embeds H := by
  exact looseCycle7_embeds_of_cleanEdgeCycle H htri ( c.toClean H hlin )

/-
It is enough for the infinitary Hajnal--Komjáth argument to produce an
induced seven-cycle in the edge-intersection graph.
-/
theorem e5_HK_loose7_of_induced_edgeIntersection_cycle
    (hcycle : ∀ {W : Type u} (H : Hypergraph W), H.IsTripleSystem → H.Linear →
      H.UncountablyChromatic → Nonempty (InducedEdgeIntersectionSevenCycle H)) :
    E5_HK_loose7.{u} := by
  intro W H htri hlin huc;
  exact looseCycle7_embeds_of_induced_edgeIntersection_cycle H htri hlin ( Classical.choice ( hcycle H htri hlin huc ) )

end Erdos1177
