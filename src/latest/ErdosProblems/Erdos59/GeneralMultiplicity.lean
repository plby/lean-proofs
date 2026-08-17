import ErdosProblems.Erdos59.QuadrilateralComponents

/-!
# The Füredi--Naor--Verstraëte general multiplicity estimate

This file isolates the finite counting part of Lemma 8.1 of Füredi--Naor--Verstraëte.
Length-three paths are stored with their smaller endpoint first, so every unoriented path is
counted exactly once.  The central (degenerate) contribution is charged to closed
neighbourhoods and costs `25 * Δ * e`; the remaining pairs are charged to the
quadrilateral components and cost `10 * Δ * e`.

The lengthy local classification of quadrilateral components is represented by the concrete
certificate `GeneralMultiplicityCertificate`.  Its fields are precisely the three estimates
used in the published proof: the Erdos--Gallai open-neighbourhood estimate, the count by pairs
of disjoint edges in a closed neighbourhood, and the ten-piece component charge.  No
asymptotic or infinitary assertion occurs here.
-/

open scoped BigOperators
open Finset

namespace Erdos59

noncomputable section

universe u

variable {V : Type u} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

attribute [local instance] Classical.propDecidable

/-- An unordered pair, represented by putting its smaller vertex first. -/
abbrev EndpointPair (V : Type u) [LinearOrder V] := {q : V × V // q.1 < q.2}

/-- A four-tuple is a three-edge simple path when consecutive vertices are adjacent and all
four vertices are different. -/
def IsPath3 (p : Fin 4 → V) : Prop :=
  Function.Injective p ∧
    G.Adj (p 0) (p 1) ∧ G.Adj (p 1) (p 2) ∧ G.Adj (p 2) (p 3)

/-- Unoriented paths of length three.  The endpoint order chooses one of the two orientations. -/
def Path3 := {p : Fin 4 → V // IsPath3 G p ∧ p 0 < p 3}

noncomputable instance : Fintype (Path3 G) :=
  Fintype.subtype
    (Finset.univ.filter fun p : Fin 4 → V ↦ IsPath3 G p ∧ p 0 < p 3)
    (fun _ ↦ by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
instance : DecidableEq (Path3 G) := inferInstance

namespace Path3

/-- The vertex at position `i` of a length-three path. -/
def vertex {G : SimpleGraph V} (p : Path3 G) (i : Fin 4) : V := p.1 i

@[simp] theorem vertex_mk {G : SimpleGraph V} (p : Fin 4 → V) (hp) (i : Fin 4) :
    (show Path3 G from ⟨p, hp⟩).vertex i = p i := rfl

/-- The (canonically ordered) endpoint pair of a path. -/
def endpoints {G : SimpleGraph V} (p : Path3 G) : EndpointPair V :=
  ⟨(p.vertex 0, p.vertex 3), p.2.2⟩

@[simp] theorem endpoints_fst {G : SimpleGraph V} (p : Path3 G) :
    p.endpoints.1.1 = p.vertex 0 := rfl
@[simp] theorem endpoints_snd {G : SimpleGraph V} (p : Path3 G) :
    p.endpoints.1.2 = p.vertex 3 := rfl

theorem injective {G : SimpleGraph V} (p : Path3 G) : Function.Injective p.vertex := p.2.1.1

theorem adj_zero_one {G : SimpleGraph V} (p : Path3 G) :
    G.Adj (p.vertex 0) (p.vertex 1) := p.2.1.2.1
theorem adj_one_two {G : SimpleGraph V} (p : Path3 G) :
    G.Adj (p.vertex 1) (p.vertex 2) := p.2.1.2.2.1
theorem adj_two_three {G : SimpleGraph V} (p : Path3 G) :
    G.Adj (p.vertex 2) (p.vertex 3) := p.2.1.2.2.2

end Path3

/-- All length-three paths with endpoint pair `pi`. -/
def pathFiber (pi : EndpointPair V) : Finset (Path3 G) :=
  Finset.univ.filter fun p ↦ p.endpoints = pi

@[simp] theorem mem_pathFiber {pi : EndpointPair V} {p : Path3 G} :
    p ∈ pathFiber G pi ↔ p.endpoints = pi := by
  simp [pathFiber]

/-- The FNV multiplicity `|pi|`. -/
def pathMultiplicity (pi : EndpointPair V) : ℕ := (pathFiber G pi).card

/-- The closed neighbourhood of a vertex. -/
def closedNeighborFinset (v : V) : Finset V := insert v (G.neighborFinset v)

@[simp] theorem mem_closedNeighborFinset {v w : V} :
    w ∈ closedNeighborFinset G v ↔ w = v ∨ G.Adj v w := by
  simp [closedNeighborFinset]

/-- Paths lying wholly in the closed neighbourhood of `v`. -/
def closedNeighborhoodPaths (v : V) : Finset (Path3 G) :=
  Finset.univ.filter fun p ↦ ∀ i, p.vertex i ∈ closedNeighborFinset G v

@[simp] theorem mem_closedNeighborhoodPaths {v : V} {p : Path3 G} :
    p ∈ closedNeighborhoodPaths G v ↔
      ∀ i, p.vertex i ∈ closedNeighborFinset G v := by
  simp [closedNeighborhoodPaths]

/-- Edges having both endpoints in the open neighbourhood of `v`. -/
def openNeighborhoodEdges (v : V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ ∀ w ∈ e, w ∈ G.neighborFinset v

/-- The number of edges in the closed neighbourhood, split into the `degree v` star edges
and the edges internal to the open neighbourhood. -/
def closedNeighborhoodEdgeCount (v : V) : ℕ :=
  G.degree v + (openNeighborhoodEdges G v).card

/-- A path fibre is central when all its paths lie in one closed neighbourhood.  This is the
spanning-star characterization in FNV Lemma 5.2. -/
def IsCentralPair (pi : EndpointPair V) : Prop :=
  ∃ v, ∀ p ∈ pathFiber G pi, ∀ i, p.vertex i ∈ closedNeighborFinset G v

/-- FNV degeneracy, using the equivalent central-union characterization of Lemma 5.2. -/
def IsDegeneratePair (pi : EndpointPair V) : Prop := IsCentralPair G pi

theorem isDegeneratePair_iff_isCentralPair (pi : EndpointPair V) :
    IsDegeneratePair G pi ↔ IsCentralPair G pi := Iff.rfl

/-- Pairs used in FNV Lemma 6.1: adjacent pairs of multiplicity at least two, and all pairs
of multiplicity at least three. -/
def ordinaryExceptionalPairs : Finset (EndpointPair V) :=
  Finset.univ.filter fun pi ↦
    (2 ≤ pathMultiplicity G pi ∧
      G.Adj pi.1.1 pi.1.2) ∨ 3 ≤ pathMultiplicity G pi

/-- Degenerate pairs having at least two paths. -/
def degeneratePairs : Finset (EndpointPair V) :=
  Finset.univ.filter fun pi ↦ 2 ≤ pathMultiplicity G pi ∧ IsDegeneratePair G pi

/-- The concrete set `Pi ∪ Pi*` from FNV Lemma 8.1. -/
def generalExceptionalPairs : Finset (EndpointPair V) :=
  ordinaryExceptionalPairs G ∪ degeneratePairs G

/-- The part of `Pi` not already charged as degenerate. -/
def nondegenerateExceptionalPairs : Finset (EndpointPair V) :=
  ordinaryExceptionalPairs G \ degeneratePairs G

/-- Sum of the endpoint-pair multiplicities over a finite family. -/
def multiplicitySum (pairs : Finset (EndpointPair V)) : ℕ :=
  ∑ pi ∈ pairs, pathMultiplicity G pi

theorem generalExceptionalPairs_eq :
    generalExceptionalPairs G =
      degeneratePairs G ∪ nondegenerateExceptionalPairs G := by
  ext pi
  simp only [generalExceptionalPairs, nondegenerateExceptionalPairs, mem_union, mem_sdiff]
  tauto

theorem degenerate_disjoint_nondegenerate :
    Disjoint (degeneratePairs G) (nondegenerateExceptionalPairs G) := by
  unfold nondegenerateExceptionalPairs
  exact Finset.disjoint_sdiff

/-- The actual edge sets of the exceptional quadrilateral components. -/
abbrev ComponentEdgeSet (V : Type u) := Finset (Sym2 V)

/-- A component charge records the at-most-ten maximal-complete-bipartite-piece part of the
FNV quadrilateral-component classification.  The edge sets remain concrete edge sets of `G`.
-/
structure ExceptionalComponentCharge where
  components : Finset (ComponentEdgeSet V)
  componentOf : EndpointPair V → ComponentEdgeSet V
  component_mem : ∀ pi ∈ nondegenerateExceptionalPairs G,
    componentOf pi ∈ components
  edge_subset : ∀ C ∈ components, C ⊆ G.edgeFinset
  pieces : ComponentEdgeSet V → Finset (ComponentEdgeSet V)
  pieces_le_ten : ∀ C ∈ components, (pieces C).card ≤ 10
  local_charge : ∀ C ∈ components,
    ∑ pi ∈ (nondegenerateExceptionalPairs G).filter (componentOf · = C),
        pathMultiplicity G pi ≤ 10 * G.maxDegree * C.card
  edge_budget : ∑ C ∈ components, C.card ≤ G.edgeFinset.card

/-- The precise finite hypotheses consumed by the counting part of FNV Lemma 8.1. -/
structure GeneralMultiplicityCertificate where
  /-- Lemma 5.2, including a consistent choice of a centre for every degenerate pair. -/
  center : EndpointPair V → V
  center_spec : ∀ pi ∈ degeneratePairs G, ∀ p ∈ pathFiber G pi, ∀ i,
    p.vertex i ∈ closedNeighborFinset G (center pi)
  /-- Disjoint endpoint fibres charged to their chosen central closed neighbourhoods. -/
  central_charge :
    multiplicitySum G (degeneratePairs G) ≤
      ∑ v, (closedNeighborhoodPaths G v).card
  /-- Choosing two disjoint end edges of a path gives the factor `2 e[v]^2`. -/
  closed_path_pair_count : ∀ v,
    (closedNeighborhoodPaths G v).card ≤ 2 * (closedNeighborhoodEdgeCount G v) ^ 2
  /-- Erdos--Gallai on the `P_5`-free graph induced by the open neighbourhood. -/
  erdos_gallai_neighborhood : ∀ v,
    2 * (openNeighborhoodEdges G v).card ≤ 3 * G.degree v
  /-- The exceptional-component classification and its at-most-ten-piece charge. -/
  exceptionalComponents : ExceptionalComponentCharge G

/-- Erdos--Gallai's open-neighbourhood estimate gives the closed-neighbourhood edge bound
`2 e[v] ≤ 5 d(v)`. -/
theorem closedNeighborhoodEdgeCount_le_five_halves
    (cert : GeneralMultiplicityCertificate G) (v : V) :
    2 * closedNeighborhoodEdgeCount G v ≤ 5 * G.degree v := by
  dsimp [closedNeighborhoodEdgeCount]
  have h := cert.erdos_gallai_neighborhood v
  omega

/-- The central path count at one vertex, in the doubled form which avoids division by two. -/
theorem twice_closedNeighborhoodPaths_le
    (cert : GeneralMultiplicityCertificate G) (v : V) :
    2 * (closedNeighborhoodPaths G v).card ≤
      25 * G.maxDegree * G.degree v := by
  let c := closedNeighborhoodEdgeCount G v
  let p := (closedNeighborhoodPaths G v).card
  have hp : p ≤ 2 * c ^ 2 := cert.closed_path_pair_count v
  have hc : 2 * c ≤ 5 * G.degree v :=
    closedNeighborhoodEdgeCount_le_five_halves G cert v
  have hd : G.degree v ≤ G.maxDegree := G.degree_le_maxDegree v
  calc
    2 * p ≤ 2 * (2 * c ^ 2) := Nat.mul_le_mul_left 2 hp
    _ = (2 * c) ^ 2 := by ring
    _ ≤ (5 * G.degree v) ^ 2 := Nat.pow_le_pow_left hc 2
    _ = 25 * G.degree v * G.degree v := by ring
    _ ≤ 25 * G.maxDegree * G.degree v := by
      exact Nat.mul_le_mul_right (G.degree v) (Nat.mul_le_mul_left 25 hd)

/-- The total contribution of all central/degenerate pairs is at most `25 Δ e`. -/
theorem degenerate_multiplicity_bound
    (cert : GeneralMultiplicityCertificate G) :
    multiplicitySum G (degeneratePairs G) ≤
      25 * G.maxDegree * G.edgeFinset.card := by
  have hlocal :
      2 * (∑ v, (closedNeighborhoodPaths G v).card) ≤
        ∑ v, 25 * G.maxDegree * G.degree v := by
    simpa only [Finset.mul_sum] using
      Finset.sum_le_sum (fun v _ ↦ twice_closedNeighborhoodPaths_le G cert v)
  have hdegree : ∑ v, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  have hcentral := Nat.mul_le_mul_left 2 cert.central_charge
  have htwo :
      2 * multiplicitySum G (degeneratePairs G) ≤
        2 * (25 * G.maxDegree * G.edgeFinset.card) := by
    calc
      2 * multiplicitySum G (degeneratePairs G)
          ≤ 2 * (∑ v, (closedNeighborhoodPaths G v).card) := hcentral
      _ ≤ ∑ v, 25 * G.maxDegree * G.degree v := hlocal
      _ = 2 * (25 * G.maxDegree * G.edgeFinset.card) := by
        rw [← Finset.mul_sum, hdegree]
        ring
  exact Nat.le_of_mul_le_mul_left htwo Nat.two_pos

/-- Summing the local ten-piece charges over the edge-disjoint exceptional components gives
the `10 Δ e` half of FNV Lemma 8.1. -/
theorem nondegenerate_multiplicity_bound
    (cert : GeneralMultiplicityCertificate G) :
    multiplicitySum G (nondegenerateExceptionalPairs G) ≤
      10 * G.maxDegree * G.edgeFinset.card := by
  let ec : ExceptionalComponentCharge G := cert.exceptionalComponents
  have hmaps : ∀ pi ∈ nondegenerateExceptionalPairs G,
      ec.componentOf pi ∈ ec.components := ec.component_mem
  have hpartition :
      multiplicitySum G (nondegenerateExceptionalPairs G) =
        ∑ C ∈ ec.components,
          ∑ pi ∈ (nondegenerateExceptionalPairs G).filter (ec.componentOf · = C),
            pathMultiplicity G pi := by
    unfold multiplicitySum
    exact (Finset.sum_fiberwise_of_maps_to hmaps (pathMultiplicity G)).symm
  calc
    multiplicitySum G (nondegenerateExceptionalPairs G) =
        ∑ C ∈ ec.components,
          ∑ pi ∈ (nondegenerateExceptionalPairs G).filter (ec.componentOf · = C),
            pathMultiplicity G pi := hpartition
    _ ≤ ∑ C ∈ ec.components, 10 * G.maxDegree * C.card := by
      exact Finset.sum_le_sum fun C hC ↦ ec.local_charge C hC
    _ = 10 * G.maxDegree * (∑ C ∈ ec.components, C.card) := by
      rw [Finset.mul_sum]
    _ ≤ 10 * G.maxDegree * G.edgeFinset.card := by
      exact Nat.mul_le_mul_left (10 * G.maxDegree) ec.edge_budget

/-- FNV Lemma 8.1, at the exact finite accounting boundary.  All endpoint pairs in `Pi ∪ Pi*`
are included, including the central/degenerate pairs. -/
theorem general_multiplicity_bound
    (_hC6 : WalkC6Free G) (cert : GeneralMultiplicityCertificate G) :
    ∑ pi ∈ generalExceptionalPairs G, pathMultiplicity G pi ≤
      35 * G.maxDegree * G.edgeFinset.card := by
  rw [generalExceptionalPairs_eq G]
  rw [Finset.sum_union (degenerate_disjoint_nondegenerate G)]
  have hd := degenerate_multiplicity_bound G cert
  have hn := nondegenerate_multiplicity_bound G cert
  dsimp [multiplicitySum] at hd hn
  calc
    (∑ pi ∈ degeneratePairs G, pathMultiplicity G pi) +
          ∑ pi ∈ nondegenerateExceptionalPairs G, pathMultiplicity G pi
        ≤ 25 * G.maxDegree * G.edgeFinset.card +
          10 * G.maxDegree * G.edgeFinset.card := Nat.add_le_add hd hn
    _ = 35 * G.maxDegree * G.edgeFinset.card := by ring

end

end Erdos59
