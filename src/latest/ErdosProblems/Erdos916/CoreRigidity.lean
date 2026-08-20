/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.Core

/-!
# The `(2,3)`-circuit route to Erdős Problem 916

This file records the elementary part of the rigidity-matroid approach.  A graph with
`2 * |V| - 2` edges and minimum degree three has at least four vertices of degree exactly
three.  Deleting any one of those vertices leaves the tight edge count
`2 * (|V| - 1) - 3`, which is the numerical starting point of inverse Henneberg induction.

No Laman- or Henneberg-matroid library currently exists in Mathlib, so the genuinely
structural admissible-node theorem is deliberately not hidden in these definitions.  The
last theorem gives the exact elementary bridge needed after such a theorem supplies a rim
cycle through the neighbours of a degree-three node.
-/

namespace Erdos916

open SimpleGraph

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The global edge-count equation of a `(2,3)`-circuit.  The additive form avoids
truncated subtraction on small vertex sets. -/
def Has23CircuitCount (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.edgeFinset.card + 2 = 2 * Fintype.card V

/-- The circuit count is equivalently expressed using the instance-independent cardinality
of the edge set. -/
theorem has23CircuitCount_iff_ncard
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Has23CircuitCount G ↔
      G.edgeSet.ncard + 2 = 2 * Fintype.card V := by
  rw [Has23CircuitCount, Set.ncard_eq_toFinset_card']
  rfl

/-- `(2,3)`-sparsity, stated only for vertex sets of size at least two (the conventional
domain of the inequality). -/
def Is23Sparse (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset V, 2 ≤ S.card →
    (G.induce (S : Set V)).edgeFinset.card + 3 ≤ 2 * S.card

/-- A Laman-tight graph: every induced vertex set is `(2,3)`-sparse and the whole graph
has exactly `2 * |V| - 3` edges. -/
def Is23Tight (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Is23Sparse G ∧ G.edgeFinset.card + 3 = 2 * Fintype.card V

/-- The vertex-set formulation of a `(2,3)`-circuit.  Its whole edge set violates
`(2,3)`-sparsity by one edge, while every proper induced vertex set is sparse. -/
def Is23Circuit (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Has23CircuitCount G ∧
    ∀ S : Finset V, 2 ≤ S.card → S ≠ Finset.univ →
      (G.induce (S : Set V)).edgeFinset.card + 3 ≤ 2 * S.card

namespace Is23Circuit

/-- Every vertex of a genuine (at least four vertex) `(2,3)`-circuit has degree at least
three.  Remove the vertex and apply sparsity to the resulting proper vertex set. -/
theorem degree_three_le (hcircuit : Is23Circuit G)
    (hcard : 4 ≤ Fintype.card V) (v : V) :
    3 ≤ G.degree v := by
  classical
  let S : Finset V := Finset.univ.erase v
  have hScard : S.card = Fintype.card V - 1 := by
    simp [S]
  have hS2 : 2 ≤ S.card := by omega
  have hSne : S ≠ Finset.univ := by
    intro h
    have hvS : v ∈ S := by rw [h]; simp
    simp [S] at hvS
  have hsparse := hcircuit.2 S hS2 hSne
  have hedgeInd := G.card_edgeFinset_induce_compl_singleton v
  have hedgeDel := G.card_edgeFinset_deleteIncidenceSet v
  have hSset : (S : Set V) = ({v}ᶜ : Set V) := by
    ext w
    simp [S]
  have hedge :
      (G.induce (S : Set V)).edgeFinset.card =
        G.edgeFinset.card - G.degree v := by
    let e : G.induce (S : Set V) ≃g G.induce ({v}ᶜ : Set V) := by
      refine { toEquiv := Equiv.setCongr hSset, map_rel_iff' := ?_ }
      intro a b
      rfl
    exact e.card_edgeFinset_eq.trans (hedgeInd.trans hedgeDel)
  have hdegreeEdge : G.degree v ≤ G.edgeFinset.card :=
    G.degree_le_card_edgeFinset v
  have hcount := hcircuit.1
  dsimp [Has23CircuitCount] at hcount
  rw [hedge, hScard] at hsparse
  omega

end Is23Circuit

/-- In a graph with circuit edge count and minimum degree three, at least four vertices
have degree exactly three.  This is the handshaking argument behind the first inverse
Henneberg move. -/
theorem four_le_card_degree_eq_three
    (hcount : Has23CircuitCount G)
    (hmin : ∀ v : V, 3 ≤ G.degree v) :
    4 ≤ (Finset.univ.filter fun v : V => G.degree v = 3).card := by
  classical
  let D : Finset V := Finset.univ.filter fun v : V => G.degree v = 3
  have hpoint (v : V) :
      4 ≤ G.degree v + if G.degree v = 3 then 1 else 0 := by
    by_cases hv : G.degree v = 3
    · simp [hv]
    · simp only [hv, if_false, add_zero]
      have := hmin v
      omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset V))
    (fun v _ => hpoint v)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [Finset.sum_add_distrib, G.sum_degrees_eq_twice_card_edges] at hsum
  have hindicator :
      (∑ v : V, if G.degree v = 3 then 1 else 0) = D.card := by
    simp [D]
  rw [hindicator] at hsum
  dsimp [Has23CircuitCount] at hcount
  have hdouble : 2 * G.edgeFinset.card + 4 = 4 * Fintype.card V := by
    omega
  have hsum' : 4 * Fintype.card V ≤ 2 * G.edgeFinset.card + D.card := by
    simpa [Nat.mul_comm] using hsum
  change 4 ≤ D.card
  omega

namespace Is23Circuit

/-- A `(2,3)`-circuit on at least four vertices therefore has at least four
degree-three nodes. -/
theorem four_le_card_degree_eq_three (hcircuit : Is23Circuit G)
    (hcard : 4 ≤ Fintype.card V) :
    4 ≤ (Finset.univ.filter fun v : V => G.degree v = 3).card :=
  Erdos916.four_le_card_degree_eq_three hcircuit.1
    (fun v => hcircuit.degree_three_le hcard v)

end Is23Circuit

/-- In particular, a minimum-degree-three graph with circuit count has a degree-three
vertex. -/
theorem exists_degree_eq_three
    (hcount : Has23CircuitCount G)
    (hmin : ∀ v : V, 3 ≤ G.degree v) :
    ∃ v : V, G.degree v = 3 := by
  classical
  have hfour := four_le_card_degree_eq_three (G := G) hcount hmin
  have hne : (Finset.univ.filter fun v : V => G.degree v = 3).Nonempty :=
    Finset.nonempty_of_ne_empty (by
      intro hempty
      rw [hempty] at hfour
      simp at hfour)
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, by simpa using hv⟩

/-- Deleting a degree-three vertex from a graph with `(2,3)`-circuit count leaves exactly
the Laman-tight edge count. -/
theorem delete_degree_three_has_tight_count
    (hcount : Has23CircuitCount G) {v : V} (hv : G.degree v = 3) :
    (G.induce ({v}ᶜ : Set V)).edgeFinset.card + 3 =
      2 * Fintype.card {w : V // w ∈ ({v}ᶜ : Set V)} := by
  classical
  have hedgeInd := G.card_edgeFinset_induce_compl_singleton v
  have hedgeDel := G.card_edgeFinset_deleteIncidenceSet v
  have hedge :
      (G.induce ({v}ᶜ : Set V)).edgeFinset.card = G.edgeFinset.card - 3 := by
    rw [hedgeInd, hedgeDel, hv]
  have hcard : Fintype.card {w : V // w ∈ ({v}ᶜ : Set V)} =
      Fintype.card V - 1 := by
    change Fintype.card {w : V // w ≠ v} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl (fun w : V => w = v)]
    simp
  have hn : 4 ≤ Fintype.card V := by
    have hlt := G.degree_lt_card_verts v
    omega
  dsimp [Has23CircuitCount] at hcount
  rw [hedge, hcard]
  omega

/-- Every induced vertex set of the deletion is a proper induced vertex set of the
original graph.  Consequently, deleting a degree-three node of a `(2,3)`-circuit gives
a Laman-tight graph. -/
theorem is23Tight_delete_degree_three
    (hcircuit : Is23Circuit G) {v : V} (hv : G.degree v = 3) :
    Is23Tight (G.induce ({v}ᶜ : Set V)) := by
  classical
  constructor
  · intro S hS
    let inc : {w : V // w ∈ ({v}ᶜ : Set V)} ↪ V :=
      Function.Embedding.subtype _
    let T : Finset V := S.map inc
    have hcardT : T.card = S.card := by simp [T]
    have hvT : v ∉ T := by
      intro hmem
      simp only [T, Finset.mem_map] at hmem
      obtain ⟨w, -, hwv⟩ := hmem
      have hwne : w.1 ≠ v := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using w.2
      exact hwne (by simpa [inc] using hwv)
    have hTproper : T ≠ Finset.univ := by
      intro hTu
      have : v ∈ T := by rw [hTu]; simp
      exact hvT this
    have hsparse := hcircuit.2 T (by omega) hTproper
    have hsets :
        ((fun w : {w : V // w ∈ ({v}ᶜ : Set V)} => (w : V)) ''
            (S : Set {w : V // w ∈ ({v}ᶜ : Set V)})) = (T : Set V) := by
      ext x
      simp [T, inc]
    let e₀ :
        {w : {w : V // w ∈ ({v}ᶜ : Set V)} // w ∈
          (S : Set {w : V // w ∈ ({v}ᶜ : Set V)})} ≃
        {x : V // x ∈ ((fun w : {w : V // w ∈ ({v}ᶜ : Set V)} => (w : V)) ''
          (S : Set {w : V // w ∈ ({v}ᶜ : Set V)}))} :=
      Equiv.Set.image (fun w : {w : V // w ∈ ({v}ᶜ : Set V)} => (w : V))
        (S : Set {w : V // w ∈ ({v}ᶜ : Set V)}) Subtype.val_injective
    let e :
        {w : {w : V // w ∈ ({v}ᶜ : Set V)} // w ∈
          (S : Set {w : V // w ∈ ({v}ᶜ : Set V)})} ≃
        {x : V // x ∈ (T : Set V)} :=
      e₀.trans (Equiv.setCongr hsets)
    let gi :
        (G.induce ({v}ᶜ : Set V)).induce
            (S : Set {w : V // w ∈ ({v}ᶜ : Set V)}) ≃g
          G.induce (T : Set V) := by
      refine { toEquiv := e, map_rel_iff' := ?_ }
      intro x y
      simp only [SimpleGraph.induce_adj]
      rfl
    have hinduce :
        ((G.induce ({v}ᶜ : Set V)).induce
          (S : Set {w : V // w ∈ ({v}ᶜ : Set V)})).edgeFinset.card =
        (G.induce (T : Set V)).edgeFinset.card :=
      gi.card_edgeFinset_eq
    rw [hinduce]
    simpa only [hcardT] using hsparse
  · exact delete_degree_three_has_tight_count hcircuit.1 hv

/-- A rim cycle for `v`: it avoids `v` and contains every neighbour of `v`.  This is the
precise output about an admissible Henneberg node that is needed for Problem 916. -/
def HasNeighborRim (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Prop :=
  ∃ (a : V) (p : G.Walk a a),
    p.IsCycle ∧ v ∉ p.support ∧
      G.neighborFinset v ⊆ p.support.toFinset

/-- A degree-at-least-three node with a rim through all of its neighbours is already the
required wheel witness. -/
theorem hasWheelWitness_of_hasNeighborRim {v : V}
    (hdeg : 3 ≤ G.degree v) (hrim : HasNeighborRim G v) :
    HasWheelWitness G := by
  rcases hrim with ⟨a, p, hp, hvp, hsub⟩
  refine ⟨a, p, v, hp, hvp, ?_⟩
  have hcard : (G.neighborFinset v).card ≤
      (G.neighborFinset v ∩ p.support.toFinset).card := by
    apply Finset.card_le_card
    intro w hw
    exact Finset.mem_inter.mpr ⟨hw, hsub hw⟩
  rw [G.card_neighborFinset_eq_degree] at hcard
  exact hdeg.trans hcard

/-- The particularly useful degree-three specialization of the rim bridge. -/
theorem hasWheelWitness_of_degree_three_rim {v : V}
    (hdeg : G.degree v = 3) (hrim : HasNeighborRim G v) :
    HasWheelWitness G :=
  hasWheelWitness_of_hasNeighborRim (by omega) hrim

/-- The elementary local alternative at a degree-three Henneberg node.  If its three
neighbours are pairwise adjacent, they form a triangular rim and the node is a wheel hub.
Otherwise a nonedge between two neighbours is available for the inverse Henneberg move. -/
theorem wheel_or_nonadjacent_neighbors_of_degree_three {v : V}
    (hdeg : G.degree v = 3) :
    HasWheelWitness G ∨
      ∃ a b : V, G.Adj v a ∧ G.Adj v b ∧ a ≠ b ∧ ¬G.Adj a b := by
  classical
  by_cases hpair :
      ∃ a b : V, G.Adj v a ∧ G.Adj v b ∧ a ≠ b ∧ ¬G.Adj a b
  · exact Or.inr hpair
  · left
    have hNcard : (G.neighborFinset v).card = 3 := by
      simpa only [G.card_neighborFinset_eq_degree] using hdeg
    have htwo : 2 < (G.neighborFinset v).card := by omega
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
      Finset.two_lt_card_iff.mp htwo
    have hva : G.Adj v a := by simpa only [SimpleGraph.mem_neighborFinset] using ha
    have hvb : G.Adj v b := by simpa only [SimpleGraph.mem_neighborFinset] using hb
    have hvc : G.Adj v c := by simpa only [SimpleGraph.mem_neighborFinset] using hc
    have habAdj : G.Adj a b := by
      by_contra hn
      exact hpair ⟨a, b, hva, hvb, hab, hn⟩
    have hbcAdj : G.Adj b c := by
      by_contra hn
      exact hpair ⟨b, c, hvb, hvc, hbc, hn⟩
    have hcaAdj : G.Adj c a := by
      by_contra hn
      exact hpair ⟨c, a, hvc, hva, hac.symm, hn⟩
    let p : G.Walk a a :=
      .cons habAdj (.cons hbcAdj (.cons hcaAdj .nil))
    have hp : p.IsCycle := by
      rw [SimpleGraph.Walk.isCycle_def]
      constructor
      · rw [SimpleGraph.Walk.isTrail_def]
        simp [p, hab, hab.symm, hac, hac.symm, hbc]
      constructor
      · simp [p]
      · simp [p, hab.symm, hac.symm, hbc]
    have hvp : v ∉ p.support := by
      simp [p, hva.ne, hvb.ne, hvc.ne]
    have habcSub : ({a, b, c} : Finset V) ⊆ G.neighborFinset v := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨ha, hb, hc⟩
    have habcCard : ({a, b, c} : Finset V).card = 3 := by
      simp [hab, hac, hbc]
    have habcEq : ({a, b, c} : Finset V) = G.neighborFinset v :=
      Finset.eq_of_subset_of_card_le habcSub (by omega)
    apply hasWheelWitness_of_degree_three_rim hdeg
    refine ⟨a, p, hp, hvp, ?_⟩
    intro w hw
    rw [← habcEq] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp [p]

/-- A degree-three node with a missing edge between two neighbours is the local datum for
an inverse Henneberg-2 move. -/
def IsInverseHennebergNode (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Prop :=
  G.degree v = 3 ∧
    ∃ a b : V, G.Adj v a ∧ G.Adj v b ∧ a ≠ b ∧ ¬G.Adj a b

/-- Delete `v` and insert one edge between two remaining vertices: the inverse
Henneberg-2 graph. -/
def inverseHennebergGraph (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (a b : {w : V // w ∈ ({v}ᶜ : Set V)}) :
    SimpleGraph {w : V // w ∈ ({v}ᶜ : Set V)} :=
  G.induce ({v}ᶜ : Set V) ⊔ SimpleGraph.edge a b

/-- Numerically, an inverse Henneberg move at a degree-three node preserves the circuit
count whenever the inserted edge was absent. -/
theorem inverseHennebergGraph_has23CircuitCount {v : V}
    (hdeg : G.degree v = 3)
    (a b : {w : V // w ∈ ({v}ᶜ : Set V)})
    (hab : ¬G.Adj a.1 b.1) (hne : a ≠ b) :
    Has23CircuitCount G → Has23CircuitCount (inverseHennebergGraph G v a b) := by
  intro hcount
  let H : SimpleGraph {w : V // w ∈ ({v}ᶜ : Set V)} :=
    G.induce ({v}ᶜ : Set V)
  have habH : ¬H.Adj a b := by
    simpa [H, SimpleGraph.induce_adj] using hab
  have hadd : (H ⊔ SimpleGraph.edge a b).edgeFinset.card =
      H.edgeFinset.card + 1 :=
    H.card_edgeFinset_sup_edge habH hne
  have hdelete := delete_degree_three_has_tight_count (G := G) hcount hdeg
  have haddN : (H ⊔ SimpleGraph.edge a b).edgeSet.ncard =
      H.edgeSet.ncard + 1 := by
    simpa only [Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset] using hadd
  have hdeleteN : H.edgeSet.ncard + 3 =
      2 * Fintype.card {w : V // w ∈ ({v}ᶜ : Set V)} := by
    simpa only [H, Set.ncard_eq_toFinset_card', SimpleGraph.edgeFinset] using hdelete
  have hgoalN :
      (G.induce ({v}ᶜ : Set V) ⊔ SimpleGraph.edge a b).edgeSet.ncard + 2 =
        2 * Fintype.card {w : V // w ∈ ({v}ᶜ : Set V)} := by
    change (H ⊔ SimpleGraph.edge a b).edgeSet.ncard + 2 = _
    omega
  apply (has23CircuitCount_iff_ncard (inverseHennebergGraph G v a b)).2
  exact hgoalN

/-- The local inverse-Henneberg alternative with its edge-count invariant already
discharged. -/
theorem wheel_or_inverseHenneberg_of_degree_three {v : V}
    (hcount : Has23CircuitCount G) (hdeg : G.degree v = 3) :
    HasWheelWitness G ∨
      ∃ a b : {w : V // w ∈ ({v}ᶜ : Set V)},
        G.Adj v a.1 ∧ G.Adj v b.1 ∧ a ≠ b ∧ ¬G.Adj a.1 b.1 ∧
          Has23CircuitCount (inverseHennebergGraph G v a b) := by
  rcases wheel_or_nonadjacent_neighbors_of_degree_three (G := G) hdeg with hW | hpair
  · exact Or.inl hW
  · right
    obtain ⟨a, b, hva, hvb, hab, hnab⟩ := hpair
    let a' : {w : V // w ∈ ({v}ᶜ : Set V)} :=
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hva.ne.symm⟩
    let b' : {w : V // w ∈ ({v}ᶜ : Set V)} :=
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hvb.ne.symm⟩
    have hab' : a' ≠ b' := by
      intro h
      exact hab (congrArg Subtype.val h)
    refine ⟨a', b', hva, hvb, hab', hnab, ?_⟩
    exact inverseHennebergGraph_has23CircuitCount (G := G) hdeg a' b' hnab hab' hcount

/-- If the desired wheel is absent, all four degree-three nodes supplied by the
handshaking argument are available for inverse Henneberg moves. -/
theorem four_le_card_inverseHennebergNodes_of_noWheel
    (hcount : Has23CircuitCount G)
    (hmin : ∀ v : V, 3 ≤ G.degree v)
    (hnoWheel : ¬HasWheelWitness G) :
    4 ≤ (Finset.univ.filter fun v : V => IsInverseHennebergNode G v).card := by
  classical
  have hfour := four_le_card_degree_eq_three (G := G) hcount hmin
  have heq :
      (Finset.univ.filter fun v : V => IsInverseHennebergNode G v) =
        Finset.univ.filter fun v : V => G.degree v = 3 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun hv => hv.1
    · intro hv
      refine ⟨hv, ?_⟩
      rcases wheel_or_nonadjacent_neighbors_of_degree_three (G := G) hv with hW | hp
      · exact (hnoWheel hW).elim
      · exact hp
  rw [heq]
  exact hfour

end Erdos916
