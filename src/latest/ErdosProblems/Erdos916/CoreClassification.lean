/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreRigidity

/-!
# Minimal `(2,3)` circuits for Erdős Problem 916

This file gives the exact extremal reduction behind the circuit/cockade route.
From any graph with at least `2 * |V| - 2` edges we choose an inclusion-minimal
vertex set which still has that density, and then retain exactly
`2 * |S| - 2` of its edges.  The resulting spanning subgraph is a `(2,3)`
circuit: every proper induced vertex set is `(2,3)`-sparse.

Consequently it is enough to prove the wheel theorem for `(2,3)` circuits.
All statements here are unconditional finite combinatorics; no structural
classification theorem is assumed in the construction.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A minimal `(2,3)` circuit, stated locally so this extremal reduction is
independent of any particular rigidity formalization. -/
def Minimal23Circuit (G : SimpleGraph V) : Prop :=
  G.edgeSet.ncard + 2 = 2 * Fintype.card V ∧
    ∀ S : Finset V, 2 ≤ S.card → S ≠ Finset.univ →
      (G.edgeSet ∩ (S.sym2 : Set (Sym2 V))).ncard + 3 ≤ 2 * S.card

/-- The instance-independent edge-set formulation is exactly the shared
`Is23Circuit` API from `CoreRigidity`. -/
theorem minimal23Circuit_iff_is23Circuit
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Minimal23Circuit G ↔ Is23Circuit G := by
  have hcount : Has23CircuitCount G ↔
      G.edgeSet.ncard + 2 = 2 * Fintype.card V := by
    rw [Has23CircuitCount, Set.ncard_eq_toFinset_card']
    rfl
  constructor
  · intro h
    constructor
    · exact hcount.2 h.1
    · intro S hS2 hSne
      have hsparse := h.2 S hS2 hSne
      have hsetEq :
          G.edgeSet ∩ (S.sym2 : Set (Sym2 V)) =
            (G.edgeFinset ∩ S.sym2 : Finset (Sym2 V)) := by
        ext e
        simp
      rw [hsetEq, Set.ncard_coe_finset] at hsparse
      have hedgeEq := G.card_filter_edgeFinset_toFinset_subset S
      rw [G.filter_edgeFinset_toFinset_subset] at hedgeEq
      rw [hedgeEq] at hsparse
      exact hsparse
  · intro h
    constructor
    · exact hcount.1 h.1
    · intro S hS2 hSne
      have hsparse := h.2 S hS2 hSne
      have hedgeEq := G.card_filter_edgeFinset_toFinset_subset S
      rw [G.filter_edgeFinset_toFinset_subset] at hedgeEq
      rw [← hedgeEq] at hsparse
      have hsetEq :
          G.edgeSet ∩ (S.sym2 : Set (Sym2 V)) =
            (G.edgeFinset ∩ S.sym2 : Finset (Sym2 V)) := by
        ext e
        simp
      rw [hsetEq, Set.ncard_coe_finset]
      exact hsparse

/-- A vertex set still carrying the forbidden extremal density. -/
def IsDenseSet (S : Finset V) : Prop :=
  4 ≤ S.card ∧
    2 * S.card ≤ (G.edgeFinset ∩ S.sym2).card + 2

/-- A minimum-cardinality dense vertex set exists whenever the ambient graph
is dense.  The second conclusion is the exact minimality property needed
below. -/
theorem exists_minimal_dense_set
    (hcard : 4 ≤ Fintype.card V)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    ∃ S : Finset V, IsDenseSet G S ∧
      ∀ T : Finset V, IsDenseSet G T → S.card ≤ T.card := by
  classical
  let candidates : Finset (Finset V) :=
    Finset.univ.filter (IsDenseSet G)
  have hunivDense : IsDenseSet G (Finset.univ : Finset V) := by
    simpa [IsDenseSet] using And.intro hcard hdense
  have hne : candidates.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp [candidates, hunivDense]
  obtain ⟨S, hS, hmin⟩ :=
    Finset.exists_min_image candidates Finset.card hne
  refine ⟨S, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hS).2
  · intro T hT
    apply hmin T
    simp [candidates, hT]

/-- A dense simple graph has at least four vertices. -/
theorem four_le_card_of_dense_set {S : Finset V}
    (hS : IsDenseSet G S) : 4 ≤ S.card := hS.1

/-- Every proper subset of a minimum-cardinality dense set satisfies the
strict integral `(2,3)` sparsity inequality. -/
theorem sparse_proper_subset_of_minimal_dense
    {S : Finset V}
    (hSmin : ∀ T : Finset V, IsDenseSet G T → S.card ≤ T.card)
    {T : Finset V} (hT2 : 2 ≤ T.card) (hTS : T ⊂ S) :
    (G.induce (T : Set V)).edgeFinset.card + 3 ≤ 2 * T.card := by
  by_cases hT4 : 4 ≤ T.card
  · by_contra hnot
    have hedgeEq := G.card_filter_edgeFinset_toFinset_subset T
    rw [G.filter_edgeFinset_toFinset_subset] at hedgeEq
    have hTdense : IsDenseSet G T := by
      exact ⟨hT4, by rw [hedgeEq]; omega⟩
    have hcardle := hSmin T hTdense
    have hcardlt := Finset.card_lt_card hTS
    omega
  · have hedge := (G.induce (T : Set V)).card_edgeFinset_le_card_choose_two
    have hcard23 : T.card = 2 ∨ T.card = 3 := by omega
    rcases hcard23 with hcard | hcard <;>
      simp [hcard] at hedge ⊢ <;> omega

/-- A graph with at least `2n-2` edges contains, on a vertex subset, a
spanning `(2,3)`-circuit subgraph.  The subgraph relation is recorded
explicitly so that a wheel in the circuit transports to the original graph.
-/
theorem exists_minimal23Circuit_subgraph_with_card
    (hcard : 4 ≤ Fintype.card V)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    ∃ (S : Finset V) (H : SimpleGraph S),
      4 ≤ Fintype.card S ∧
        H ≤ G.induce (S : Set V) ∧ Minimal23Circuit H := by
  classical
  obtain ⟨S, hSdense, hSmin⟩ := exists_minimal_dense_set G hcard hdense
  have hS4 : 4 ≤ S.card := four_le_card_of_dense_set G hSdense
  let J : SimpleGraph S := G.induce (S : Set V)
  let target : ℕ := 2 * S.card - 2
  have htarget : target ≤ J.edgeFinset.card := by
    have hd := hSdense.2
    have hedgeEq := G.card_filter_edgeFinset_toFinset_subset S
    rw [G.filter_edgeFinset_toFinset_subset] at hedgeEq
    rw [hedgeEq] at hd
    change 2 * S.card ≤ J.edgeFinset.card + 2 at hd
    dsimp [target]
    omega
  obtain ⟨E, hEsub, hEcard⟩ :=
    Finset.exists_subset_card_eq htarget
      (s := J.edgeFinset)
  let H : SimpleGraph S := SimpleGraph.fromEdgeSet (E : Set (Sym2 S))
  have hEnodiag : Disjoint (E : Set (Sym2 S)) Sym2.diagSet := by
    rw [Set.disjoint_left]
    intro e heE hediag
    exact (J.not_isDiag_of_mem_edgeFinset (hEsub heE))
      (by simpa only [Sym2.mem_diagSet] using hediag)
  have hHedgeSet : H.edgeSet = (E : Set (Sym2 S)) := by
    change (SimpleGraph.fromEdgeSet (E : Set (Sym2 S))).edgeSet =
      (E : Set (Sym2 S))
    rw [SimpleGraph.edgeSet_fromEdgeSet, hEnodiag.sdiff_eq_left]
  letI : DecidableRel H.Adj := Classical.decRel _
  have hHedgeFinset : H.edgeFinset = E := by
    apply Finset.coe_injective
    simpa [hHedgeSet]
  have hHJ : H ≤ J := by
    rw [← SimpleGraph.edgeSet_subset_edgeSet, hHedgeSet,
      ← SimpleGraph.coe_edgeFinset]
    exact_mod_cast hEsub
  refine ⟨S, H, by simpa using hS4, hHJ, ?_⟩
  constructor
  · rw [hHedgeSet, Set.ncard_coe_finset, hEcard]
    rw [Fintype.card_coe]
    dsimp [target]
    omega
  · intro T hT2 hTne
    let valS : S ↪ V := Function.Embedding.subtype _
    let U : Finset V := T.map valS
    have hUcard : U.card = T.card := by simp [U, valS]
    have hUS : U ⊆ S := by
      intro x hx
      simp only [U, Finset.mem_map] at hx
      obtain ⟨t, -, rfl⟩ := hx
      exact t.2
    have hUne : U ≠ S := by
      intro hUS_eq
      apply hTne
      apply Finset.eq_univ_of_forall
      intro t
      have htU : t.1 ∈ U := by rw [hUS_eq]; exact t.2
      simp only [U, Finset.mem_map] at htU
      obtain ⟨z, hzT, hz⟩ := htU
      have hzt : z = t := by
        apply Subtype.ext
        simpa [valS] using hz
      simpa [hzt] using hzT
    have hUproper : U ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hUS, hUne⟩
    have hsparseU :=
      sparse_proper_subset_of_minimal_dense G hSmin
        (by rw [hUcard]; exact hT2) hUproper
    have hmapSub :
        (H.edgeFinset ∩ T.sym2).map valS.sym2Map ⊆
          G.edgeFinset ∩ U.sym2 := by
      intro e he
      rw [Finset.mem_map] at he
      obtain ⟨e₀, he₀, rfl⟩ := he
      have heH := (Finset.mem_inter.mp he₀).1
      have heT := (Finset.mem_inter.mp he₀).2
      apply Finset.mem_inter.mpr
      constructor
      · cases e₀ using Sym2.inductionOn with
        | _ a b =>
            rw [Function.Embedding.sym2Map_apply, Sym2.map_mk]
            apply SimpleGraph.mem_edgeFinset.mpr
            apply hHJ
            exact SimpleGraph.mem_edgeFinset.mp heH
      · have heMap : valS.sym2Map e₀ ∈ T.sym2.map valS.sym2Map :=
          Finset.mem_map.mpr ⟨e₀, heT, rfl⟩
        simpa only [U, Finset.sym2_map] using heMap
    have hedgeLe := Finset.card_le_card hmapSub
    rw [Finset.card_map] at hedgeLe
    have hedgeUEq := G.card_filter_edgeFinset_toFinset_subset U
    rw [G.filter_edgeFinset_toFinset_subset] at hedgeUEq
    rw [← hedgeUEq] at hsparseU
    rw [hUcard] at hsparseU
    have hsetEq :
        H.edgeSet ∩ (T.sym2 : Set (Sym2 S)) =
          (H.edgeFinset ∩ T.sym2 : Finset (Sym2 S)) := by
      ext e
      simp
    rw [hsetEq, Set.ncard_coe_finset]
    omega

/-- Compatibility wrapper for callers that do not need the cardinality of the
extracted circuit. -/
theorem exists_minimal23Circuit_subgraph
    (hcard : 4 ≤ Fintype.card V)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    ∃ (S : Finset V) (H : SimpleGraph S),
      H ≤ G.induce (S : Set V) ∧ Minimal23Circuit H := by
  obtain ⟨S, H, -, hHG, hH⟩ :=
    exists_minimal23Circuit_subgraph_with_card G hcard hdense
  exact ⟨S, H, hHG, hH⟩

/-- Shared-API form of `exists_minimal23Circuit_subgraph`.  The adjacency
decider is recorded explicitly because it is data required by `Is23Circuit`,
while the underlying circuit property is independent of that choice. -/
theorem exists_is23Circuit_subgraph_with_card
    (hcard : 4 ≤ Fintype.card V)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    ∃ (S : Finset V) (H : SimpleGraph S),
      4 ≤ Fintype.card S ∧
        H ≤ G.induce (S : Set V) ∧
          @Is23Circuit S _ H (Classical.decRel H.Adj) := by
  classical
  rcases exists_minimal23Circuit_subgraph_with_card G hcard hdense with
    ⟨S, H, hS4, hHG, hHcircuit⟩
  refine ⟨S, H, hS4, hHG, ?_⟩
  exact (@minimal23Circuit_iff_is23Circuit S _ _ H
    (Classical.decRel H.Adj)).mp hHcircuit

/-- Compatibility wrapper for the shared circuit API. -/
theorem exists_is23Circuit_subgraph
    (hcard : 4 ≤ Fintype.card V)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    ∃ (S : Finset V) (H : SimpleGraph S),
      H ≤ G.induce (S : Set V) ∧
        @Is23Circuit S _ H (Classical.decRel H.Adj) := by
  obtain ⟨S, H, -, hHG, hH⟩ :=
    exists_is23Circuit_subgraph_with_card G hcard hdense
  exact ⟨S, H, hHG, hH⟩

end Erdos916
