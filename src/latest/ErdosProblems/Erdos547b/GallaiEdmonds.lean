/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Combinatorics.SimpleGraph.Tutte
import Mathlib.Combinatorics.SimpleGraph.Hall
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Tauto

open scoped SimpleGraph

namespace GallaiEdmonds547

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A matching covering all vertices except the specified vertex. -/
def IsNearPerfectMatchingMissing (M : G.Subgraph) (x : V) : Prop :=
  M.IsMatching ∧ M.vertsᶜ = {x}

/-- A matching covering all but exactly one vertex. -/
def IsNearPerfectMatching (M : G.Subgraph) : Prop :=
  ∃ x, IsNearPerfectMatchingMissing M x

/-- A maximum-cardinality matching, measured by its number of edges. -/
def IsMaximumMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ N : G.Subgraph, N.IsMatching →
    N.verts.ncard ≤ M.verts.ncard

/-- The vertices of a finite matching are exactly twice as numerous as its edges. -/
theorem card_verts_eq_two_mul_card_edges {M : G.Subgraph} (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.coe.edgeSet.ncard := by
  classical
  let : Fintype M.verts := Fintype.ofFinite _
  have hdeg (v : M.verts) : M.coe.degree v = 1 := by
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
    obtain ⟨w, hvw, huniq⟩ := hM v.property
    refine ⟨⟨w, M.edge_vert hvw.symm⟩, ?_, ?_⟩
    · exact hvw
    · intro y hvy
      apply Subtype.ext
      exact huniq y hvy
  have hcard : M.verts.toFinset.card = 2 * M.coe.edgeFinset.card := by
    calc
      M.verts.toFinset.card = ∑ _v : M.verts, 1 := by simp
      _ = ∑ v : M.verts, M.coe.degree v := by simp_rw [hdeg]
      _ = 2 * M.coe.edgeFinset.card := by
        convert M.coe.sum_degrees_eq_twice_card_edges using 1
        apply Finset.sum_congr rfl
        intro v _
        unfold SimpleGraph.degree
        congr 1
        ext w
        simp
  calc
    M.verts.ncard = M.verts.toFinset.card := Set.ncard_eq_toFinset_card' _
    _ = 2 * M.coe.edgeFinset.card := hcard
    _ = 2 * M.coe.edgeSet.ncard := by
      rw [Set.ncard_eq_toFinset_card']
      have hedge : M.coe.edgeFinset = M.coe.edgeSet.toFinset := by
        ext e
        simp
      rw [hedge]

/-- Every finite graph has a maximum-cardinality matching. -/
theorem exists_isMaximumMatching (G : SimpleGraph V) :
    ∃ M : G.Subgraph, IsMaximumMatching M := by
  classical
  let good : Set G.Subgraph := {M | M.IsMatching}
  have hgood_finite : good.Finite := Set.toFinite good
  have hgood_nonempty : good.Nonempty := by
    refine ⟨⊥, ?_⟩
    change (⊥ : G.Subgraph).IsMatching
    intro v hv
    simpa using hv
  obtain ⟨M, hM, hmax⟩ :=
    Set.exists_max_image good (fun N : G.Subgraph => N.verts.ncard)
      hgood_finite hgood_nonempty
  exact ⟨M, hM, fun N hN => hmax N hN⟩

/-- The vertex-count definition of maximum matching also maximizes edge count. -/
theorem IsMaximumMatching.edge_card_le {M N : G.Subgraph}
    (hM : IsMaximumMatching M) (hN : N.IsMatching) :
    N.coe.edgeSet.ncard ≤ M.coe.edgeSet.ncard := by
  have hverts : N.verts.ncard ≤ M.verts.ncard := hM.2 N hN
  rw [card_verts_eq_two_mul_card_edges hN,
    card_verts_eq_two_mul_card_edges hM.1] at hverts
  omega

theorem IsNearPerfectMatchingMissing.card_compl {M : G.Subgraph} {x : V}
    (hM : IsNearPerfectMatchingMissing M x) : M.vertsᶜ.ncard = 1 := by
  rw [hM.2, Set.ncard_singleton]

theorem IsNearPerfectMatchingMissing.mem_verts_iff {M : G.Subgraph} {x y : V}
    (hM : IsNearPerfectMatchingMissing M x) : y ∈ M.verts ↔ y ≠ x := by
  have hc : y ∈ M.vertsᶜ ↔ y ∈ ({x} : Set V) := by rw [hM.2]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
  tauto

theorem IsNearPerfectMatchingMissing.card_verts {M : G.Subgraph} {x : V}
    (hM : IsNearPerfectMatchingMissing M x) :
    M.verts.ncard = Fintype.card V - 1 := by
  have hsum : M.verts.ncard + M.vertsᶜ.ncard = Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl M.verts
  have hcompl : M.vertsᶜ.ncard = 1 := hM.card_compl
  omega

theorem IsNearPerfectMatchingMissing.card_eq_two_mul_card_edges_add_one
    {M : G.Subgraph} {x : V} (hM : IsNearPerfectMatchingMissing M x) :
    Fintype.card V = 2 * M.coe.edgeSet.ncard + 1 := by
  have hsum : M.verts.ncard + M.vertsᶜ.ncard = Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl M.verts
  rw [card_verts_eq_two_mul_card_edges hM.1, hM.card_compl] at hsum
  omega

/-- On an odd-order graph, a matching missing at most one vertex is near-perfect. -/
theorem IsMatching.isNearPerfectMatching_of_odd_of_card_le_succ {M : G.Subgraph}
    (hM : M.IsMatching) (hodd : Odd (Fintype.card V))
    (hcover : Fintype.card V ≤ M.verts.ncard + 1) : IsNearPerfectMatching M := by
  classical
  have hsum : M.verts.ncard + M.vertsᶜ.ncard = Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl M.verts
  have heven : Even M.verts.ncard := by
    let : Fintype M.verts := Fintype.ofFinite _
    rw [Set.ncard_eq_toFinset_card']
    exact hM.even_card
  rcases hodd with ⟨a, ha⟩
  rcases heven with ⟨b, hb⟩
  have hcompl : M.vertsᶜ.ncard = 1 := by omega
  rw [Set.ncard_eq_one] at hcompl
  obtain ⟨x, hx⟩ := hcompl
  exact ⟨x, hM, hx⟩

/-- Every vertex deletion leaves a perfect matching, expressed without changing vertex types. -/
def IsFactorCritical (G : SimpleGraph V) : Prop :=
  ∀ x : V, ∃ M : G.Subgraph, IsNearPerfectMatchingMissing M x

theorem IsFactorCritical.odd_card [Nonempty V]
    (hG : IsFactorCritical G) : Odd (Fintype.card V) := by
  classical
  let x : V := Classical.choice inferInstance
  obtain ⟨M, hM⟩ := hG x
  have heven : Even M.verts.ncard := by
    let : Fintype M.verts := Fintype.ofFinite _
    rw [Set.ncard_eq_toFinset_card']
    exact hM.1.even_card
  have hsum : M.verts.ncard + M.vertsᶜ.ncard = Fintype.card V := by
    simpa [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl M.verts
  have hcompl : M.vertsᶜ.ncard = 1 := hM.card_compl
  rcases heven with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  omega

namespace ConnectedComponent

/-- A perfect matching of a connected component becomes an ambient matching
covering exactly that component. -/
theorem map_perfectMatching_to_ambient (C : G.ConnectedComponent)
    {N : C.toSimpleGraph.Subgraph} (hN : N.IsPerfectMatching) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = C.supp := by
  classical
  let M : G.Subgraph := N.map C.toSimpleGraph_hom
  refine ⟨M, hN.1.map C.toSimpleGraph_hom Subtype.val_injective, ?_⟩
  rw [Subgraph.map_verts, hN.2.verts_eq_univ]
  ext v
  constructor
  · rintro ⟨a, -, ha⟩
    rw [← ha]
    exact a.property
  · intro hv
    refine ⟨⟨v, hv⟩, Set.mem_univ _, ?_⟩
    rfl

/-- A near-perfect matching of a connected component becomes an ambient matching
covering the component except for the same specified vertex. -/
theorem map_nearPerfectMatching_to_ambient (C : G.ConnectedComponent)
    {N : C.toSimpleGraph.Subgraph} {x : C}
    (hN : IsNearPerfectMatchingMissing N x) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = C.supp \ {x.1} := by
  classical
  let M : G.Subgraph := N.map C.toSimpleGraph_hom
  refine ⟨M, hN.1.map C.toSimpleGraph_hom Subtype.val_injective, ?_⟩
  have hverts : N.verts = ({x} : Set C)ᶜ := by
    apply compl_injective
    simpa using hN.2
  rw [Subgraph.map_verts, hverts]
  ext v
  constructor
  · rintro ⟨a, ha, hva⟩
    have hane : a ≠ x := by simpa using ha
    have hav : a.1 = v := by
      simpa [ConnectedComponent.toSimpleGraph_hom_apply] using hva
    refine ⟨?_, ?_⟩
    · rw [← hav]
      exact a.property
    · simp only [Set.mem_singleton_iff]
      intro hvx
      apply hane
      apply Subtype.ext
      exact hav.trans hvx
  · rintro ⟨hvC, hvx⟩
    refine ⟨⟨v, hvC⟩, ?_, ?_⟩
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      apply hvx
      simp only [Set.mem_singleton_iff]
      exact congrArg Subtype.val heq
    · rfl

end ConnectedComponent

end GallaiEdmonds547
