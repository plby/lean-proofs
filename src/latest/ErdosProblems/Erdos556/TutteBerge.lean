import ErdosProblems.Erdos556.BergeReduction
import ErdosProblems.Erdos556.MatchingCompletion

/-!
# The exact Tutte--Berge matching certificate

Every maximum matching has a deleted set attaining its uncovered-vertex
deficit. The proof uses the parity gap and both universal-extension bounds.
-/

namespace Erdos556

open SimpleGraph

theorem odd_component_defect_even {V : Type*} [Finite V] (G : SimpleGraph V) (X : Set V) :
    Even (((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard + X.ncard + Nat.card V) := by
  have hcard : Nat.card ((⊤ : G.Subgraph).deleteVerts X).verts + X.ncard = Nat.card V := by
    simpa [Subgraph.deleteVerts_verts, Subgraph.verts_top, Nat.card_coe_set_eq,
      Set.compl_eq_univ_sdiff, Nat.add_comm]
      using Set.ncard_add_ncard_compl X
  have hp := SimpleGraph.odd_ncard_oddComponents ((⊤ : G.Subgraph).deleteVerts X).coe
  rw [Nat.odd_iff, Nat.odd_iff] at hp
  rw [Nat.even_iff]
  omega

open scoped Classical in
theorem maximum_edgeMatching_barrier {V : Type*} [Finite V] (G : SimpleGraph V)
    {M : Finset (Sym2 V)} (hM : EdgeMatching G M)
    (hmax : ∀ F, EdgeMatching G F → F.card ≤ M.card) :
    ∃ X : Set V, ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard + 2 * M.card =
      X.ncard + Nat.card V := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hsize : 2 * M.card ≤ Nat.card V := by
    have hh := Finset.card_le_univ (matchingSupport M)
    rw [hM.card_support, Fintype.card_eq_nat_card] at hh
    exact hh
  let k := Nat.card V - 2 * M.card
  have hkN : Nat.card V = 2 * M.card + k := by dsimp [k]; omega
  by_cases hk : k ≤ 1
  · refine ⟨∅, ?_⟩
    have hb := hM.odd_components_bound (∅ : Set V)
    obtain ⟨s, hs⟩ := odd_component_defect_even G (∅ : Set V)
    simp only [Set.ncard_empty] at hb hs ⊢
    omega
  · by_contra hnone
    push Not at hnone
    have hbound : ∀ X : Set V,
        ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard ≤ X.ncard + (k - 2) := by
      intro X
      have hb := hM.odd_components_bound X
      have hne := hnone X
      obtain ⟨s, hs⟩ := odd_component_defect_even G X
      omega
    have hparity : Even (Nat.card V + (k - 2)) := by
      refine ⟨M.card + k - 1, ?_⟩
      omega
    obtain ⟨F, hF, hcard⟩ := matching_of_odd_components_bound G hparity hbound
    have hh := hmax F hF
    omega

open scoped Classical in
theorem tutte_berge_certificate {V : Type*} [Finite V] (G : SimpleGraph V) :
    ∃ M : Finset (Sym2 V), EdgeMatching G M ∧
      (∀ F, EdgeMatching G F → F.card ≤ M.card) ∧
      ∃ X : Set V, ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard + 2 * M.card =
        X.ncard + Nat.card V := by
  classical
  let : Fintype V := Fintype.ofFinite V
  obtain ⟨M, hM, hmax⟩ := exists_maximum_edgeMatching G
  exact ⟨M, hM, hmax, maximum_edgeMatching_barrier G hM hmax⟩

end Erdos556
