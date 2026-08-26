import ErdosProblems.Erdos1010.DenseCounting

/-! # A maximum-degree vertex with a sparse open antineighborhood -/

open Finset

namespace Erdos1010

theorem exists_sparse_antineighborhood {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (D : ℕ)
    (hn : Fintype.card V = 2 * D + 3) (hcap : ∀ x, F.degree x ≤ D)
    (v : V) (hv : F.degree v = D) :
    ∃ u, F.degree u = D ∧ (internalPairs F (antiNeighbors F u)).card ≤ (D + 1).choose 2 := by
  classical
  let A := F.neighborFinset v
  let B := antiNeighbors F v
  have hAcard : A.card = D := by simpa [A] using hv
  have hBcard : B.card = D + 2 := by rw [card_antiNeighbors, hn, hv]; omega
  by_cases hBsmall : (internalPairs F B).card ≤ (D + 1).choose 2
  · exact ⟨v, hv, hBsmall⟩
  let H := (F.induce (B : Set V))ᶜ
  have hBtype : Fintype.card (B : Set V) = D + 2 := by simpa using hBcard
  have hHmin : ∀ u, 1 ≤ H.degree u := by
    intro u
    have hle := (degree_induce_finset_le F B u).trans (hcap u.val)
    dsimp [H]
    rw [SimpleGraph.degree_compl]
    simp only [Fintype.card_coe, hBcard]
    omega
  have hHedge : H.edgeFinset.card + 2 ≤ Fintype.card (B : Set V) := by
    have hc := edges_add_compl_edges (F.induce (B : Set V))
    rw [hBtype, ← card_internalPairs, choose_add_two] at hc
    dsimp [H]
    simp only [Fintype.card_coe, hBcard]
    omega
  obtain ⟨u₁, u₂, w₁, w₂, hu₁, hu₂, hu₁w₁, hu₂w₂, hwne⟩ :=
    exists_distinct_leaf_supports H hHmin hHedge
  have hwne' : w₁.val ≠ w₂.val := fun h ↦ hwne (Subtype.ext h)
  have hw₁ : w₁.val ≠ v ∧ ¬F.Adj v w₁.val := (mem_antiNeighbors F v w₁.val).mp w₁.property
  have hw₂ : w₂.val ≠ v ∧ ¬F.Adj v w₂.val := (mem_antiNeighbors F v w₂.val).mp w₂.property
  have hu₁data := leaf_complement_induce_anti F B D hBcard hcap u₁ w₁ hu₁ hu₁w₁
  have hu₂data := leaf_complement_induce_anti F B D hBcard hcap u₂ w₂ hu₂ hu₂w₂
  have ha₁ : antiNeighbors F u₁.val = insert w₁.val (insert v A) := by
    rw [hu₁data.2]
    change (antiNeighbors F v)ᶜ ∪ {w₁.val} = insert w₁.val (insert v A)
    rw [compl_antiNeighbors, union_singleton]
  have ha₂ : antiNeighbors F u₂.val = insert w₂.val (insert v A) := by
    rw [hu₂data.2]
    change (antiNeighbors F v)ᶜ ∪ {w₂.val} = insert w₂.val (insert v A)
    rw [compl_antiNeighbors, union_singleton]
  have he₁ : (internalPairs F (antiNeighbors F u₁.val)).card =
      (internalPairs F A).card + D + (F.neighborFinset w₁.val ∩ A).card := by
    rw [ha₁]
    simpa [A, hv] using internalPairs_neighborhood_insert_two F v w₁.val hw₁.1 hw₁.2
  have he₂ : (internalPairs F (antiNeighbors F u₂.val)).card =
      (internalPairs F A).card + D + (F.neighborFinset w₂.val ∩ A).card := by
    rw [ha₂]
    simpa [A, hv] using internalPairs_neighborhood_insert_two F v w₂.val hw₂.1 hw₂.2
  have hT : ({v, w₁.val, w₂.val} : Finset V) ⊆ Aᶜ := by
    simp [insert_subset_iff, A, hw₁.2, hw₂.2]
  have hsel := selected_external_neighbors_bound F A {v, w₁.val, w₂.val} hT D (fun x _ ↦ hcap x)
  have hsum : (∑ x ∈ ({v, w₁.val, w₂.val} : Finset V), (F.neighborFinset x ∩ A).card) =
      D + (F.neighborFinset w₁.val ∩ A).card + (F.neighborFinset w₂.val ∩ A).card := by
    rw [sum_insert (by simp [hw₁.1.symm, hw₂.1.symm]), sum_pair hwne']
    simp [A, hv, add_assoc]
  rw [hsum, hAcard] at hsel
  have hchoose := twice_choose_succ_two D
  have htotal : (internalPairs F (antiNeighbors F u₁.val)).card +
      (internalPairs F (antiNeighbors F u₂.val)).card ≤ 2 * (D + 1).choose 2 := by
    nlinarith
  by_cases h₁ : (internalPairs F (antiNeighbors F u₁.val)).card ≤ (D + 1).choose 2
  · exact ⟨u₁.val, hu₁data.1, h₁⟩
  · exact ⟨u₂.val, hu₂data.1, by omega⟩

end Erdos1010
