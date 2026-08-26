import ErdosProblems.Erdos19.ReservoirRepairIteration
import ErdosProblems.Erdos19.MatchingColorExtension

/-! # Turning block repairs into a partial coloring that saturates an active palette -/

namespace Erdos19.SetHypergraph

variable {V I C : Type*} [Fintype V]

attribute [local instance] Classical.propDecidable

theorem exists_extension_covering_active_colors (H J : SetHypergraph V) (hJH : J ⊆ H)
    (color : J.EdgeColoring C) (p : ℕ) (index : Fin p ↪ C)
    (U Y : Set V) (hUY : Disjoint U Y) (X : I → Set V)
    (hX : Pairwise fun i j ↦ Disjoint (X i) (X j)) (hXcover : ∀ v, ∃ i, v ∈ X i)
    (missing requests : ℕ) (B : Fin p → I → Set V)
    (hBY : ∀ i j, B i j ⊆ Y) (hBX : ∀ i j, B i j ⊆ X j)
    (hBavoid : ∀ i j, Disjoint (B i j) (J.coveredVertices {e | color e = index i}))
    (hBsize : ∀ i j, missing + requests ≤ (B i j).ncard)
    (hmissing : ∀ i j u, u ∈ (U \ J.coveredVertices {e | color e = index i}) ∩ X j →
      ((((U \ J.coveredVertices {e | color e = index i}) ∩ X j) ∪ B i j) \
        (H \ J).twoGraph.neighborSet u).ncard ≤ missing)
    (hrequests : ∀ v, (∑ i : Fin p,
      if v ∈ U \ J.coveredVertices {e | color e = index i} then 1 else 0) ≤ requests) :
    ∃ J' : SetHypergraph V, ∃ color' : J'.EdgeColoring C,
      J ⊆ J' ∧ J' ⊆ H ∧
      (∀ e : J, ∀ he : e.1 ∈ J', color' ⟨e.1, he⟩ = color e) ∧
      (∀ i, U ⊆ J'.coveredVertices {e | color' e = index i}) ∧
      ∀ a, J.coveredVertices {e | color e = a} ⊆ J'.coveredVertices {e | color' e = a} := by
  classical
  let G := (H \ J).twoGraph
  let A : Fin p → Set V := fun i ↦ U \ J.coveredVertices {e | color e = index i}
  have hused : ∀ u ∈ U, ((⊥ : _root_.SimpleGraph V).neighborSet u).ncard ≤ 0 := by
    intro u _
    simp
  have hrequestsA : ∀ v, (∑ i : Fin p, if v ∈ A i then 1 else 0) ≤ requests := by
    intro v
    apply le_trans _ (hrequests v)
    apply Finset.sum_le_sum
    intro i _
    by_cases hv : v ∈ A i
    · have hv' : v ∈ U \ J.coveredVertices {e | color e = index i} := hv
      simp only [if_pos hv, if_pos hv', le_refl]
    · simp only [if_neg hv, Nat.zero_le]
  obtain ⟨M, hM, hdis⟩ := exists_reservoir_repair_family G ⊥ U Y hUY X hX hXcover
    missing 0 requests hused p A B (fun _ ↦ Set.sdiff_subset) hBY hBX
    (by simpa only [Nat.add_zero] using hBsize) hmissing (by
      intro v
      convert! hrequestsA v using 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases hv : v ∈ A i <;> simp only [hv, ↓reduceIte])
  have hnewSubset : matchingFamilyHypergraph M ⊆ H \ J := by
    intro e he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
    obtain ⟨x, y, hxy, rfl⟩ := hi
    exact hxy.adj_sub.2
  have hnew : Disjoint J (matchingFamilyHypergraph M) :=
    Set.disjoint_left.mpr (fun _ heJ heM ↦ (hnewSubset heM).2 heJ)
  have havoid : ∀ i, Disjoint (J.coveredVertices {e | color e = index i}) (M i).verts := by
    intro i
    apply Set.disjoint_left.mpr
    intro v hvC hvM
    rcases (hM i).2.2.1 hvM with hv | hv
    · exact hv.2 hvC
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hv
      exact Set.disjoint_left.mp (hBavoid i j) hj hvC
  obtain ⟨color', hagree, hcoverage, hold, _⟩ := J.extend_coloring_by_indexed_matching_family
    M (fun i ↦ (hM i).1) hdis hnew color index havoid
  refine ⟨J ∪ matchingFamilyHypergraph M, color', Set.subset_union_left,
    Set.union_subset hJH (hnewSubset.trans Set.sdiff_subset), ?_, ?_, hold⟩
  · intro e _
    exact hagree e
  · intro i v hv
    rw [hcoverage i]
    by_cases hvC : v ∈ J.coveredVertices {e | color e = index i}
    · exact Or.inl hvC
    · exact Or.inr ((hM i).2.1 ⟨hv, hvC⟩)

#print axioms exists_extension_covering_active_colors

end Erdos19.SetHypergraph
