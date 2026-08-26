import ErdosProblems.Erdos19.MatchingFamilyHypergraph
import ErdosProblems.Erdos19.CompatibleColorings
import ErdosProblems.Erdos19.ReservedPaletteEmbedding

/-! # Extending color classes by a disjoint family of pair matchings -/

namespace Erdos19.SetHypergraph

variable {V I : Type*} [Fintype V]

theorem unionColoring_covered_eq_of_disjoint (J K : SetHypergraph V)
    (cJ : J.EdgeColoring I) (cK : K.EdgeColoring I) (hJK : Disjoint J K)
    (hcross : ∀ e : J, ∀ f : K, (e.1 ∩ f.1).Nonempty → cJ e ≠ cK f) (i : I) :
    (J ∪ K).coveredVertices {e | (J.unionColoring K cJ cK hcross) e = i} =
      J.coveredVertices {e | cJ e = i} ∪ K.coveredVertices {e | cK e = i} := by
  apply Set.Subset.antisymm (J.unionColoring_covered_subset K cJ cK hcross i)
  intro v hv
  rcases hv with hv | hv
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hei, hve⟩ := Set.mem_iUnion.mp he
    refine Set.mem_iUnion.mpr ⟨⟨e.1, Or.inl e.2⟩, Set.mem_iUnion.mpr ⟨?_, hve⟩⟩
    exact (J.unionColoring_left K cJ cK hcross e).trans hei
  · obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hei, hve⟩ := Set.mem_iUnion.mp he
    refine Set.mem_iUnion.mpr ⟨⟨e.1, Or.inr e.2⟩, Set.mem_iUnion.mpr ⟨?_, hve⟩⟩
    exact (J.unionColoring_right K cJ cK hcross e
      (fun heJ ↦ Set.disjoint_left.mp hJK heJ e.2)).trans hei

theorem extend_coloring_by_matching_family (J : SetHypergraph V)
    {G : _root_.SimpleGraph V} (M : I → G.Subgraph)
    (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe)
    (hnew : Disjoint J (matchingFamilyHypergraph M)) (color : J.EdgeColoring I)
    (havoid : ∀ i, Disjoint (J.coveredVertices {e | color e = i}) (M i).verts) :
    ∃ c : (J ∪ matchingFamilyHypergraph M).EdgeColoring I,
      (∀ e : J, c ⟨e.1, Or.inl e.2⟩ = color e) ∧
      ∀ i, (J ∪ matchingFamilyHypergraph M).coveredVertices {e | c e = i} =
        J.coveredVertices {e | color e = i} ∪ (M i).verts := by
  obtain ⟨cM, _, hcoverM⟩ := exists_matching_family_hypergraph_coloring M hM hdis
  have hcross : ∀ e : J, ∀ f : matchingFamilyHypergraph M,
      (e.1 ∩ f.1).Nonempty → color e ≠ cM f := by
    intro e f hinter heq
    obtain ⟨v, hve, hvf⟩ := hinter
    apply Set.disjoint_left.mp (havoid (color e))
      (Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨rfl, hve⟩⟩)
    rw [← hcoverM (color e)]
    exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨heq.symm, hvf⟩⟩
  refine ⟨J.unionColoring (matchingFamilyHypergraph M) color cM hcross,
    J.unionColoring_left _ _ _ _, ?_⟩
  intro i
  rw [unionColoring_covered_eq_of_disjoint J _ color cM hnew hcross i, hcoverM i]

theorem twoGraph_union (H J : SetHypergraph V) : (H ∪ J).twoGraph = H.twoGraph ⊔ J.twoGraph := by
  ext x y
  change (x ≠ y ∧ (({x, y} : Set V) ∈ H ∨ {x, y} ∈ J)) ↔
    ((x ≠ y ∧ ({x, y} : Set V) ∈ H) ∨ (x ≠ y ∧ ({x, y} : Set V) ∈ J))
  tauto

theorem twoGraph_sdiff (H J : SetHypergraph V) : (H \ J).twoGraph = H.twoGraph \ J.twoGraph := by
  ext x y
  change (x ≠ y ∧ (({x, y} : Set V) ∈ H ∧ {x, y} ∉ J)) ↔
    ((x ≠ y ∧ ({x, y} : Set V) ∈ H) ∧ ¬(x ≠ y ∧ ({x, y} : Set V) ∈ J))
  tauto

theorem extend_coloring_by_indexed_matching_family {P : Type*}
    (J : SetHypergraph V) {G : _root_.SimpleGraph V} (M : P → G.Subgraph)
    (hM : ∀ i, (M i).IsMatching)
    (hdis : Pairwise fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe)
    (hnew : Disjoint J (matchingFamilyHypergraph M)) (color : J.EdgeColoring I)
    (index : P ↪ I)
    (havoid : ∀ i, Disjoint (J.coveredVertices {e | color e = index i}) (M i).verts) :
    ∃ c : (J ∪ matchingFamilyHypergraph M).EdgeColoring I,
      (∀ e : J, c ⟨e.1, Or.inl e.2⟩ = color e) ∧
      (∀ i, (J ∪ matchingFamilyHypergraph M).coveredVertices {e | c e = index i} =
        J.coveredVertices {e | color e = index i} ∪ (M i).verts) ∧
      (∀ a, J.coveredVertices {e | color e = a} ⊆
        (J ∪ matchingFamilyHypergraph M).coveredVertices {e | c e = a}) ∧
      ∀ e : matchingFamilyHypergraph M, c ⟨e.1, Or.inr e.2⟩ ∈ Set.range index := by
  obtain ⟨cM, _, hcoverM⟩ := exists_matching_family_hypergraph_coloring M hM hdis
  let cM' := cM.mapEmbedding index
  have hcoverIndex (i : P) :
      (matchingFamilyHypergraph M).coveredVertices {e | cM' e = index i} = (M i).verts := by
    have hclass : ({e : matchingFamilyHypergraph M | cM' e = index i} :
        Set (matchingFamilyHypergraph M)) = {e | cM e = i} := by
      ext e
      exact index.injective.eq_iff
    rw [hclass, hcoverM i]
  have hcross : ∀ e : J, ∀ f : matchingFamilyHypergraph M,
      (e.1 ∩ f.1).Nonempty → color e ≠ cM' f := by
    intro e f hinter heq
    obtain ⟨v, hve, hvf⟩ := hinter
    apply Set.disjoint_left.mp (havoid (cM f))
      (Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heq, hve⟩⟩)
    rw [← hcoverM (cM f)]
    exact Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨rfl, hvf⟩⟩
  let c := J.unionColoring (matchingFamilyHypergraph M) color cM' hcross
  refine ⟨c, J.unionColoring_left _ _ _ _, ?_, ?_, ?_⟩
  · intro i
    rw [unionColoring_covered_eq_of_disjoint J _ color cM' hnew hcross (index i), hcoverIndex i]
  · intro a
    rw [unionColoring_covered_eq_of_disjoint J _ color cM' hnew hcross a]
    exact Set.subset_union_left
  · intro e
    refine ⟨cM e, ?_⟩
    exact (J.unionColoring_right _ color cM' hcross e
      (fun heJ ↦ Set.disjoint_left.mp hnew heJ e.2)).symm

#print axioms extend_coloring_by_matching_family
#print axioms extend_coloring_by_indexed_matching_family

end Erdos19.SetHypergraph
