import ErdosProblems.Erdos19.MatchingTransport

/-! # Merging cross-matchings with matchings in the complementary induced graph -/

namespace Erdos19

open _root_.SimpleGraph

variable {V I : Type*} (G : _root_.SimpleGraph V) (X : Set V)

def inducedMatchingLift (B : (G.induce Xᶜ).Subgraph) : G.Subgraph :=
  B.map (_root_.SimpleGraph.Embedding.induce Xᶜ).toHom

theorem inducedMatchingLift_mem (B : (G.induce Xᶜ).Subgraph) (v : V) :
    v ∈ (inducedMatchingLift G X B).verts ↔ ∃ hv : v ∉ X, (⟨v, hv⟩ : ↥(Xᶜ)) ∈ B.verts := by
  change (∃ w : ↥(Xᶜ), w ∈ B.verts ∧ w.1 = v) ↔ _
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hv, hw⟩
    exact ⟨⟨v, hv⟩, hw, rfl⟩

theorem inducedMatchingLift_disjoint_cross (P : G.Subgraph)
    (hcross : ∀ x y, P.Adj x y → x ∈ X ∨ y ∈ X) (B : (G.induce Xᶜ).Subgraph) :
    Disjoint P.spanningCoe (inducedMatchingLift G X B).spanningCoe := by
  apply _root_.SimpleGraph.disjoint_left.mpr
  intro x y hp hb
  obtain ⟨a, b, _, ha, hb⟩ := hb
  have hx : x ∉ X := ha ▸ a.2
  have hy : y ∉ X := hb ▸ b.2
  exact (hcross x y hp).elim hx hy

theorem merge_induced_matching_families
    (P : I → G.Subgraph) (B : I → (G.induce Xᶜ).Subgraph)
    (hP : ∀ i, (P i).IsMatching) (hB : ∀ i, (B i).IsMatching)
    (hPd : Pairwise (fun i j ↦ Disjoint (P i).spanningCoe (P j).spanningCoe))
    (hBd : Pairwise (fun i j ↦ Disjoint (B i).spanningCoe (B j).spanningCoe))
    (hcross : ∀ i x y, (P i).Adj x y → x ∈ X ∨ y ∈ X)
    (havoid : ∀ i v, v ∈ (B i).verts → v.1 ∉ (P i).verts) :
    (∀ i, (P i ⊔ inducedMatchingLift G X (B i)).IsMatching) ∧
      Pairwise (fun i j ↦ Disjoint (P i ⊔ inducedMatchingLift G X (B i)).spanningCoe
        (P j ⊔ inducedMatchingLift G X (B j)).spanningCoe) := by
  have hmix (i j : I) := inducedMatchingLift_disjoint_cross G X (P i) (hcross i) (B j)
  have hBd' : Pairwise (fun i j ↦
      Disjoint (inducedMatchingLift G X (B i)).spanningCoe
        (inducedMatchingLift G X (B j)).spanningCoe) := by
    intro i j hij
    exact subgraph_map_spanning_disjoint (_root_.SimpleGraph.Embedding.induce Xᶜ).toHom
      Subtype.val_injective _ _ (hBd hij)
  refine ⟨?_, ?_⟩
  · intro i
    apply (hP i).sup
      ((hB i).map (_root_.SimpleGraph.Embedding.induce Xᶜ).toHom Subtype.val_injective)
    apply Set.disjoint_left.mpr
    intro v hp hb
    obtain ⟨hv, hb⟩ := (inducedMatchingLift_mem G X (B i) v).mp
      ((inducedMatchingLift G X (B i)).support_subset_verts hb)
    exact havoid i ⟨v, hv⟩ hb ((P i).support_subset_verts hp)
  · intro i j hij
    apply _root_.SimpleGraph.disjoint_left.mpr
    intro x y hi hj
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact _root_.SimpleGraph.disjoint_left.mp (hPd hij) x y hi hj
    · exact _root_.SimpleGraph.disjoint_left.mp (hmix i j) x y hi hj
    · exact _root_.SimpleGraph.disjoint_left.mp (hmix j i) x y hj hi
    · exact _root_.SimpleGraph.disjoint_left.mp (hBd' hij) x y hi hj

theorem merge_induced_mem_of_outlier (P : G.Subgraph)
    (B : (G.induce Xᶜ).Subgraph) {v : V} (hv : v ∈ X) :
    v ∈ (P ⊔ inducedMatchingLift G X B).verts ↔ v ∈ P.verts := by
  change v ∈ P.verts ∨ v ∈ (inducedMatchingLift G X B).verts ↔ _
  constructor
  · rintro (hp | hb)
    · exact hp
    · obtain ⟨hn, _⟩ := (inducedMatchingLift_mem G X B v).mp hb
      exact (hn hv).elim
  · exact Or.inl

theorem merge_induced_mem_of_not_outlier (P : G.Subgraph)
    (B : (G.induce Xᶜ).Subgraph) {v : V} (hv : v ∉ X) :
    v ∈ (P ⊔ inducedMatchingLift G X B).verts ↔
      v ∈ P.verts ∨ (⟨v, hv⟩ : ↥(Xᶜ)) ∈ B.verts := by
  change v ∈ P.verts ∨ v ∈ (inducedMatchingLift G X B).verts ↔ _
  rw [inducedMatchingLift_mem]
  constructor
  · rintro (hp | ⟨_, hb⟩)
    · exact Or.inl hp
    · exact Or.inr hb
  · rintro (hp | hb)
    · exact Or.inl hp
    · exact Or.inr ⟨hv, hb⟩

#print axioms merge_induced_matching_families

end Erdos19
