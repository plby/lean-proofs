import ErdosProblems.Erdos1105.Disintegration

namespace Erdos1105

open SimpleGraph Finset

lemma degreeWithin_univ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degreeWithin G univ v = G.degree v := by
  classical
  rw [← card_neighborFinset_eq_degree]
  apply congrArg Finset.card
  ext w
  simp only [degreeWithin, mem_filter, mem_univ, true_and, mem_neighborFinset]

lemma degreeWithin_erase_adj {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {T : Finset V} {v w : V} (hv : v ∈ T) (hvw : G.Adj w v) :
    degreeWithin G (T.erase v) w + 1 = degreeWithin G T w := by
  classical
  have heq : (T.erase v).filter (G.Adj w) = (T.filter (G.Adj w)).erase v := by
    ext z
    simp only [mem_filter, mem_erase]
    tauto
  have hmem : v ∈ T.filter (G.Adj w) := mem_filter.mpr ⟨hv, hvw⟩
  change ((T.erase v).filter (G.Adj w)).card + 1 = (T.filter (G.Adj w)).card
  rw [heq, card_erase_of_mem hmem]
  have := card_pos.mpr ⟨v, hmem⟩
  omega

/-- Equality in the disintegration count forces every vertex outside
the core to meet the minimum deletion degree. -/
theorem degreeWithin_ge_of_sharp_core_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (T : Finset V)
    (hsub : vertexCore G d ⊆ T)
    (hsharp : (E767EGApi.edgesInside G T).card = (E767EGApi.edgesInside G (vertexCore G d)).card +
      d * (T.card - (vertexCore G d).card))
    {v : V} (hv : v ∈ T) (hvcore : v ∉ vertexCore G d) : d ≤ degreeWithin G T v := by
  have hsub' : vertexCore G d ⊆ T.erase v := by
    intro w hw
    exact mem_erase.mpr ⟨fun h ↦ hvcore (h ▸ hw), hsub hw⟩
  have hb := edgesInside_le_core_add G d (T.erase v) hsub'
  have hcard := card_le_card hsub'
  have he := edgesInside_erase G hv
  rw [card_erase_of_mem hv] at hb hcard
  have hpos : 0 < T.card := card_pos.mpr ⟨v, hv⟩
  have hdiff : T.card - (vertexCore G d).card = T.card - 1 - (vertexCore G d).card + 1 := by omega
  rw [hdiff, Nat.mul_add, Nat.mul_one] at hsharp
  omega

theorem sharp_core_count_erase {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (T : Finset V)
    (hsub : vertexCore G d ⊆ T)
    (hsharp : (E767EGApi.edgesInside G T).card = (E767EGApi.edgesInside G (vertexCore G d)).card +
      d * (T.card - (vertexCore G d).card))
    {v : V} (hv : v ∈ T) (hvcore : v ∉ vertexCore G d) (hdeg : degreeWithin G T v = d) :
    (E767EGApi.edgesInside G (T.erase v)).card = (E767EGApi.edgesInside G (vertexCore G d)).card +
      d * ((T.erase v).card - (vertexCore G d).card) := by
  have hsub' : vertexCore G d ⊆ T.erase v := by
    intro w hw
    exact mem_erase.mpr ⟨fun h ↦ hvcore (h ▸ hw), hsub hw⟩
  have hcard := card_le_card hsub'
  have he := edgesInside_erase G hv
  rw [hdeg] at he
  rw [card_erase_of_mem hv] at hcard ⊢
  have hpos : 0 < T.card := card_pos.mpr ⟨v, hv⟩
  have hdiff : T.card - (vertexCore G d).card = T.card - 1 - (vertexCore G d).card + 1 := by omega
  rw [hdiff, Nat.mul_add, Nat.mul_one] at hsharp
  omega

theorem sharp_core_outside_independent {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (T : Finset V)
    (hsub : vertexCore G d ⊆ T)
    (hsharp : (E767EGApi.edgesInside G T).card = (E767EGApi.edgesInside G (vertexCore G d)).card +
      d * (T.card - (vertexCore G d).card))
    (hdeg : ∀ v ∈ T, v ∉ vertexCore G d → degreeWithin G T v = d) :
    ∀ v ∈ T, v ∉ vertexCore G d → ∀ w ∈ T, w ∉ vertexCore G d → ¬G.Adj v w := by
  intro v hv hvc w hw hwc hvw
  have hsub' : vertexCore G d ⊆ T.erase v := by
    intro z hz
    exact mem_erase.mpr ⟨fun h ↦ hvc (h ▸ hz), hsub hz⟩
  have hs := sharp_core_count_erase G d T hsub hsharp hv hvc (hdeg v hv hvc)
  have hw' : w ∈ T.erase v := mem_erase.mpr ⟨hvw.ne.symm, hw⟩
  have hlo := degreeWithin_ge_of_sharp_core_count G d (T.erase v) hsub' hs hw' hwc
  have he := degreeWithin_erase_adj G hv hvw.symm
  rw [hdeg w hw hwc] at he
  omega

lemma sharp_core_count_actual {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hsharp : G.edgeFinset.card = (vertexCore G d).card.choose 2 +
      d * (Fintype.card V - (vertexCore G d).card)) :
    (E767EGApi.edgesInside G univ).card = (E767EGApi.edgesInside G (vertexCore G d)).card +
      d * ((univ : Finset V).card - (vertexCore G d).card) := by
  have he := edgesInside_le_core_add G d univ (subset_univ _)
  have hcore := edgesInside_le_choose G (vertexCore G d)
  have heq : E767EGApi.edgesInside G univ = G.edgeFinset := by simp [E767EGApi.edgesInside]
  rw [heq, card_univ] at he ⊢
  omega

end Erdos1105

#print axioms Erdos1105.sharp_core_outside_independent
