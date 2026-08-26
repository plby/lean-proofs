import ErdosProblems.Erdos556.JoinedCorePaths
import ErdosProblems.Erdos556.TwoCliqueCycles
import ErdosProblems.Erdos556.CrossEdgeCover

/-! Cross edges between joined-core buckets form a star, without a prior bucket-size bound. -/

namespace Erdos556

open SimpleGraph Finset

theorem joined_bucket_cross_edges_share_endpoint_of_large_left {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A B S T : Finset V) (r : ℕ) (hr : 4 ≤ r)
    (hAS : A ⊆ S) (hBT : B ⊆ T) (hA : r ≤ A.card) (hB : r ≤ B.card)
    (hjoinA : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s)
    (hjoinB : ∀ b ∈ B, ∀ t ∈ T, b ≠ t → G.Adj b t)
    (hdis : Disjoint S T) (hS : r + 1 ≤ S.card)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G)
    (a a' b b' : V) (ha : a ∈ S) (ha' : a' ∈ S) (hb : b ∈ T) (hb' : b' ∈ T)
    (hab : G.Adj a b) (hab' : G.Adj a' b') : a = a' ∨ b = b' := by
  classical
  by_contra! hne
  obtain ⟨p, hp, hplen, hpS⟩ := exists_path_in_joined_core_bucket G A S hAS hjoinA
    r (by omega) hA hS a a' ha ha' hne.1
  have hT : r ≤ T.card := hB.trans (card_le_card hBT)
  obtain ⟨q, hq, hqlen, hqT⟩ := exists_path_in_joined_core_bucket G B T hBT hjoinB
    (r - 1) (by omega) (by omega) (by omega) b' b hb' hb hne.2.symm
  obtain ⟨v, c, hc, hlen⟩ := exists_cycle_of_paths_and_cross_edges S T hdis hb' p q hp hq
    (by omega) hpS hqT hab hab'
  exact hno ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr ⟨v, c, hc, by omega⟩)

theorem exists_single_vertex_bucket_cross_cover {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B S T : Finset V) (r : ℕ) (hr : 4 ≤ r)
    (hAS : A ⊆ S) (hBT : B ⊆ T) (hA : r ≤ A.card) (hB : r ≤ B.card)
    (hjoinA : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s)
    (hjoinB : ∀ b ∈ B, ∀ t ∈ T, b ≠ t → G.Adj b t)
    (hdis : Disjoint S T) (hunion : S ∪ T = univ) (hN : 2 * r < Fintype.card V)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G) :
    ∃ Z : Finset V, Z.card ≤ 1 ∧ ∀ s ∈ S, ∀ t ∈ T, G.Adj s t → s ∈ Z ∨ t ∈ Z := by
  have hcard : S.card + T.card = Fintype.card V := by
    rw [← card_union_of_disjoint hdis, hunion, card_univ]
  apply exists_single_vertex_cross_cover S T G.Adj
  intro a ha a' ha' b hb b' hb' hab hab'
  by_cases hS : r + 1 ≤ S.card
  · exact joined_bucket_cross_edges_share_endpoint_of_large_left G A B S T r hr
      hAS hBT hA hB hjoinA hjoinB hdis hS hno a a' b b' ha ha' hb hb' hab hab'
  · have hT : r + 1 ≤ T.card := by omega
    have h := joined_bucket_cross_edges_share_endpoint_of_large_left G B A T S r hr
      hBT hAS hB hA hjoinB hjoinA hdis.symm hT hno b b' a a' hb hb' ha ha' hab.symm hab'.symm
    exact h.symm

#print axioms exists_single_vertex_bucket_cross_cover

end Erdos556
