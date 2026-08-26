import ErdosProblems.Erdos556.JoinedCorePaths
import ErdosProblems.Erdos556.BipartiteOddCycle

/-! Size and clique consequences with the exact half-cycle boundary retained. -/

namespace Erdos556

open SimpleGraph Finset

theorem exists_odd_cycle_in_large_joined_bucket {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A S : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hAS : A ⊆ S) (hA : r + 1 ≤ A.card) (hS : 2 * r + 1 ≤ S.card)
    (hjoin : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = 2 * r + 1 := by
  classical
  obtain ⟨C, hCA, hCc⟩ := exists_subset_card_eq hA
  have hCS : C ⊆ S := hCA.trans hAS
  have hdiff : r ≤ (S \ C).card := by
    rw [card_sdiff, inter_eq_left.mpr hCS, hCc]
    omega
  obtain ⟨W, hWS, hWc⟩ := exists_subset_card_eq hdiff
  have hCW : Disjoint C W := by
    apply Finset.disjoint_left.mpr
    intro x hx hxW
    exact (mem_sdiff.mp (hWS hxW)).2 hx
  have hcross : ∀ a ∈ C, ∀ w ∈ W, G.Adj a w := by
    intro a ha w hw
    have hwS := (mem_sdiff.mp (hWS hw)).1
    have haw : a ≠ w := fun h => (Finset.disjoint_left.mp hCW ha) (h ▸ hw)
    exact hjoin a (hCA ha) w hwS haw
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (show 1 < C.card by omega)
  exact exists_odd_cycle_of_bipartite_side_edge G C W r hr hCW (by omega) (by omega)
    hcross u v hu hv (hjoin u (hCA hu) v (hCS hv) huv)

theorem complement_clique_outside_small_joined_core {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A S : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hA : r ≤ A.card) (hX : r + 1 ≤ (S \ A).card)
    (hjoin : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G) : Gᶜ.IsClique ((S \ A : Finset V) : Set V) := by
  classical
  have hdis : Disjoint (S \ A) A := Finset.disjoint_left.mpr fun _ hx => (mem_sdiff.mp hx).2
  have hcross : ∀ x ∈ S \ A, ∀ a ∈ A, G.Adj x a := by
    intro x hx a ha
    exact (hjoin a ha x (mem_sdiff.mp hx).1 (fun h => (mem_sdiff.mp hx).2 (h ▸ ha))).symm
  intro u hu v hv huv
  rw [compl_adj]
  refine ⟨huv, ?_⟩
  intro hadj
  exact hno ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr
    (exists_odd_cycle_of_bipartite_side_edge G (S \ A) A r hr hdis hX hA hcross u v hu hv hadj))

theorem joined_bucket_isClique_of_one_outside {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A S : Finset V) (hAS : A ⊆ S) (hsize : S.card ≤ A.card + 1)
    (hjoin : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s) : G.IsClique (S : Set V) := by
  have hdiff : (S \ A).card ≤ 1 := by rw [card_sdiff, inter_eq_left.mpr hAS]; omega
  intro u hu v hv huv
  by_cases huA : u ∈ A
  · exact hjoin u huA v hv huv
  by_cases hvA : v ∈ A
  · exact (hjoin v hvA u hu huv.symm).symm
  exact (huv (card_le_one.mp hdiff u (mem_sdiff.mpr ⟨hu, huA⟩) v (mem_sdiff.mpr ⟨hv, hvA⟩))).elim

theorem isClique_of_complete_complement_cross {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S T : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hdis : Disjoint S T) (hS : r + 1 ≤ S.card) (hT : r ≤ T.card)
    (hcross : ∀ s ∈ S, ∀ t ∈ T, Gᶜ.Adj s t)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜ) : G.IsClique (S : Set V) := by
  classical
  intro u hu v hv huv
  by_contra hadj
  have hblue : Gᶜ.Adj u v := by rw [compl_adj]; exact ⟨huv, hadj⟩
  exact hno ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr
    (exists_odd_cycle_of_bipartite_side_edge Gᶜ S T r hr hdis hS hT hcross u v hu hv hblue))

#print axioms exists_odd_cycle_in_large_joined_bucket
#print axioms complement_clique_outside_small_joined_core

end Erdos556
