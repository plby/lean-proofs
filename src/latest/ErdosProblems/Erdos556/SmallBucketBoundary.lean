import ErdosProblems.Erdos556.JoinedBucketBounds

/-!
# The smallest bucket after deleting a cross-edge cover

This handles the case where a core initially has exactly `(n-1)/2`
vertices. A second large clique in the opposite colour supplies the
contradiction; no incorrect insertion bound at equality is used.
-/

namespace Erdos556

open SimpleGraph Finset

theorem not_large_joined_bucket_with_opposite_set {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A S T : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hAS : A ⊆ S) (hA : r ≤ A.card) (hS : 2 * r + 2 ≤ S.card) (hT : r - 1 ≤ T.card)
    (hdis : Disjoint S T) (hcross : ∀ s ∈ S, ∀ t ∈ T, Gᶜ.Adj s t)
    (hjoin : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜ) : False := by
  classical
  by_cases hlargeA : r + 1 ≤ A.card
  · exact hno ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr
      (exists_odd_cycle_in_large_joined_bucket G A S r hr hAS hlargeA (by omega) hjoin))
  have hAc : A.card = r := by omega
  let X := S \ A
  have hX : r + 2 ≤ X.card := by
    dsimp only [X]
    rw [card_sdiff, inter_eq_left.mpr hAS, hAc]
    omega
  have hclique : Gᶜ.IsClique (X : Set V) :=
    complement_clique_outside_small_joined_core G A S r hr hA
      (show r + 1 ≤ X.card by omega) hjoin hno
  have hXT : Disjoint X T := hdis.mono_left sdiff_subset
  have hU : 2 * r + 1 ≤ (X ∪ T).card := by
    rw [card_union_of_disjoint hXT]
    omega
  have hbluejoin : ∀ x ∈ X, ∀ y ∈ X ∪ T, x ≠ y → Gᶜ.Adj x y := by
    intro x hx y hy hxy
    rcases mem_union.mp hy with hy | hy
    · exact hclique hx hy hxy
    · exact hcross x (mem_sdiff.mp hx).1 y hy
  exact hnoc ((cycleGraph_isContained_iff (by omega : 2 < 2 * r + 1)).mpr
    (exists_odd_cycle_in_large_joined_bucket Gᶜ X (X ∪ T) r hr subset_union_left
      (by omega) hU hbluejoin))

theorem bucket_card_after_single_deletion {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A S T Z : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hAS : A ⊆ S) (hA : r ≤ A.card) (hT : r ≤ T.card)
    (hjoin : ∀ a ∈ A, ∀ s ∈ S, a ≠ s → G.Adj a s)
    (hdis : Disjoint S T) (hunion : S ∪ T = univ) (hN : 3 * r + 2 ≤ Fintype.card V)
    (hZ : Z.card ≤ 1) (hcross : ∀ s ∈ S \ Z, ∀ t ∈ T \ Z, Gᶜ.Adj s t)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜ) :
    r ≤ (T \ Z).card := by
  classical
  by_contra hsmall
  have hpart := card_sdiff_add_card_inter T Z
  have hinter : (T ∩ Z).card ≤ 1 := (card_le_card inter_subset_right).trans hZ
  have hTc : T.card = r := by omega
  have hlost : (T ∩ Z).Nonempty := card_pos.mp (by omega)
  obtain ⟨z, hz⟩ := hlost
  have hZT : Z ⊆ T := by
    intro x hx
    have he : x = z := card_le_one.mp hZ x hx z (mem_inter.mp hz).2
    exact he ▸ (mem_inter.mp hz).1
  have hSZ : Disjoint S Z := hdis.mono_right hZT
  have hdiff : S \ Z = S := by
    ext s
    constructor
    · exact fun h => (mem_sdiff.mp h).1
    · intro hs
      exact mem_sdiff.mpr ⟨hs, Finset.disjoint_left.mp hSZ hs⟩
  have hcard : S.card + T.card = Fintype.card V := by
    rw [← card_union_of_disjoint hdis, hunion, card_univ]
  have hSc : 2 * r + 2 ≤ S.card := by omega
  have hcross' : ∀ s ∈ S, ∀ t ∈ T \ Z, Gᶜ.Adj s t := by simpa only [hdiff] using hcross
  exact not_large_joined_bucket_with_opposite_set G A S (T \ Z) r hr hAS hA hSc (by omega)
    (hdis.mono_right sdiff_subset) hcross' hjoin hno hnoc

#print axioms bucket_card_after_single_deletion

end Erdos556
