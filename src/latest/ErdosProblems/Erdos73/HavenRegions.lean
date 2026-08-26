import ErdosProblems.Erdos73.HavenSeparation

/-! Canonical region separations and oddness of the normalized Reed haven. -/

namespace Erdos73.BrambleHaven
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {β : Finset (Finset V)} {q : ℕ}

theorem pointsTo_region_separation (h : BrambleHaven G β q)
    (K : {X : Finset V // X.card < q}) :
    h.PointsTo (Finset.univ \ h.region K)
      (h.region K ∪ externalNeighborhood G (h.region K)) := by
  have hcard : (externalNeighborhood G (h.region K)).card < q :=
    (Finset.card_le_card (h.boundary K)).trans_lt K.property
  have hsmall : ((Finset.univ \ h.region K) ∩
      (h.region K ∪ externalNeighborhood G (h.region K))).card < q := by
    rwa [inter_externalNeighborhood]
  apply h.pointsTo_of_touches_right (separation_externalNeighborhood G (h.region K)) hsmall
    (T := h.region K)
  · rw [rightDiff_externalNeighborhood]
  · exact h.touches _ K

theorem controlled_connected_subset_region (h : BrambleHaven G β q)
    (K : {X : Finset V // X.card < q}) {g : ℕ} (hKg : K.val.card < g)
    (T : Finset V) (hT : (G.induce (T : Set V)).Connected) (hTK : Disjoint T K.val)
    (hcontrol : ∀ C D : Finset V, IsVertexSeparation G C D → (C ∩ D).card < g →
      h.PointsTo C D → ¬ T ⊆ C) : T ⊆ h.region K := by
  have hsep := separation_externalNeighborhood G (h.region K)
  have hcut : Disjoint T ((Finset.univ \ h.region K) ∩
      (h.region K ∪ externalNeighborhood G (h.region K))) := by
    rw [inter_externalNeighborhood]
    exact hTK.mono_right (h.boundary K)
  rcases connected_finset_subset_side_of_disjoint_separator hsep hT hcut with hleft | hright
  · have hsmall : ((Finset.univ \ h.region K) ∩
        (h.region K ∪ externalNeighborhood G (h.region K))).card < g := by
      rw [inter_externalNeighborhood]
      exact (Finset.card_le_card (h.boundary K)).trans_lt hKg
    exact (hcontrol _ _ hsep hsmall (h.pointsTo_region_separation K)
      (hleft.trans Finset.sdiff_subset)).elim
  · simpa only [rightDiff_externalNeighborhood] using hright

theorem odd_region_of_lowOrderOddSides {ell : ℕ}
    (h : BrambleHaven G (lowOrderOddSides G ell) q)
    (K : {X : Finset V // X.card < q}) :
    ¬ (G.induce (h.region K : Set V)).IsBipartite := by
  obtain ⟨T, hT, hTR⟩ := h.contains K
  have hTodd := ((mem_lowOrderOddSides G ell T).mp hT).2.1
  intro hbip
  have hTbip : (G.induce (T : Set V)).IsBipartite :=
    Colorable.of_hom (G.induceHomOfLE (show (T : Set V) ⊆ (h.region K : Set V) from hTR)).toHom hbip
  exact ((isBipartite_iff_no_oddCycleSubgraph _).mp hTbip) hTodd

end
end Erdos73.BrambleHaven
