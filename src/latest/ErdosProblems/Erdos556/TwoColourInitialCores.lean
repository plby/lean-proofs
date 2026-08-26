import ErdosProblems.Erdos556.TwoColourLongCycles
import ErdosProblems.Erdos556.OddPredecessorCycle
import ErdosProblems.Erdos556.ParityCliques
import ErdosProblems.Erdos556.TwoCliqueCycles
import ErdosProblems.Erdos556.CrossEdgeCover

/-! Initial clique cores for the two-colour structural reduction. -/

namespace Erdos556

open SimpleGraph Finset

def TwoCliqueCorePair {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ A B : Finset V, Disjoint A B ∧ r ≤ A.card ∧ r ≤ B.card ∧
    G.IsClique (A : Set V) ∧ G.IsClique (B : Set V) ∧
    ∀ a ∈ A, ∀ b ∈ B, Gᶜ.Adj a b

theorem two_clique_core_pair_of_even_cycle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (r t : ℕ) (hr : 3 ≤ r) (hrt : r + 1 ≤ t)
    (hc : cycleGraph (2 * t) ⊑ G)
    (hno : ¬ cycleGraph (2 * t - 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * t - 1) ⊑ Gᶜ)
    (hforbid : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜ) : TwoCliqueCorePair Gᶜ r := by
  classical
  obtain ⟨A, B, hdis, hAc, hBc, hA, hB⟩ := exists_two_parity_cliques G t (by omega) hc hno hnoc
  have hmatch := two_clique_cross_edges_share_endpoint Gᶜ A B hdis hA hB r hr
    (by omega) (by omega) hforbid
  obtain ⟨S, hS, hcover⟩ := exists_single_vertex_cross_cover A B Gᶜ.Adj
    (fun a ha a' ha' b hb b' hb' hab hab' => hmatch a a' b b' ha ha' hb hb' hab hab')
  have hsize (C : Finset V) (hC : r + 1 ≤ C.card) : r ≤ (C \ S).card := by
    have hcount := card_sdiff_add_card_inter C S
    have hinter : (C ∩ S).card ≤ S.card := card_le_card inter_subset_right
    omega
  refine ⟨A \ S, B \ S, hdis.mono sdiff_subset sdiff_subset,
    hsize A (by omega), hsize B (by omega), ?_, ?_, ?_⟩
  · intro a ha b hb hab
    exact hA (mem_sdiff.mp ha).1 (mem_sdiff.mp hb).1 hab
  · intro a ha b hb hab
    exact hB (mem_sdiff.mp ha).1 (mem_sdiff.mp hb).1 hab
  · exact complete_complement_cross_of_cover Gᶜ A B S hdis hcover

theorem two_clique_core_pair_of_long_cycle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 3 ≤ r)
    (hno : ¬ cycleGraph (2 * r + 1) ⊑ G) (hnoc : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜ)
    (hex : ∃ m, 2 * r + 1 ≤ m ∧ (cycleGraph m ⊑ G ∨ cycleGraph m ⊑ Gᶜ)) :
    TwoCliqueCorePair G r ∨ TwoCliqueCorePair Gᶜ r := by
  obtain ⟨m, hmr, hmEven, hcycle, hpred, hpredc⟩ :=
    exists_minimal_even_monochromatic_cycle G (2 * r + 1) (by omega) hno hnoc hex
  obtain ⟨t, ht⟩ := hmEven
  have hmt : m = 2 * t := by omega
  rw [hmt] at hcycle hpred hpredc hmr
  rcases hcycle with hc | hc
  · exact Or.inr (two_clique_core_pair_of_even_cycle G r t hr (by omega) hc hpred hpredc hnoc)
  · left
    have hpredcc : ¬ cycleGraph (2 * t - 1) ⊑ Gᶜᶜ := by simpa only [compl_compl] using hpred
    have hnocc : ¬ cycleGraph (2 * r + 1) ⊑ Gᶜᶜ := by simpa only [compl_compl] using hno
    simpa only [compl_compl] using
      two_clique_core_pair_of_even_cycle Gᶜ r t hr (by omega) hc hpredc hpredcc hnocc

theorem exists_uniform_two_colour_initial_cores :
    ∃ N₀ : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ),
      N₀ ≤ r → 4 * (r + 1) - (r + 1) / 100000 ≤ Fintype.card V →
      (¬ cycleGraph (2 * r + 1) ⊑ G) → (¬ cycleGraph (2 * r + 1) ⊑ Gᶜ) →
      TwoCliqueCorePair G r ∨ TwoCliqueCorePair Gᶜ r := by
  obtain ⟨N₁, hN₁⟩ := exists_uniform_two_colour_long_cycle
  refine ⟨max N₁ 3, ?_⟩
  intro V _ _ G _ r hr hN hno hnoc
  apply two_clique_core_pair_of_long_cycle G r (by omega) hno hnoc
  rcases hN₁ G (r + 1) (by omega) hN with ⟨v, c, hc, hlen⟩ | ⟨v, c, hc, hlen⟩
  · refine ⟨c.length, by omega, Or.inl ?_⟩
    exact (cycleGraph_isContained_iff (by omega : 2 < c.length)).mpr ⟨v, c, hc, rfl⟩
  · refine ⟨c.length, by omega, Or.inr ?_⟩
    exact (cycleGraph_isContained_iff (by omega : 2 < c.length)).mpr ⟨v, c, hc, rfl⟩

#print axioms exists_uniform_two_colour_initial_cores

end Erdos556
