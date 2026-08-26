import ErdosProblems.Erdos556.FourCorePatternOneClean
import ErdosProblems.Erdos556.CrossEdgeCover

/-! Deleting two diagonal covers completes the first exact four-core finisher. -/

namespace Erdos556

open SimpleGraph Finset

theorem FourCorePatternOne.exists_clean_cores {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {A : Fin 4 → Finset V} {d : ℕ}
    (h : FourCorePatternOne c A d) (r : ℕ) (hr : 4 ≤ r)
    (hsize : ∀ i, r + 2 * d + 3 ≤ (A i).card)
    (hno : ∀ k, ¬ cycleGraph (2 * r + 1) ⊑ c.graph k) :
    ∃ C : Fin 4 → Finset V, FourCorePatternOneClean c C d ∧
      ∀ i, r + 2 * d + 1 ≤ (C i).card := by
  classical
  have hclique := h.core_cliques r (by omega) (fun i => by have hi := hsize i; omega) hno
  have hmatch03 := two_clique_cross_edges_share_endpoint (c.graph 2) (A 0) (A 3)
    (h.disjoint 0 3 (by decide)) (hclique 0) (hclique 3) r (by omega)
    (by have hi := hsize 0; omega) (by have hi := hsize 3; omega) (hno 2)
  have hmatch12 := two_clique_cross_edges_share_endpoint (c.graph 2) (A 1) (A 2)
    (h.disjoint 1 2 (by decide)) (hclique 1) (hclique 2) r (by omega)
    (by have hi := hsize 1; omega) (by have hi := hsize 2; omega) (hno 2)
  obtain ⟨Z₁, hZ₁, hcover₁⟩ := exists_single_vertex_cross_cover (A 0) (A 3) (c.graph 2).Adj
    (fun a ha a' ha' b hb b' hb' hab hab' => hmatch03 a a' b b' ha ha' hb hb' hab hab')
  obtain ⟨Z₂, hZ₂, hcover₂⟩ := exists_single_vertex_cross_cover (A 1) (A 2) (c.graph 2).Adj
    (fun a ha a' ha' b hb b' hb' hab hab' => hmatch12 a a' b b' ha ha' hb hb' hab hab')
  let Z := Z₁ ∪ Z₂
  let C := fun i => A i \ Z
  have hZ : Z.card ≤ 2 := (card_union_le Z₁ Z₂).trans (by omega)
  have hsub (i : Fin 4) : C i ⊆ A i := sdiff_subset
  have hp : FourCorePatternOne c C d :=
    { disjoint := fun i j hij => (h.disjoint i j hij).mono (hsub i) (hsub j)
      red02 := h.red02.mono (hsub 0) (hsub 2)
      red13 := h.red13.mono (hsub 1) (hsub 3)
      blue01 := h.blue01.mono (hsub 0) (hsub 1)
      blue23 := h.blue23.mono (hsub 2) (hsub 3) }
  have hgreen03 : ∀ a ∈ C 0, ∀ b ∈ C 3, ¬ (c.graph 2).Adj a b := by
    intro a ha b hb hab
    rcases hcover₁ a (hsub 0 ha) b (hsub 3 hb) hab with h | h
    · exact (mem_sdiff.mp ha).2 (mem_union_left Z₂ h)
    · exact (mem_sdiff.mp hb).2 (mem_union_left Z₂ h)
  have hgreen12 : ∀ a ∈ C 1, ∀ b ∈ C 2, ¬ (c.graph 2).Adj a b := by
    intro a ha b hb hab
    rcases hcover₂ a (hsub 1 ha) b (hsub 2 hb) hab with h | h
    · exact (mem_sdiff.mp ha).2 (mem_union_right Z₁ h)
    · exact (mem_sdiff.mp hb).2 (mem_union_right Z₁ h)
  refine ⟨C, { toFourCorePatternOne := hp, noGreen03 := hgreen03, noGreen12 := hgreen12 }, ?_⟩
  intro i
  have hc := card_sdiff_add_card_inter (A i) Z
  have hi : ((A i) ∩ Z).card ≤ 2 := (card_le_card inter_subset_right).trans hZ
  have hs := hsize i
  change r + 2 * d + 1 ≤ (A i \ Z).card
  omega

theorem monochromatic_cycle_of_four_core_pattern_one {V : Type*} [Fintype V] [DecidableEq V]
    (c : ThreeColouring V) (A : Fin 4 → Finset V) (r d : ℕ) (hr : 4 ≤ r)
    (hN : 8 * r < Fintype.card V) (h : FourCorePatternOne c A d)
    (hsize : ∀ i, r + 2 * d + 3 ≤ (A i).card) : ∃ k, cycleGraph (2 * r + 1) ⊑ c.graph k := by
  classical
  by_contra hn
  have hno : ∀ k, ¬ cycleGraph (2 * r + 1) ⊑ c.graph k := fun k hk => hn ⟨k, hk⟩
  obtain ⟨C, hC, hCs⟩ := h.exists_clean_cores r hr hsize hno
  exact hn (monochromatic_cycle_of_clean_four_core_pattern_one c C r d hr hN hC hCs)

#print axioms monochromatic_cycle_of_four_core_pattern_one

end Erdos556
