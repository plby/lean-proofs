import ErdosProblems.Erdos556.FourCorePatternTwo
import ErdosProblems.Erdos556.MixedFourCoreCycle

/-! The first four-core finisher after deleting the green diagonal covers. -/

namespace Erdos556

open SimpleGraph Finset

structure FourCorePatternOne {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (A : Fin 4 → Finset V) (d : ℕ) : Prop where
  disjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  red02 : BipartiteDefect (c.graph 0) (A 0) (A 2) d
  red13 : BipartiteDefect (c.graph 0) (A 1) (A 3) d
  blue01 : BipartiteDefect (c.graph 1) (A 0) (A 1) d
  blue23 : BipartiteDefect (c.graph 1) (A 2) (A 3) d

structure FourCorePatternOneClean {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (A : Fin 4 → Finset V) (d : ℕ) : Prop
    extends FourCorePatternOne c A d where
  noGreen03 : ∀ a ∈ A 0, ∀ b ∈ A 3, ¬ (c.graph 2).Adj a b
  noGreen12 : ∀ a ∈ A 1, ∀ b ∈ A 2, ¬ (c.graph 2).Adj a b

theorem FourCorePatternOne.core_cliques {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {A : Fin 4 → Finset V} {d : ℕ}
    (h : FourCorePatternOne c A d) (r : ℕ) (hr : 2 ≤ r)
    (hsize : ∀ i, r + 2 * d + 1 ≤ (A i).card)
    (hno : ∀ k, ¬ cycleGraph (2 * r + 1) ⊑ c.graph k) :
    ∀ i, (c.graph 2).IsClique (A i : Set V) := by
  have hside (i j : Fin 4) (k : Fin 3) (hij : i ≠ j)
      (hd : BipartiteDefect (c.graph k) (A i) (A j) d) :
      ∀ u ∈ A i, ∀ v ∈ A i, ¬ (c.graph k).Adj u v :=
    no_side_edges_of_forbidden_odd_cycle (c.graph k) (A i) (A j) r d (by omega)
      (h.disjoint i j hij) hd (hsize i) (by have hj := hsize j; omega) (hno k)
  intro i
  apply c.isClique_of_excluded_colours (A i) 0 1 2 fin_three_cases
  · fin_cases i
    · exact hside 0 2 0 (by decide) h.red02
    · exact hside 1 3 0 (by decide) h.red13
    · exact hside 2 0 0 (by decide) h.red02.symm
    · exact hside 3 1 0 (by decide) h.red13.symm
  · fin_cases i
    · exact hside 0 1 1 (by decide) h.blue01
    · exact hside 1 0 1 (by decide) h.blue01.symm
    · exact hside 2 3 1 (by decide) h.blue23
    · exact hside 3 2 1 (by decide) h.blue23.symm

theorem patternOne_colour_cases : ∀ k : Fin 4 → Fin 3, (∀ i, k i ≠ 2) →
    (k 0 = 0 ∧ k 2 = 0) ∨ (k 1 = 0 ∧ k 3 = 0) ∨
    (k 0 = 1 ∧ k 1 = 1) ∨ (k 2 = 1 ∧ k 3 = 1) ∨
    (k 0 = 0 ∧ k 1 = 1 ∧ k 2 = 1 ∧ k 3 = 0) ∨
    (k 0 = 1 ∧ k 1 = 0 ∧ k 2 = 0 ∧ k 3 = 1) := by decide

def fourCorePairFlip (i : Fin 4) : Fin 4 := ![1, 0, 3, 2] i

theorem fourCorePairFlip_injective : Function.Injective fourCorePairFlip := by decide

theorem FourCorePatternOneClean.outside_complete_to_core {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {A : Fin 4 → Finset V} {d : ℕ}
    (h : FourCorePatternOneClean c A d) (r : ℕ) (hr : 4 ≤ r)
    (hsize : ∀ i, r + 2 * d + 1 ≤ (A i).card)
    (hno : ∀ k, ¬ cycleGraph (2 * r + 1) ⊑ c.graph k)
    (x : V) (hx : ∀ i, x ∉ A i) : ∃ i, ∀ a ∈ A i, (c.graph 2).Adj x a := by
  classical
  by_contra hn
  push Not at hn
  choose u hu hbad using hn
  have hne (i : Fin 4) : x ≠ u i := by intro he; exact hx i (he.symm ▸ hu i)
  have hcolour (i : Fin 4) : c.colour x (u i) ≠ 2 := fun he => hbad i ⟨hne i, he⟩
  have havoid (i j : Fin 4) (k : Fin 3) (hij : i ≠ j)
      (hd : BipartiteDefect (c.graph k) (A i) (A j) d) :
      ¬ (c.colour x (u i) = k ∧ c.colour x (u j) = k) := by
    intro he
    apply outside_vertex_not_adjacent_to_both_sides (c.graph k) (A i) (A j) r d (by omega)
      (h.disjoint i j hij) hd (by have hi := hsize i; omega) (by have hj := hsize j; omega)
      (hno k) x (hx i) (hx j) (u i) (u j) (hu i) (hu j)
    exact ⟨⟨hne i, he.1⟩, ⟨hne j, he.2⟩⟩
  rcases patternOne_colour_cases (fun i => c.colour x (u i)) hcolour with
    he | he | he | he | he | he
  · exact havoid 0 2 0 (by decide) h.red02 he
  · exact havoid 1 3 0 (by decide) h.red13 he
  · exact havoid 0 1 1 (by decide) h.blue01 he
  · exact havoid 2 3 1 (by decide) h.blue23 he
  · have hout := monochromatic_cycle_of_mixed_four_core_neighbors c A r d hr h.disjoint hsize
      h.red02 h.red13 h.noGreen12 x hx u hu
      ⟨hne 0, he.1⟩ ⟨hne 3, he.2.2.2⟩ ⟨hne 1, he.2.1⟩ ⟨hne 2, he.2.2.1⟩
    exact hout.elim (hno 0) (hno 1)
  · let A' := fun i => A (fourCorePairFlip i)
    let u' := fun i => u (fourCorePairFlip i)
    have hdis' : ∀ i j, i ≠ j → Disjoint (A' i) (A' j) :=
      fun i j hij => h.disjoint _ _ (fourCorePairFlip_injective.ne hij)
    have hout := monochromatic_cycle_of_mixed_four_core_neighbors c A' r d hr hdis'
      (fun i => hsize (fourCorePairFlip i)) h.red13 h.red02 h.noGreen03
      x (fun i => hx (fourCorePairFlip i)) u' (fun i => hu (fourCorePairFlip i))
      ⟨hne 1, he.2.1⟩ ⟨hne 2, he.2.2.1⟩ ⟨hne 0, he.1⟩ ⟨hne 3, he.2.2.2⟩
    exact hout.elim (hno 0) (hno 1)

theorem monochromatic_cycle_of_clean_four_core_pattern_one {V : Type*} [Fintype V] [DecidableEq V]
    (c : ThreeColouring V) (A : Fin 4 → Finset V) (r d : ℕ) (hr : 4 ≤ r)
    (hN : 8 * r < Fintype.card V) (h : FourCorePatternOneClean c A d)
    (hsize : ∀ i, r + 2 * d + 1 ≤ (A i).card) : ∃ k, cycleGraph (2 * r + 1) ⊑ c.graph k := by
  classical
  by_contra hn
  have hno : ∀ k, ¬ cycleGraph (2 * r + 1) ⊑ c.graph k := fun k hk => hn ⟨k, hk⟩
  have hclique := h.toFourCorePatternOne.core_cliques r (by omega) hsize hno
  have hcover : ∀ x : V, ∃ i, x ∈ A i ∨ ∀ a ∈ A i, (c.graph 2).Adj x a := by
    intro x
    by_cases hex : ∃ i, x ∈ A i
    · obtain ⟨i, hi⟩ := hex
      exact ⟨i, Or.inl hi⟩
    · have hx : ∀ i, x ∉ A i := fun i hi => hex ⟨i, hi⟩
      obtain ⟨i, hi⟩ := h.outside_complete_to_core r hr hsize hno x hx
      exact ⟨i, Or.inr hi⟩
  have hbound := clique_core_capacity_bound (fun _ : Fin 4 => c.graph 2) A r
    (by omega) (fun i => by have hi := hsize i; omega) hclique (fun _ => hno 2) hcover
  simp only [Fintype.card_fin] at hbound
  omega

#print axioms monochromatic_cycle_of_clean_four_core_pattern_one

end Erdos556
