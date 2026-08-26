import ErdosProblems.Erdos556.ThreeColourTools
import ErdosProblems.Erdos556.DenseBipartiteOddCycle
import ErdosProblems.Erdos556.CliqueCoreCapacity

/-!
# The four-core finisher for two pairs in different colours

All edges between the pairs `01` and `23` are nearly colour zero;
the pair `01` is nearly colour one and `23` nearly colour two.
The missing-neighbour budget is explicit.
-/

namespace Erdos556

open SimpleGraph Finset

structure FourCorePatternTwo {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (A : Fin 4 → Finset V) (d : ℕ) : Prop where
  disjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  red02 : BipartiteDefect (c.graph 0) (A 0) (A 2) d
  red03 : BipartiteDefect (c.graph 0) (A 0) (A 3) d
  red12 : BipartiteDefect (c.graph 0) (A 1) (A 2) d
  red13 : BipartiteDefect (c.graph 0) (A 1) (A 3) d
  blue01 : BipartiteDefect (c.graph 1) (A 0) (A 1) d
  green23 : BipartiteDefect (c.graph 2) (A 2) (A 3) d

def patternTwoCoreColour (i : Fin 4) : Fin 3 := if i.val < 2 then 2 else 1

theorem patternTwo_colour_conflict : ∀ k : Fin 4 → Fin 3,
    k 0 ≠ 2 → k 1 ≠ 2 → k 2 ≠ 1 → k 3 ≠ 1 →
    (k 0 = 0 ∧ k 2 = 0) ∨ (k 0 = 0 ∧ k 3 = 0) ∨
    (k 1 = 0 ∧ k 2 = 0) ∨ (k 1 = 0 ∧ k 3 = 0) ∨
    (k 0 = 1 ∧ k 1 = 1) ∨ (k 2 = 2 ∧ k 3 = 2) := by decide

theorem FourCorePatternTwo.core_cliques {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {A : Fin 4 → Finset V} {d : ℕ}
    (h : FourCorePatternTwo c A d) (r : ℕ) (hr : 2 ≤ r)
    (hsize : ∀ i, r + 2 * d + 1 ≤ (A i).card)
    (hno : ∀ k, ¬ cycleGraph (2 * r + 1) ⊑ c.graph k) :
    ∀ i, (c.graph (patternTwoCoreColour i)).IsClique (A i : Set V) := by
  have hside (i j : Fin 4) (k : Fin 3) (hij : i ≠ j)
      (hd : BipartiteDefect (c.graph k) (A i) (A j) d) :
      ∀ u ∈ A i, ∀ v ∈ A i, ¬ (c.graph k).Adj u v :=
    no_side_edges_of_forbidden_odd_cycle (c.graph k) (A i) (A j) r d (by omega)
      (h.disjoint i j hij) hd (hsize i) (by have hj := hsize j; omega) (hno k)
  intro i
  fin_cases i
  · apply c.isClique_of_excluded_colours (A 0) 0 1 2 fin_three_cases
    · exact hside 0 2 0 (by decide) h.red02
    · exact hside 0 1 1 (by decide) h.blue01
  · apply c.isClique_of_excluded_colours (A 1) 0 1 2 fin_three_cases
    · exact hside 1 2 0 (by decide) h.red12
    · exact hside 1 0 1 (by decide) h.blue01.symm
  · apply c.isClique_of_excluded_colours (A 2) 0 2 1 (fun k => by have hk := fin_three_cases k; tauto)
    · exact hside 2 0 0 (by decide) h.red02.symm
    · exact hside 2 3 2 (by decide) h.green23
  · apply c.isClique_of_excluded_colours (A 3) 0 2 1 (fun k => by have hk := fin_three_cases k; tauto)
    · exact hside 3 0 0 (by decide) h.red03.symm
    · exact hside 3 2 2 (by decide) h.green23.symm

theorem FourCorePatternTwo.outside_complete_to_core {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {A : Fin 4 → Finset V} {d : ℕ}
    (h : FourCorePatternTwo c A d) (r : ℕ) (hr : 2 ≤ r)
    (hsize : ∀ i, r + 2 * d + 1 ≤ (A i).card)
    (hno : ∀ k, ¬ cycleGraph (2 * r + 1) ⊑ c.graph k)
    (x : V) (hx : ∀ i, x ∉ A i) :
    ∃ i, ∀ a ∈ A i, (c.graph (patternTwoCoreColour i)).Adj x a := by
  classical
  by_contra hn
  push Not at hn
  choose u hu hbad using hn
  have hne (i : Fin 4) : x ≠ u i := by
    intro he
    exact hx i (he.symm ▸ hu i)
  have hcolour (i : Fin 4) : c.colour x (u i) ≠ patternTwoCoreColour i :=
    fun he => hbad i ⟨hne i, he⟩
  have havoid (i j : Fin 4) (k : Fin 3) (hij : i ≠ j)
      (hd : BipartiteDefect (c.graph k) (A i) (A j) d) :
      ¬ (c.colour x (u i) = k ∧ c.colour x (u j) = k) := by
    intro he
    apply outside_vertex_not_adjacent_to_both_sides (c.graph k) (A i) (A j) r d hr
      (h.disjoint i j hij) hd (by have hi := hsize i; omega) (by have hj := hsize j; omega)
      (hno k) x (hx i) (hx j) (u i) (u j) (hu i) (hu j)
    exact ⟨⟨hne i, he.1⟩, ⟨hne j, he.2⟩⟩
  have h0 : c.colour x (u 0) ≠ 2 := by simpa [patternTwoCoreColour] using hcolour 0
  have h1 : c.colour x (u 1) ≠ 2 := by simpa [patternTwoCoreColour] using hcolour 1
  have h2 : c.colour x (u 2) ≠ 1 := by simpa [patternTwoCoreColour] using hcolour 2
  have h3 : c.colour x (u 3) ≠ 1 := by simpa [patternTwoCoreColour] using hcolour 3
  rcases patternTwo_colour_conflict (fun i => c.colour x (u i)) h0 h1 h2 h3 with
    he | he | he | he | he | he
  · exact havoid 0 2 0 (by decide) h.red02 he
  · exact havoid 0 3 0 (by decide) h.red03 he
  · exact havoid 1 2 0 (by decide) h.red12 he
  · exact havoid 1 3 0 (by decide) h.red13 he
  · exact havoid 0 1 1 (by decide) h.blue01 he
  · exact havoid 2 3 2 (by decide) h.green23 he

theorem monochromatic_cycle_of_four_core_pattern_two {V : Type*} [Fintype V] [DecidableEq V]
    (c : ThreeColouring V) (A : Fin 4 → Finset V) (r d : ℕ) (hr : 2 ≤ r)
    (hN : 8 * r < Fintype.card V) (h : FourCorePatternTwo c A d)
    (hsize : ∀ i, r + 2 * d + 1 ≤ (A i).card) :
    ∃ k, cycleGraph (2 * r + 1) ⊑ c.graph k := by
  classical
  by_contra hn
  have hno : ∀ k, ¬ cycleGraph (2 * r + 1) ⊑ c.graph k := fun k hk => hn ⟨k, hk⟩
  have hclique := h.core_cliques r hr hsize hno
  have hcover : ∀ x : V, ∃ i, x ∈ A i ∨ ∀ a ∈ A i, (c.graph (patternTwoCoreColour i)).Adj x a := by
    intro x
    by_cases hex : ∃ i, x ∈ A i
    · obtain ⟨i, hi⟩ := hex
      exact ⟨i, Or.inl hi⟩
    · have hx : ∀ i, x ∉ A i := fun i hi => hex ⟨i, hi⟩
      obtain ⟨i, hi⟩ := h.outside_complete_to_core r hr hsize hno x hx
      exact ⟨i, Or.inr hi⟩
  have hbound := clique_core_capacity_bound (fun i => c.graph (patternTwoCoreColour i)) A r
    (by omega) (fun i => by have hi := hsize i; omega) hclique
    (fun i => hno (patternTwoCoreColour i)) hcover
  simp only [Fintype.card_fin] at hbound
  omega

#print axioms monochromatic_cycle_of_four_core_pattern_two

end Erdos556
