import ErdosProblems.Erdos577.WeightedTwelveLabels

/-! The swapped objects again have pattern12 and occur in an actual strong feasible chain. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exposed_pattern {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) :
    WeightedPawBlock.Pattern12 (exposedPaw p q hd h) (exposedQuad p q hd h) := by
  have hcenter := (degreeIn_eq_zero_iff (G := G) p.center q.support).mp
    (center_zero hc hcard hn p hp hs q hq h)
  have hnleaf := c.paw_nonadjacent hcard hn p hp
  have hXY : ¬G.Adj p.leaf (q 3) := fun hh ↦
    (by decide : ¬(7 : ℕ).testBit 3 = true) ((h.2.1 3).mp hh)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [exposedQuad_apply, exposedQuad_apply]
    exact ((first_rows p q h).1 1 (by decide)).symm
  · change ∀ i : Fin 4, G.Adj (q 3) (exposedQuad p q hd h i) ↔ (7 : ℕ).testBit i.val = true
    intro i
    rw [exposedQuad_apply]
    fin_cases i
    · exact ⟨fun _ ↦ by decide, fun _ ↦ q.adjacent 3⟩
    · exact ⟨fun _ ↦ by decide, fun _ ↦ h.1.symm⟩
    · exact ⟨fun _ ↦ by decide, fun _ ↦ (q.adjacent 2).symm⟩
    · exact iff_of_false (fun hh ↦ hXY hh.symm) (by decide)
  · change ∀ i : Fin 4, G.Adj (p.vertices 2) (exposedQuad p q hd h i) ↔
      (7 : ℕ).testBit i.val = true
    intro i
    by_cases hi : i = 3
    · subst i
      rw [exposedQuad_apply]
      exact iff_of_false (fun hh ↦ hnleaf.1 hh.symm) (by decide)
    · rw [exposedQuad_apply, if_neg hi]
      exact h.2.2.1 i
  · change ∀ i : Fin 4, G.Adj p.center (exposedQuad p q hd h i) ↔ (8 : ℕ).testBit i.val = true
    intro i
    by_cases hi : i = 3
    · subst i
      rw [exposedQuad_apply]
      exact ⟨fun _ ↦ by decide, fun _ ↦ p.pendant.symm⟩
    · rw [exposedQuad_apply, if_neg hi]
      have hbits : ∀ i : Fin 4, i ≠ 3 → ¬(8 : ℕ).testBit i.val = true := by decide +kernel
      exact iff_of_false (hcenter (q i) ((q.mem_support _).mpr ⟨i, rfl⟩)) (hbits i hi)

theorem exists_swap {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (hd : Disjoint p.support q.support)
    (h : WeightedPawBlock.Pattern12 p q) :
    ∃ e : TriangleChain G, e.Strong ∧ e.terminal = q 3 ∧ e.triangle = p.triangle ∧
      (exposedPaw p q hd h).support = e.remainder ∧ (exposedQuad p q hd h).support ∈ e.blocks ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore ∧
      e.blocks = c.blocks.erase s ∪ {(exposedQuad p q hd h).support} ∧
      WeightedPawBlock.Pattern12 (exposedPaw p q hd h) (exposedQuad p q hd h) ∧
      ∀ a ∈ c.blocks, a ≠ s → a ∈ e.blocks ∧ a ≠ (exposedQuad p q hd h).support := by
  obtain ⟨e, he, ht, hT, hscore, hcomplete, hblocks⟩ :=
    FullRow.exists_strong_first_swap hc hcard hn p.swapNoncentral
      (by rw [Paw.swapNoncentral_support, hp]) hs q hq
      (first_rows p q h).1 (first_rows p q h).2
  rw [Paw.swapNoncentral_triangle] at hT
  rw [Paw.swapNoncentral_leaf] at hblocks
  have hnew : (exposedQuad p q hd h).support = insert p.leaf (s.erase (q 3)) := by
    rw [exposedQuad_support, hq]
  have hblocks' : e.blocks = c.blocks.erase s ∪ {(exposedQuad p q hd h).support} := by
    rwa [hnew]
  have hp' : (exposedPaw p q hd h).support = e.remainder := by
    rw [exposedPaw_support]
    change insert (q 3) p.triangle = insert e.terminal e.triangle
    rw [ht, hT]
  refine ⟨e, he, ht, hT, hp', ?_, hscore, hcomplete, hblocks',
    exposed_pattern hc hcard hn p hp hs q hq hd h, ?_⟩
  · rw [hblocks']
    exact mem_union_right _ (mem_singleton_self _)
  · intro a ha has
    refine ⟨?_, ?_⟩
    · rw [hblocks']
      exact mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)
    · intro heq
      have hx : p.leaf ∈ a := by rw [heq, hnew]; exact mem_insert_self _ _
      exact (c.presentPaw p hp).terminal_not_mem_block ha hx

end Erdos577.WeightedTwelve
