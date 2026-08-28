import ErdosProblems.Erdos577.OutsideSelectedPairs

/-! Two three-sets with inside sum at most22 force a13-contact block outside one selected block. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma exists_paired_thirteen_outside_one (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    {b : Finset V} (hb : b ∈ c.blocks) (s t : Finset V) (hs : s.card = 3) (ht : t.card = 3)
    (hinside : contacts G s (c.remainder ∪ b) + contacts G t (c.remainder ∪ b) ≤ 22) :
    ∃ a ∈ c.blocks, a ≠ b ∧ 13 ≤ contacts G s a + contacts G t a := by
  have hbs : ({b} : Finset (Finset V)) ⊆ c.blocks := singleton_subset_iff.mpr hb
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  simp only [card_singleton] at hsub hge
  obtain ⟨a, ha, hna, hh⟩ := c.exists_paired_heavy_outside_selected {b} hbs s t (2 * k) 12
    hdeg (by simp only [hs, ht, singleton_biUnion, id_eq]; omega)
  exact ⟨a, ha, fun he ↦ hna (mem_singleton.mpr he), Nat.succ_le_of_lt hh⟩

end Erdos577.TriangleChain
