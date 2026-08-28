import ErdosProblems.Erdos577.OutsideSelectedCount

/-! Paired degree averaging preserves intentional overlap between two vertex sets. -/

namespace Erdos577.TriangleChain

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma exists_paired_heavy_outside_selected (c : TriangleChain G) (bs : Finset (Finset V))
    (hbs : bs ⊆ c.blocks) (s t : Finset V) (d threshold : ℕ) (hdeg : ∀ v, d ≤ G.degree v)
    (hbudget : contacts G s (c.remainder ∪ bs.biUnion id) +
      contacts G t (c.remainder ∪ bs.biUnion id) + (c.blocks \ bs).card * threshold <
      s.card * d + t.card * d) :
    ∃ a ∈ c.blocks, a ∉ bs ∧ threshold < contacts G s a + contacts G t a := by
  have htotalS := minimum_degree_sum G s d (fun v _ ↦ hdeg v)
  have htotalT := minimum_degree_sum G t d (fun v _ ↦ hdeg v)
  have hidS := c.contacts_selected_core_add_outside bs hbs s
  have hidT := c.contacts_selected_core_add_outside bs hbs t
  by_contra! hn
  have hbound : (∑ a ∈ c.blocks \ bs, (contacts G s a + contacts G t a)) ≤
      (c.blocks \ bs).card * threshold := by
    calc
      _ ≤ ∑ _ ∈ c.blocks \ bs, threshold := sum_le_sum fun a ha ↦
        hn a (mem_sdiff.mp ha).1 (mem_sdiff.mp ha).2
      _ = _ := by simp
  rw [sum_add_distrib] at hbound
  omega

lemma exists_paired_thirteen_outside_two (c : TriangleChain G) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (bs : Finset (Finset V)) (hbs : bs ⊆ c.blocks) (hbs2 : bs.card = 2)
    (s t : Finset V) (hs : s.card = 3) (ht : t.card = 3)
    (hinside : contacts G s (c.remainder ∪ bs.biUnion id) +
      contacts G t (c.remainder ∪ bs.biUnion id) ≤ 31) :
    ∃ a ∈ c.blocks, a ∉ bs ∧ 13 ≤ contacts G s a + contacts G t a := by
  have hblocks := c.card_vertices
  have hsub := card_sdiff_of_subset hbs
  have hge := card_le_card hbs
  obtain ⟨a, ha, hna, hh⟩ := c.exists_paired_heavy_outside_selected bs hbs s t (2 * k) 12
    hdeg (by rw [hs, ht]; omega)
  exact ⟨a, ha, hna, Nat.succ_le_of_lt hh⟩

end Erdos577.TriangleChain
