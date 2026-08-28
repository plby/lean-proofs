import ErdosProblems.Erdos577.FullRowCompleteBlock
import ErdosProblems.Erdos577.OneContactLabels

/-! Exact triangle contributions in the two locations of the full distinguished row. -/

namespace Erdos577.FullRow

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem direct_triangle_contacts {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hrow : degreeIn G p.leaf a = 4)
    (z : V) (hz : z ∈ p.triangle) (hzrow : degreeIn G z a = 4) : contacts G p.triangle a = 4 := by
  have hfull := (degreeIn_eq_card_iff z a).mp (hzrow.trans (c.property.blocks_quad a ha).card.symm)
  have hcol (u : V) (hu : u ∈ a) : degreeIn G u p.triangle = 1 :=
    (unique_row_of_bound p.triangle u z hz (hfull u hu).symm
      (full_column_triangle_bound hc hcard hn p hp ha hrow u hu)).1
  rw [contacts_comm]
  calc
    contacts G a p.triangle = ∑ _ ∈ a, 1 := sum_congr rfl hcol
    _ = 4 := by simp only [sum_const, smul_eq_mul, mul_one, (c.property.blocks_quad a ha).card]

theorem core_triangle_contacts_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hrow : degreeIn G p.leaf a = 4)
    {b : Finset V} (hb : b ∈ c.blocks) (z : V) (hz : z ∈ b) (hzrow : degreeIn G z a = 4)
    (hcore : ∀ v, v ∉ p.triangle ∪ b → 2 ≤ degreeIn G v (p.triangle ∪ b) →
      LocalFactor G (insert v (p.triangle ∪ b))) : b ≠ a ∧ contacts G p.triangle a = 0 := by
  have hout := full_row_outside (c.property.blocks_quad a ha) z hzrow
  have hba : b ≠ a := fun he ↦ hout (he ▸ hz)
  have hzT : z ∉ p.triangle := by
    intro hh
    have hzF : z ∈ p.support := p.support_eq ▸ mem_insert_of_mem hh
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hz)).2 (hp ▸ hzF)
  have hfull := (degreeIn_eq_card_iff z a).mp (hzrow.trans (c.property.blocks_quad a ha).card.symm)
  have hcol (u : V) (hu : u ∈ a) : degreeIn G u p.triangle = 0 := by
    have huniq := (unique_row_of_bound (p.triangle ∪ b) u z (mem_union_right _ hz)
      (hfull u hu).symm (full_column_core_bound hc hcard hn p hp ha hrow hb hba hcore u hu)).2
    rw [degreeIn, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvT, huv⟩ := mem_filter.mp hv
    have he := (huniq v (mem_union_left _ hvT)).mp huv
    exact hzT (he ▸ hvT)
  refine ⟨hba, ?_⟩
  rw [contacts_comm]
  calc
    contacts G a p.triangle = ∑ _ ∈ a, 0 := sum_congr rfl hcol
    _ = 0 := by simp

theorem outside_labels {c : TriangleChain G}
    {a : Finset V} (ha : a ∈ c.blocks) (z : V) (hz : degreeIn G z a = 1) :
    ∃ d : Quadrilateral G, d.support = a ∧ ∀ j : Fin 4, G.Adj z (d j) ↔ j = 0 := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad a ha
  obtain ⟨d, hd, hrow⟩ := q.exists_one_contact_labels z (by rwa [hq])
  exact ⟨d, hd.trans hq, hrow⟩

end Erdos577.FullRow
