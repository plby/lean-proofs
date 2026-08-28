import ErdosProblems.Erdos577.CoreTransferLowFactor
import ErdosProblems.Erdos577.CoreTransferConsequences
import ErdosProblems.Erdos577.CoreTransferCount
import ErdosProblems.Erdos577.PathMiddleReplacements

/-! A heavy six-row outside block cannot have at most eight contacts from the old remainder. -/

namespace Erdos577.CoreTransfer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem small_remainder_false {c : TriangleChain G} {q : Quadrilateral G}
    {bs : Finset (Finset V)} (r : Route c q bs) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {b : Finset V} (hb : b ∈ c.blocks) (hbq : b ≠ q.support)
    (hcore : LocalFactor G (insert (q 2) (c.triangle ∪ b)))
    {a : Finset V} (ha : a ∈ c.blocks) (hna : a ∉ bs) (hab : a ≠ b)
    (hheavy : 13 ≤ contacts G (rows c q) a) (hsmall : contacts G c.remainder a ≤ 8) : False := by
  have hq := r.blocks_subset r.contains_cycle
  have haq : a ≠ q.support := fun he ↦ hna (he ▸ r.contains_cycle)
  have hrows := rows_contacts c q hq a
  obtain ⟨i, j, hpair, hrow⟩ : ∃ i j : Fin 4,
      ((i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1)) ∧ 3 ≤ degreeIn G (q i) a := by
    by_cases hh : 3 ≤ degreeIn G (q 1) a
    · exact ⟨1, 3, Or.inl ⟨rfl, rfl⟩, hh⟩
    · exact ⟨3, 1, Or.inr ⟨rfl, rfl⟩, by omega⟩
  have hi : i = 1 ∨ i = 3 := hpair.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1)
  have htri := r.triangle_contacts_le_four hcard hn i hi ha hna hrow
  have hrem := remainder_contacts c a
  have hfour := degreeIn_le_card G (q i) a
  rw [(c.property.blocks_quad a ha).card] at hfour
  have hsum : degreeIn G (q i) a + degreeIn G (q j) a =
      degreeIn G (q 1) a + degreeIn G (q 3) a := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · omega
  have hbound : ((a.filter (G.Adj c.terminal)) ∪ (a.filter (G.Adj (q j)))).card ≤ 4 := by
    calc
      _ ≤ a.card := card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
      _ = 4 := (c.property.blocks_quad a ha).card
  obtain ⟨u, hu, hxu, hju⟩ := common_neighbor_of_union_bound c.terminal (q j) a 4 hbound (by omega)
  have hrep := r.terminal_universal i hi ha hna hrow u hu
  obtain ⟨parts⟩ := common_low_factor c q hq hb hbq hcore ha hab haq i j hpair r.high_contact
    ⟨u, hu, hxu, hju, hrep⟩
  have hbs : ({b, q.support, a} : Finset (Finset V)) ⊆ c.blocks := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hb
    · exact hq
    · exact ha
  exact hn (c.complementPartition.hasPacking_of_selected_factor hcard {b, q.support, a} hbs parts)

end Erdos577.CoreTransfer
