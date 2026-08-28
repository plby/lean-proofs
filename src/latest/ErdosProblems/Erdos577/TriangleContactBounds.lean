import ErdosProblems.Erdos577.TriangleRows

/-! A missing contact and a dense column in a three-by-four incidence table. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma triangle_contacts_le_eleven_of_missing {t a : Finset V}
    (ht : t.card = 3) (ha : a.card = 4) {x w : V} (hx : x ∈ t) (hw : w ∈ a)
    (hn : ¬G.Adj x w) : contacts G t a ≤ 11 := by
  classical
  have hsub : a.filter (G.Adj x) ⊆ a.erase w := by
    intro u hu
    obtain ⟨hua, hxu⟩ := mem_filter.mp hu
    exact mem_erase.mpr ⟨fun he ↦ hn (he ▸ hxu), hua⟩
  have hrow := card_le_card hsub
  change degreeIn G x a ≤ (a.erase w).card at hrow
  rw [card_erase_of_mem hw, ha] at hrow
  have hid := contacts_erase_add (G := G) (q := a) hx
  have hbound := contacts_le_card_mul G (t.erase x) a
  rw [card_erase_of_mem hx, ht, ha] at hbound
  omega

omit [DecidableEq V] in
lemma triangle_column_ge_two_of_eleven {t a : Finset V}
    (ht : t.card = 3) (ha : a.card = 4) (hh : 11 ≤ contacts G t a)
    {w : V} (hw : w ∈ a) : 2 ≤ degreeIn G w t := by
  classical
  have hid := contacts_erase_add (G := G) (q := t) hw
  have hbound := contacts_le_card_mul G (a.erase w) t
  rw [card_erase_of_mem hw, ha, ht] at hbound
  rw [contacts_comm G a t] at hid
  omega

end Erdos577
