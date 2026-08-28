import ErdosProblems.Erdos577.FullLeafSixDiamondLabels

/-! Eight contacts and one low column force an actual three-neighbor row. -/

namespace Erdos577.FullLeafSix

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma three_contacts_of_eight (q : Quadrilateral G) {t : Finset V} (ht : t.card = 3)
    (height : contacts G t q.support = 8) (hlow : degreeIn G (q 3) t ≤ 1) :
    ∃ x ∈ t, ∀ i : Fin 4, i ≠ 3 → G.Adj x (q i) := by
  have hm : q 3 ∈ q.support := (q.mem_support _).mpr ⟨3, rfl⟩
  have he := contacts_erase_add (G := G) (q := t) hm
  rw [contacts_comm G (q.support.erase (q 3)) t, contacts_comm G q.support t] at he
  have hseven : 7 ≤ contacts G t (q.support.erase (q 3)) := by omega
  obtain ⟨x, hx, hrow⟩ := exists_row_gt_of_contacts (G := G) (n := 2)
    (q := q.support.erase (q 3)) (by rw [ht]; omega)
  have hc : (q.support.erase (q 3)).card = 3 := by
    rw [card_erase_of_mem hm, q.card_support]
  have hb := degreeIn_le_card G x (q.support.erase (q 3))
  have hfull := (degreeIn_eq_card_iff (G := G) x (q.support.erase (q 3))).mp (by omega)
  refine ⟨x, hx, fun i hi ↦ hfull (q i) ?_⟩
  exact mem_erase.mpr ⟨q.injective.ne hi, (q.mem_support _).mpr ⟨i, rfl⟩⟩

end Erdos577.FullLeafSix
