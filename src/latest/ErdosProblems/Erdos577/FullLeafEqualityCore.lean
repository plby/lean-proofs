import ErdosProblems.Erdos577.FullLeafEqualityInside

/-! Saturating the five second-side core degrees makes the whole seven-set complete. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.core_row_le_six {v : V} (hv : v ∈ p.triangle ∪ a) :
    degreeIn G v (p.triangle ∪ a) ≤ 6 := by
  have hb := degreeIn_le_card G v ((p.triangle ∪ a).erase v)
  rw [degreeIn_erase_self G v hv, card_erase_of_mem hv, h.core_card] at hb
  exact hb

lemma Configuration.second_core_contacts_le_thirty :
    contacts G (insert (p.vertices 3) a) (p.triangle ∪ a) ≤ 30 := by
  calc
    contacts G (insert (p.vertices 3) a) (p.triangle ∪ a) ≤
        ∑ _ ∈ insert (p.vertices 3) a, (6 : ℕ) :=
      sum_le_sum (fun _ hv ↦ h.core_row_le_six (h.second_five_subset hv))
    _ = 30 := by rw [sum_const, smul_eq_mul, h.second_five_card]

theorem Configuration.core_complete_of_thirty
    (hthirty : contacts G (insert (p.vertices 3) a) (p.triangle ∪ a) = 30) :
    G.IsNClique 7 (p.triangle ∪ a) := by
  have hrow (u : V) (hu : u ∈ insert (p.vertices 3) a) : degreeIn G u (p.triangle ∪ a) = 6 := by
    have he := contacts_erase_add (G := G) (q := p.triangle ∪ a) hu
    have hb : contacts G ((insert (p.vertices 3) a).erase u) (p.triangle ∪ a) ≤ 24 := by
      calc
        contacts G ((insert (p.vertices 3) a).erase u) (p.triangle ∪ a) ≤
            ∑ _ ∈ (insert (p.vertices 3) a).erase u, (6 : ℕ) :=
          sum_le_sum (fun _ hv ↦ h.core_row_le_six (h.second_five_subset (mem_erase.mp hv).2))
        _ = 24 := by rw [sum_const, smul_eq_mul, card_erase_of_mem hu, h.second_five_card]
    have hupper := h.core_row_le_six (h.second_five_subset hu)
    omega
  have hadj (u : V) (hu : u ∈ insert (p.vertices 3) a) (v : V)
      (hv : v ∈ p.triangle ∪ a) (huv : u ≠ v) : G.Adj u v := by
    have hfull : degreeIn G u ((p.triangle ∪ a).erase u) = ((p.triangle ∪ a).erase u).card := by
      rw [degreeIn_erase_self G u (h.second_five_subset hu), hrow u hu,
        card_erase_of_mem (h.second_five_subset hu), h.core_card]
    exact (degreeIn_eq_card_iff u ((p.triangle ∪ a).erase u)).mp hfull v
      (mem_erase.mpr ⟨huv.symm, hv⟩)
  refine ⟨?_, h.core_card⟩
  intro u hu v hv huv
  by_cases huSecond : u ∈ insert (p.vertices 3) a
  · exact hadj u huSecond v hv huv
  by_cases hvSecond : v ∈ insert (p.vertices 3) a
  · exact (hadj v hvSecond u hu huv.symm).symm
  have huPair : u = p.center ∨ u = p.vertices 2 := by
    rw [h.second_five_eq, mem_sdiff, mem_insert, mem_singleton] at huSecond
    tauto
  have hvPair : v = p.center ∨ v = p.vertices 2 := by
    rw [h.second_five_eq, mem_sdiff, mem_insert, mem_singleton] at hvSecond
    tauto
  rcases huPair with rfl | rfl <;> rcases hvPair with rfl | rfl
  · exact False.elim (huv rfl)
  · exact p.edge12
  · exact p.edge12.symm
  · exact False.elim (huv rfl)

end Erdos577.FullLeafCore
