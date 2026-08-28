import ErdosProblems.Erdos577.TerminalSwap

/-! With a missing low diagonal, the first maximum makes any terminal's high-pair row exact. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Quadrilateral.degree_after_erase_eq_three (q : Quadrilateral G) (z : V) (i : Fin 4)
    (h : ∀ j : Fin 4, j ≠ i → G.Adj z (q j)) :
    degreeIn G z (q.support.erase (q i)) = 3 := by
  have hcard : (q.support.erase (q i)).card = 3 := by
    rw [card_erase_of_mem ((q.mem_support _).mpr ⟨i, rfl⟩), q.card_support]
  rw [← hcard]
  apply (degreeIn_eq_card_iff z (q.support.erase (q i))).mpr
  intro w hw
  obtain ⟨hne, hwq⟩ := mem_erase.mp hw
  obtain ⟨j, rfl⟩ := (q.mem_support w).mp hwq
  exact h j (fun he ↦ hne (congrArg q he))

variable [Fintype V]

theorem TriangleChain.Feasible.high_pair_row {c : TriangleChain G} (hc : c.Feasible)
    (q : Quadrilateral G) (hq : q.support ∈ c.blocks)
    (hn : ¬G.Adj (q 1) (q 3)) (h0 : G.Adj c.terminal (q 0)) (h2 : G.Adj c.terminal (q 2)) :
    ∀ j : Fin 4, G.Adj c.terminal (q j) ↔ (5 : ℕ).testBit j.val = true := by
  have h1 : ¬G.Adj c.terminal (q 1) := by
    intro hh
    have hr := q.degree_after_erase_eq_three c.terminal 3 (by
      intro j hj
      fin_cases j
      · exact h0
      · exact hh
      · exact h2
      · exact False.elim (hj rfl))
    have hd := hc.terminal_replacement_diagonal hq q rfl 3 hr
    change G.Adj (q 3) (q 1) at hd
    exact hn hd.symm
  have h3 : ¬G.Adj c.terminal (q 3) := by
    intro hh
    have hr := q.degree_after_erase_eq_three c.terminal 1 (by
      intro j hj
      fin_cases j
      · exact h0
      · exact False.elim (hj rfl)
      · exact h2
      · exact hh)
    have hd := hc.terminal_replacement_diagonal hq q rfl 1 hr
    exact hn hd
  intro j
  fin_cases j
  · exact ⟨fun _ ↦ by decide, fun _ ↦ h0⟩
  · exact ⟨fun hh ↦ False.elim (h1 hh), fun hh ↦ False.elim (by contradiction)⟩
  · exact ⟨fun _ ↦ by decide, fun _ ↦ h2⟩
  · exact ⟨fun hh ↦ False.elim (h3 hh), fun hh ↦ False.elim (by contradiction)⟩

end Erdos577
