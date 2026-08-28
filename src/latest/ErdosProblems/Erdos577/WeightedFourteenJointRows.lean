import ErdosProblems.Erdos577.WeightedFourteenPawRows
import ErdosProblems.Erdos577.RowSaturationIncluded

/-! Both exposed terminal rows equal the high pair in pattern (14)'s forced second block. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma PawBlock.ExactRows.full_column (p : Paw G) (q : Quadrilateral G) (rows : Fin 4 → ℕ)
    (h : PawBlock.ExactRows p q rows) (j : Fin 4)
    (hbits : ∀ i : Fin 4, (rows i).testBit j.val = true) :
    ∀ u ∈ p.triangle, G.Adj (q j) u := by
  intro u hu
  change u ∈ {p.vertices 1, p.vertices 2, p.vertices 3} at hu
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl | rfl
  · exact ((h 1 j).mpr (hbits 1)).symm
  · exact ((h 2 j).mpr (hbits 2)).symm
  · exact ((h 3 j).mpr (hbits 3)).symm

namespace WeightedFourteen

variable [Fintype V] [DecidableRel G.Adj]

theorem terminal_high_pair_row {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q) (tag : Fin 3)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b)
    (v : Quadrilateral G) (hv : v.support = a)
    (hfull : ∀ j : Fin 4, (j = 0 ∨ j = 2) → ∀ u ∈ p.triangle, G.Adj (v j) u)
    (hrow : degreeIn G (terminal p q tag) a = 2) :
    ∀ j : Fin 4, G.Adj (terminal p q tag) (v j) ↔ (5 : ℕ).testBit j.val = true := by
  obtain ⟨d, hdF, hdx, hdt, hkeep⟩ := exists_terminal_chain hc p hp hb q hq hd h tag
  have he0 := hdF.terminal_high_contact_any_block hcard hn (hkeep a ha hab) v hv
    (by rw [hdt]; exact hfull 0 (Or.inl rfl)) (by rw [hdx, hv]; exact hrow)
  rw [hdx] at he0
  have he2 := hdF.terminal_high_contact_any_block hcard hn (hkeep a ha hab) (v.rotate 2)
    ((v.rotate_support 2).trans hv)
    (by rw [hdt]; exact hfull 2 (Or.inr rfl))
    (by rw [hdx, v.rotate_support, hv]; exact hrow)
  rw [hdx] at he2
  change G.Adj (terminal p q tag) (v 2) at he2
  apply v.row_saturated_of_included (terminal p q tag) 5
  · intro j hj
    have hbits : ∀ j : Fin 4, (5 : ℕ).testBit j.val = true → j = 0 ∨ j = 2 := by
      decide +kernel
    rcases hbits j hj with rfl | rfl
    · exact he0
    · exact he2
  · rw [hv, hrow]
    decide +kernel

theorem joint_rows_at_heavy {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern14 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (hheavy : 17 ≤ weight p q a) :
    contacts G p.support a = 9 ∧ ∃ v : Quadrilateral G, v.support = a ∧
      PawBlock.OnlyFirst v ∧ (PawBlock.ExactRows p v ![5, 13, 5, 5] ∨
        ∃ swap : Bool, PawBlock.ExactRows (FirstPaw.normalizedPaw p swap) v ![5, 5, 13, 5]) ∧
      (∀ j : Fin 4, G.Adj (q 1) (v j) ↔ (5 : ℕ).testBit j.val = true) ∧
      (∀ j : Fin 4, G.Adj (q 3) (v j) ↔ (5 : ℕ).testBit j.val = true) := by
  obtain ⟨htotal, v, hv, hdiag, hrows⟩ := paw_rows_at_heavy hc hcard hdeg hn p hp hb q hq
    hd h ha hab hheavy
  obtain ⟨_, hy2, _, _, _, _, hlast⟩ := heavy_rows hc hcard hdeg hn p hp hb q hq hd h ha hab hheavy
  have hw2 := hlast htotal
  have hfull : ∀ j : Fin 4, (j = 0 ∨ j = 2) → ∀ u ∈ p.triangle, G.Adj (v j) u := by
    intro j hj
    rcases hrows with hr | ⟨swap, hr⟩
    · have hbits : ∀ i j : Fin 4, (j = 0 ∨ j = 2) →
          ((![5, 13, 5, 5] : Fin 4 → ℕ) i).testBit j.val = true := by decide +kernel
      exact hr.full_column p v _ j (fun i ↦ hbits i j hj)
    · have hbits : ∀ i j : Fin 4, (j = 0 ∨ j = 2) →
          ((![5, 5, 13, 5] : Fin 4 → ℕ) i).testBit j.val = true := by decide +kernel
      rw [← FirstPaw.normalizedPaw_triangle p swap]
      exact hr.full_column (FirstPaw.normalizedPaw p swap) v _ j (fun i ↦ hbits i j hj)
  exact ⟨htotal, v, hv, hdiag, hrows,
    terminal_high_pair_row hc hcard hn p hp hb q hq hd h 1 ha hab v hv hfull hy2,
    terminal_high_pair_row hc hcard hn p hp hb q hq hd h 2 ha hab v hv hfull hw2⟩

end WeightedFourteen

end Erdos577
