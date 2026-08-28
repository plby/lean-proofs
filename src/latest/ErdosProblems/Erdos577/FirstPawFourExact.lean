import ErdosProblems.Erdos577.FirstPawFourColumns

/-! Excluding the two low center contacts forces exactly nine contacts in case (4). -/

namespace Erdos577.PawBlock

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Pattern4.center_rows (p : Paw G) (q : Quadrilateral G) (h : Pattern4 p q)
    (hnot : ¬(G.Adj p.center (q 1) ∧ G.Adj p.center (q 3))) :
    WeightedPawBlock.Row p q 1 13 ∨ WeightedPawBlock.Row p q 1 7 := by
  by_cases h1 : G.Adj p.center (q 1)
  · right
    have h3 : ¬G.Adj p.center (q 3) := fun hh ↦ hnot ⟨h1, hh⟩
    apply q.row_saturated (p.vertices 1) 7
    · intro j hj
      have hj3 : j ≠ 3 := fun he ↦ h3 (he ▸ hj)
      have hmask : ∀ j : Fin 4, j ≠ 3 → (7 : ℕ).testBit j.val = true := by decide +kernel
      exact hmask j hj3
    · have hm : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
      rw [hm]
      exact h.2.1
  · left
    apply q.row_saturated (p.vertices 1) 13
    · intro j hj
      have hj1 : j ≠ 1 := fun he ↦ h1 (he ▸ hj)
      have hmask : ∀ j : Fin 4, j ≠ 1 → (13 : ℕ).testBit j.val = true := by decide +kernel
      exact hmask j hj1
    · have hm : (∑ j : Fin 4, ((13 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
      rw [hm]
      exact h.2.1

lemma Pattern4.exact_rows_of_center_no_both (p : Paw G) (q : Quadrilateral G) (h : Pattern4 p q)
    (hleaf : degreeIn G p.leaf q.support = 2) (hheavy : 9 ≤ contacts G p.support q.support)
    (hnot : ¬(G.Adj p.center (q 1) ∧ G.Adj p.center (q 3))) :
    contacts G p.support q.support = 9 ∧
      (ExactRows p q ![5, 13, 5, 5] ∨ ExactRows p q ![5, 7, 5, 5]) := by
  have hr := h.center_rows p q hnot
  have hcenter : degreeIn G (p.vertices 1) q.support = 3 := by
    rcases hr with hr | hr
    · rw [hr.degree p q 1 13]
      decide +kernel
    · rw [hr.degree p q 1 7]
      decide +kernel
  obtain ⟨hb, hc⟩ := h.noncentral_bounds p q
  have hsum := p.contacts_support q.support
  rw [p.contacts_triangle] at hsum
  have hb2 : degreeIn G (p.vertices 2) q.support = 2 := by omega
  have hc2 : degreeIn G (p.vertices 3) q.support = 2 := by omega
  have htotal : contacts G p.support q.support = 9 := by omega
  have hm : (∑ j : Fin 4, ((5 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  have hmask : ∀ j : Fin 4, (j = 0 ∨ j = 2) → (5 : ℕ).testBit j.val = true := by
    decide +kernel
  have hbr : WeightedPawBlock.Row p q 2 5 := q.row_saturated (p.vertices 2) 5
    (fun j hj ↦ hmask j (h.2.2.2 j (Or.inr (Or.inl hj)))) (by rw [hm, hb2])
  have hcr : WeightedPawBlock.Row p q 3 5 := q.row_saturated (p.vertices 3) 5
    (fun j hj ↦ hmask j (h.2.2.2 j (Or.inr (Or.inr hj)))) (by rw [hm, hc2])
  have hxr := h.leaf_exact p q hleaf
  refine ⟨htotal, ?_⟩
  rcases hr with hr | hr
  · left
    intro i j
    fin_cases i
    · exact hxr j
    · exact hr j
    · exact hbr j
    · exact hcr j
  · right
    intro i j
    fin_cases i
    · exact hxr j
    · exact hr j
    · exact hbr j
    · exact hcr j

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma ExactRows.four_reverse (p : Paw G) (q : Quadrilateral G)
    (h : ExactRows p q ![5, 7, 5, 5]) : ExactRows p q.reverse ![5, 13, 5, 5] := by
  have hbits : ∀ i j : Fin 4, ((![5, 7, 5, 5] : Fin 4 → ℕ) i).testBit (-j).val =
      ((![5, 13, 5, 5] : Fin 4 → ℕ) i).testBit j.val := by decide +kernel
  intro i j
  rw [Quadrilateral.reverse_apply, h i (-j), hbits i j]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma ExactRows.four_unnormalize (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (h : ExactRows (FirstPaw.normalizedPaw p swap) q ![5, 13, 5, 5]) :
    ExactRows p q ![5, 13, 5, 5] := by
  cases swap
  · exact h
  · intro i j
    fin_cases i
    · exact h 0 j
    · exact h 1 j
    · exact h 3 j
    · exact h 2 j

end Erdos577.PawBlock
