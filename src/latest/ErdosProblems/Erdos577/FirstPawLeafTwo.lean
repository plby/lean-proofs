import ErdosProblems.Erdos577.FirstPawLeafCount

/-! A two-contact leaf leaves precisely cases (4), (5), and (6) of the first classification. -/

namespace Erdos577.PawBlock

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma PatternsWithOutside.leaf_two (p : Paw G) (q : Quadrilateral G)
    (h : PatternsWithOutside p q) (hleaf : degreeIn G p.leaf q.support = 2) :
    Pattern4 p q ∨ Pattern5 p q ∨ Pattern6 p q := by
  have hnot (rows : Fin 4 → ℕ) (hrows : ExactRows p q rows) (hzero : rows 0 = 1) :
      False := by
    have hr := WeightedPawBlock.Row.degree p q 0 (rows 0) (hrows 0)
    change degreeIn G p.leaf q.support = _ at hr
    rw [hzero] at hr
    have hm : (∑ j : Fin 4, ((1 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
    rw [hm] at hr
    omega
  rcases h with h | h | h | h | h | h
  · exact False.elim (hnot _ h.1.2 rfl)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact False.elim (hnot _ h.2 rfl)
  · exact False.elim (hnot _ h.1.2 rfl)

lemma FullClassification.leaf_two (p : Paw G) (q : Quadrilateral G)
    (h : FullClassification p q) (hleaf : degreeIn G p.leaf q.support = 2) :
    ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
      (Pattern4 (FirstPaw.normalizedPaw p swap) q' ∨
        Pattern5 (FirstPaw.normalizedPaw p swap) q' ∨
        Pattern6 (FirstPaw.normalizedPaw p swap) q') := by
  obtain ⟨_, _, swap, q', hq', hp⟩ := h
  refine ⟨swap, q', hq', hp.leaf_two _ _ ?_⟩
  rw [FirstPaw.normalizedPaw_leaf, hq']
  exact hleaf

lemma Pattern5.center_le_two (p : Paw G) (q : Quadrilateral G) (h : Pattern5 p q) :
    degreeIn G p.center q.support ≤ 2 := by
  have hbits : ∀ j : Fin 4, (j = 0 ∨ j = 2) → (5 : ℕ).testBit j.val = true := by
    decide +kernel
  have hr := q.degree_le_mask (p.vertices 1) 5 (fun j hj ↦ hbits j (h.2.1 j (Or.inr hj)))
  have hm : (∑ j : Fin 4, ((5 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  rwa [hm] at hr

lemma Pattern6.center_ge_three (p : Paw G) (q : Quadrilateral G) (h : Pattern6 p q)
    (hheavy : 9 ≤ contacts G p.support q.support) : 3 ≤ degreeIn G p.center q.support := by
  have hbits3 : ∀ j : Fin 4, (j = 0 ∨ j = 1) → (3 : ℕ).testBit j.val = true := by
    decide +kernel
  have hbits7 : ∀ j : Fin 4, j ≠ 3 → (7 : ℕ).testBit j.val = true := by decide +kernel
  have hx := q.degree_le_mask (p.vertices 0) 3 (fun j hj ↦ hbits3 j (h.2.1 j hj))
  have hb := q.degree_le_mask (p.vertices 2) 7 (fun j hj ↦ hbits7 j (h.2.2.1 j hj))
  have hc := q.degree_le_mask (p.vertices 3) 1 (fun j hj ↦ by rw [h.2.2.2 j hj]; decide)
  have hm3 : (∑ j : Fin 4, ((3 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  have hm7 : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have hm1 : (∑ j : Fin 4, ((1 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
  rw [hm3] at hx
  rw [hm7] at hb
  rw [hm1] at hc
  rw [p.contacts_support, p.contacts_triangle] at hheavy
  change 3 ≤ degreeIn G (p.vertices 1) q.support
  change degreeIn G p.leaf q.support ≤ 2 at hx
  omega

end Erdos577.PawBlock
