import ErdosProblems.Erdos577.FirstPawLeafTwo

/-! Individual noncentral row bounds used when comparing two paw presentations. -/

namespace Erdos577.PawBlock

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Pattern4.noncentral_bounds (p : Paw G) (q : Quadrilateral G) (h : Pattern4 p q) :
    degreeIn G (p.vertices 2) q.support ≤ 2 ∧ degreeIn G (p.vertices 3) q.support ≤ 2 := by
  have hbits : ∀ j : Fin 4, (j = 0 ∨ j = 2) → (5 : ℕ).testBit j.val = true := by
    decide +kernel
  have hb := q.degree_le_mask (p.vertices 2) 5
    (fun j hj ↦ hbits j (h.2.2.2 j (Or.inr (Or.inl hj))))
  have hc := q.degree_le_mask (p.vertices 3) 5
    (fun j hj ↦ hbits j (h.2.2.2 j (Or.inr (Or.inr hj))))
  have hm : (∑ j : Fin 4, ((5 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  rw [hm] at hb hc
  exact ⟨hb, hc⟩

lemma Pattern4.normalized_noncentral_bounds (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (h : Pattern4 (FirstPaw.normalizedPaw p swap) q) :
    degreeIn G (p.vertices 2) q.support ≤ 2 ∧ degreeIn G (p.vertices 3) q.support ≤ 2 := by
  have hh := h.noncentral_bounds (FirstPaw.normalizedPaw p swap) q
  cases swap
  · exact hh
  · exact ⟨hh.2, hh.1⟩

lemma Pattern6.last_bound (p : Paw G) (q : Quadrilateral G) (h : Pattern6 p q) :
    degreeIn G (p.vertices 3) q.support ≤ 1 := by
  have hh := q.degree_le_mask (p.vertices 3) 1
    (fun j hj ↦ by rw [h.2.2.2 j hj]; decide)
  have hm : (∑ j : Fin 4, ((1 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
  rwa [hm] at hh

end Erdos577.PawBlock
