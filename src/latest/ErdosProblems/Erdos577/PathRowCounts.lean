import ErdosProblems.Erdos577.PathClassPatterns

/-! Exact row bounds and equality at nine in the complete-block path pattern. -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Quadrilateral.degree_le_mask (q : Quadrilateral G) (z : V) (mask : ℕ)
    (h : ∀ j : Fin 4, G.Adj z (q j) → mask.testBit j.val = true) :
    degreeIn G z q.support ≤ ∑ j : Fin 4, (mask.testBit j.val).toNat := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rw [Quadrilateral.support, degreeIn_image G z univ q hinj]
  apply sum_le_sum
  intro j _
  by_cases hj : G.Adj z (q j)
  · rw [if_pos hj, h j hj]
    exact le_refl 1
  · simp only [if_neg hj, zero_le]

lemma FourPath.contacts_support (p : FourPath G) (s : Finset V) :
    contacts G p.support s = degreeIn G (p.vertices 0) s + degreeIn G (p.vertices 1) s +
      degreeIn G (p.vertices 2) s + degreeIn G (p.vertices 3) s := by
  rw [FourPath.support, contacts_image_left G univ p.vertices p.vertices.injective]
  simp only [Fin.sum_univ_four]

namespace PathBlock

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma PatternB.reverse_iff (p : FourPath G) (q : Quadrilateral G) :
    PatternB p.reverse q ↔ PatternB p q := by
  change ((∀ j : Fin 4, G.Adj (p.vertices 3) (q j) ∨ G.Adj (p.vertices 0) (q j) →
      j = 0 ∨ j = 1) ∧
    (∀ j : Fin 4, G.Adj (p.vertices 2) (q j) ∨ G.Adj (p.vertices 1) (q j) → j ≠ 3)) ↔ _
  simp only [PatternB, or_comm]

lemma PatternB.row_bounds (p : FourPath G) (q : Quadrilateral G) (h : PatternB p q) :
    degreeIn G (p.vertices 0) q.support ≤ 2 ∧ degreeIn G (p.vertices 1) q.support ≤ 3 ∧
      degreeIn G (p.vertices 2) q.support ≤ 3 ∧ degreeIn G (p.vertices 3) q.support ≤ 2 := by
  have h3 : ∀ j : Fin 4, (j = 0 ∨ j = 1) → (3 : ℕ).testBit j.val = true := by decide +kernel
  have h7 : ∀ j : Fin 4, j ≠ 3 → (7 : ℕ).testBit j.val = true := by decide +kernel
  have hs3 : (∑ j : Fin 4, ((3 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  have hs7 : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have h0 := q.degree_le_mask (p.vertices 0) 3 (fun j hj ↦ h3 j (h.1 j (Or.inl hj)))
  have h1 := q.degree_le_mask (p.vertices 1) 7 (fun j hj ↦ h7 j (h.2 j (Or.inl hj)))
  have h2 := q.degree_le_mask (p.vertices 2) 7 (fun j hj ↦ h7 j (h.2 j (Or.inr hj)))
  have h3' := q.degree_le_mask (p.vertices 3) 3 (fun j hj ↦ h3 j (h.1 j (Or.inr hj)))
  rw [hs3] at h0 h3'
  rw [hs7] at h1 h2
  exact ⟨h0, h1, h2, h3'⟩

lemma PatternB.exact_nine (p : FourPath G) (q : Quadrilateral G) (h : PatternB p q)
    (hheavy : 9 ≤ contacts G p.support q.support)
    (hsmall : degreeIn G (p.vertices 1) q.support ≤ 2) :
    contacts G p.support q.support = 9 ∧ degreeIn G (p.vertices 0) q.support = 2 ∧
      degreeIn G (p.vertices 1) q.support = 2 ∧ degreeIn G (p.vertices 2) q.support = 3 ∧
      degreeIn G (p.vertices 3) q.support = 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := h.row_bounds p q
  have hsum := p.contacts_support q.support
  omega

end PathBlock

end Erdos577
