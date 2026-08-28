import ErdosProblems.Erdos577.WeightedPawPatterns

/-! Degree consequences of exact and included weighted rows. -/

namespace Erdos577

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Quadrilateral.degree_ge_mask (q : Quadrilateral G) (z : V) (mask : ℕ)
    (h : ∀ j : Fin 4, mask.testBit j.val = true → G.Adj z (q j)) :
    (∑ j : Fin 4, (mask.testBit j.val).toNat) ≤ degreeIn G z q.support := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rw [Quadrilateral.support, degreeIn_image G z univ q hinj]
  apply sum_le_sum
  intro j _
  cases hb : mask.testBit j.val
  · simp only [Bool.toNat_false, zero_le]
  · simp only [Bool.toNat_true, if_pos (h j hb), le_refl]

namespace WeightedPawBlock

lemma Row.degree (p : Paw G) (q : Quadrilateral G) (i : Fin 4) (mask : ℕ)
    (h : Row p q i mask) :
    degreeIn G (p.vertices i) q.support = ∑ j : Fin 4, (mask.testBit j.val).toNat := by
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  rw [Quadrilateral.support, degreeIn_image G (p.vertices i) univ q hinj]
  apply sum_congr rfl
  intro j _
  simp only [h j]
  cases hb : mask.testBit j.val <;> simp only [Bool.false_eq_true, if_false,
    Bool.toNat_false, if_true, Bool.toNat_true]

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma Row.full (p : Paw G) (q : Quadrilateral G) (i : Fin 4)
    (h : Row p q i 15) (j : Fin 4) : G.Adj (p.vertices i) (q j) := by
  apply (h j).mpr
  fin_cases j <;> decide

lemma Row.three_le (p : Paw G) (q : Quadrilateral G) (i : Fin 4)
    (h : Row p q i 7) : 3 ≤ degreeIn G (p.vertices i) q.support := by
  rw [h.degree p q i 7]
  decide +kernel

end WeightedPawBlock

end Erdos577
