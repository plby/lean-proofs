import ErdosProblems.Erdos577.FullLeafSixOppositeColumns

/-! Four second contacts on four columns of capacity one saturate every column. -/

namespace Erdos577.FullLeafSix

open Finset

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]

lemma columns_one {t j : Finset V} (hcard : j.card = 4) (htotal : contacts G t j = 4)
    (hcolumns : ∀ d ∈ j, degreeIn G d t ≤ 1) : ∀ d ∈ j, degreeIn G d t = 1 := by
  intro d hd
  apply FullLeafEquality.pointwise_eq_of_sum_eq hcolumns ?_ hd
  rw [contacts_comm G t j] at htotal
  simpa only [contacts, sum_const, smul_eq_mul, hcard, mul_one] using htotal

end Erdos577.FullLeafSix
