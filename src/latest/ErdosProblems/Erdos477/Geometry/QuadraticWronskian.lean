/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Vanishing of the Wronskian for a base-point-free quadratic sixth-power identity.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.WronskianThree
import ErdosProblems.Erdos477.Geometry.PolynomialBezout

namespace Erdos477.Geometry

open Polynomial
open scoped BigOperators

lemma prod_univ_erase_fin {n : ℕ} {R : Type*} [CommMonoid R] (f : Fin (n + 1) → R)
    (i : Fin (n + 1)) :
    (∏ j ∈ Finset.univ.erase i, f j) = ∏ j : Fin n, f (i.succAbove j) := by
  have herase : Finset.univ.erase i = Finset.univ.map i.succAboveEmb := by
    conv_lhs => rw [Fin.univ_succAbove n i]
    exact Finset.erase_cons _
  rw [herase, Finset.prod_map]
  rfl

variable {K : Type*} [Field K] [IsAlgClosed K]

lemma four_sixth_wronskian_divisibility (f : Fin 4 → K[X])
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0)
    (hsum : f 0 ^ 6 + f 1 ^ 6 + f 2 ^ 6 + f 3 ^ 6 = 0) :
    (∏ i, f i ^ 4) ∣ wronskianThree ![f 0 ^ 6, f 1 ^ 6, f 2 ^ 6] := by
  have hlast : f 3 ^ 6 = -(f 0 ^ 6 + f 1 ^ 6 + f 2 ^ 6) := by
    linear_combination hsum
  apply polynomial_prod_dvd_of_except_dvd (fun i => f i ^ 4)
  · intro x
    obtain ⟨i, hi⟩ := hroot x
    exact ⟨i, by simpa only [eval_pow] using pow_ne_zero 4 hi⟩
  intro i
  rw [prod_univ_erase_fin, Fin.prod_univ_three]
  fin_cases i
  · have h := prod_pow_dvd_wronskianThree ![f 1, f 2, f 3] 6
    have heq : (fun j => ![f 1, f 2, f 3] j ^ 6) = ![f 1 ^ 6, f 2 ^ 6, f 3 ^ 6] := by
      ext j; fin_cases j <;> rfl
    rw [heq, hlast, wronskianThree_neg_sum, dvd_neg] at h
    simpa [Fin.prod_univ_three, Fin.succAbove] using h
  · have h := prod_pow_dvd_wronskianThree ![f 0, f 2, f 3] 6
    have heq : (fun j => ![f 0, f 2, f 3] j ^ 6) = ![f 0 ^ 6, f 2 ^ 6, f 3 ^ 6] := by
      ext j; fin_cases j <;> rfl
    have hlast' : f 3 ^ 6 = -(f 1 ^ 6 + f 0 ^ 6 + f 2 ^ 6) := by rw [hlast]; ring
    rw [heq, hlast', wronskianThree_neg_sum, wronskianThree_swap, neg_neg] at h
    simpa [Fin.prod_univ_three, Fin.succAbove] using h
  · have h := prod_pow_dvd_wronskianThree ![f 0, f 1, f 3] 6
    have heq : (fun j => ![f 0, f 1, f 3] j ^ 6) = ![f 0 ^ 6, f 1 ^ 6, f 3 ^ 6] := by
      ext j; fin_cases j <;> rfl
    have hlast' : f 3 ^ 6 = -(f 2 ^ 6 + f 0 ^ 6 + f 1 ^ 6) := by rw [hlast]; ring
    rw [heq, hlast', wronskianThree_neg_sum, ← wronskianThree_cycle,
      dvd_neg] at h
    simpa [Fin.prod_univ_three, Fin.succAbove] using h
  · have h := prod_pow_dvd_wronskianThree ![f 0, f 1, f 2] 6
    have heq : (fun j => ![f 0, f 1, f 2] j ^ 6) = ![f 0 ^ 6, f 1 ^ 6, f 2 ^ 6] := by
      ext j; fin_cases j <;> rfl
    rw [heq] at h
    simpa [Fin.prod_univ_three, Fin.succAbove] using h

/-- Four degree-two polynomials without a common root whose sixth powers
sum to zero have vanishing three-column Wronskian: its degree is at most 30,
but a nonzero one would have a divisor of degree 32. -/
theorem quadratic_sixth_wronskian_eq_zero (f : Fin 4 → K[X])
    (hf : ∀ i, (f i).natDegree = 2)
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0)
    (hsum : f 0 ^ 6 + f 1 ^ 6 + f 2 ^ 6 + f 3 ^ 6 = 0) :
    wronskianThree ![f 0 ^ 6, f 1 ^ 6, f 2 ^ 6] = 0 := by
  have hf0 (i) : f i ≠ 0 := by
    intro hi
    have h := hf i
    rw [hi, natDegree_zero] at h
    omega
  have hdegree : (∏ i, f i ^ 4).natDegree = 32 := by
    rw [natDegree_prod _ _ (fun i _ => pow_ne_zero 4 (hf0 i))]
    simp only [natDegree_pow, hf, Fin.sum_univ_four]
  have hbound : (wronskianThree ![f 0 ^ 6, f 1 ^ 6, f 2 ^ 6]).natDegree ≤ 30 := by
    apply natDegree_wronskianThree_le 12 (by decide)
    intro j
    fin_cases j <;> simp [natDegree_pow, hf]
  by_contra hne
  have hdiv := natDegree_le_of_dvd (four_sixth_wronskian_divisibility f hroot hsum) hne
  rw [hdegree] at hdiv
  omega

#print axioms quadratic_sixth_wronskian_eq_zero
-- 'Erdos477.Geometry.quadratic_sixth_wronskian_eq_zero' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
