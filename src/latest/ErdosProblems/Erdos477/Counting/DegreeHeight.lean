/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Support and derivative-height bounds in terms of total degree.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.PolynomialHeight
import ErdosProblems.Erdos477.Geometry.CurveCriticalPoints

namespace Erdos477.Counting

open scoped BigOperators

lemma plane_support_card_le {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin 2) R) (D : ℕ) (hD : P.totalDegree ≤ D) :
    P.support.card ≤ (D + 1) ^ 2 := by
  have h := Finset.card_le_card_of_injOn (s := P.support)
    (t := (Finset.range (D + 1)) ×ˢ (Finset.range (D + 1)))
    (fun m => (m 0, m 1)) (by
      intro m hm
      have hdeg := (MvPolynomial.le_totalDegree hm).trans hD
      rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hdeg
      change (m 0, m 1) ∈ (Finset.range (D + 1)) ×ˢ (Finset.range (D + 1))
      simp only [Finset.mem_product, Finset.mem_range]
      omega) (by
      intro a _ b _ h
      ext i
      fin_cases i
      · exact congrArg Prod.fst h
      · exact congrArg Prod.snd h)
  simpa only [Finset.card_product, Finset.card_range, pow_two] using h

lemma abs_eval_plane_monomial_le {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin 2) R) (D : ℕ) (hD : P.totalDegree ≤ D)
    (m : Fin 2 →₀ ℕ) (hm : m ∈ P.support)
    (z : Fin 2 → ℤ) (B : ℝ) (hB : 1 ≤ B) (hz : ∀ k, |(z k : ℝ)| ≤ B) :
    |(MvPolynomial.eval z (MvPolynomial.monomial m (1 : ℤ)) : ℝ)| ≤ B ^ D := by
  have hdeg := (MvPolynomial.le_totalDegree hm).trans hD
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at hdeg
  rw [MvPolynomial.eval_monomial, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  push_cast
  rw [abs_mul, abs_pow, abs_pow]
  calc
    _ ≤ B ^ m 0 * B ^ m 1 := by gcongr <;> exact hz _
    _ = B ^ (m 0 + m 1) := (pow_add ..).symm
    _ ≤ B ^ D := pow_le_pow_right₀ hB hdeg

lemma coefficientSum_pderiv_le (P : MvPolynomial (Fin 2) ℤ)
    (D : ℕ) (hD : P.totalDegree ≤ D) (H : ℝ) (hH : 0 ≤ H)
    (hcoeff : ∀ m, |((P.coeff m : ℤ) : ℝ)| ≤ H) (i : Fin 2) :
    (coefficientSum (MvPolynomial.pderiv i P) : ℝ) ≤ (D + 1 : ℝ) ^ 2 * D * H := by
  classical
  have hcard : (MvPolynomial.pderiv i P).support.card ≤ (D + 1) ^ 2 :=
    plane_support_card_le _ D
      ((Geometry.totalDegree_pderiv_le P i).trans ((Nat.sub_le _ _).trans hD))
  have heach (m) (hm : m ∈ (MvPolynomial.pderiv i P).support) :
      (((MvPolynomial.pderiv i P).coeff m).natAbs : ℝ) ≤ (D : ℝ) * H := by
    have hnonzero := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hnonzero
    have hmP : m + Finsupp.single i 1 ∈ P.support :=
      MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hnonzero)
    have hmi : m i + 1 ≤ D := by
      have h := (MvPolynomial.le_degreeOf_of_mem_support i hmP).trans
        ((MvPolynomial.degreeOf_le_totalDegree P i).trans hD)
      simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using h
    rw [natAbs_cast_eq_abs, MvPolynomial.coeff_pderiv]
    push_cast
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m i : ℝ) + 1)]
    have hmiR : (m i : ℝ) + 1 ≤ D := by exact_mod_cast hmi
    calc
      _ ≤ H * (D : ℝ) := mul_le_mul (hcoeff _) hmiR (by positivity) hH
      _ = _ := mul_comm _ _
  calc
    _ = ∑ m ∈ (MvPolynomial.pderiv i P).support,
        (((MvPolynomial.pderiv i P).coeff m).natAbs : ℝ) := by
      simp only [coefficientSum, Nat.cast_sum]
    _ ≤ ∑ _m ∈ (MvPolynomial.pderiv i P).support, (D : ℝ) * H := Finset.sum_le_sum heach
    _ = ((MvPolynomial.pderiv i P).support.card : ℝ) * ((D : ℝ) * H) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D + 1 : ℝ) ^ 2 * ((D : ℝ) * H) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hH)
      exact_mod_cast hcard
    _ = _ := by ring

#print axioms coefficientSum_pderiv_le
-- 'Erdos477.Counting.coefficientSum_pderiv_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
