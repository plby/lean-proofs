/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Rectangular monomial families for a plane curve of degree d.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Counting

open scoped BigOperators

abbrev CurveMonomial (d n : ℕ) := Fin d × Fin n

def curveDegree {d n : ℕ} (a : CurveMonomial d n) : ℕ := a.1.val + a.2.val

lemma card_curveMonomial (d n : ℕ) : Fintype.card (CurveMonomial d n) = d * n := by
  simp [CurveMonomial]

lemma two_mul_sum_fin_val (n : ℕ) : 2 * (∑ i : Fin n, i.val) + n = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      nlinarith

lemma sum_curveDegree (d n : ℕ) :
    2 * (∑ a : CurveMonomial d n, curveDegree a) + 2 * d * n = d * n * (d + n) := by
  have hsum : (∑ a : CurveMonomial d n, curveDegree a) =
      n * (∑ i : Fin d, i.val) + d * (∑ j : Fin n, j.val) := by
    simp [Fintype.sum_prod_type, curveDegree, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hsum]
  have hd := two_mul_sum_fin_val d
  have hn := two_mul_sum_fin_val n
  nlinarith only [congrArg (n * ·) hd, congrArg (d * ·) hn]

noncomputable def curveExponent {d n : ℕ} (a : CurveMonomial d n) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a.1.val, a.2.val]

@[simp] lemma curveExponent_zero {d n : ℕ} (a : CurveMonomial d n) :
    curveExponent a 0 = a.1.val := rfl

@[simp] lemma curveExponent_one {d n : ℕ} (a : CurveMonomial d n) :
    curveExponent a 1 = a.2.val := rfl

lemma curveExponent_injective {d n : ℕ} :
    Function.Injective (curveExponent (d := d) (n := n)) := by
  intro a b h
  apply Prod.ext
  · exact Fin.ext (congrArg (fun e : Fin 2 →₀ ℕ => e 0) h)
  · exact Fin.ext (congrArg (fun e : Fin 2 →₀ ℕ => e 1) h)

lemma sum_curveExponent {d n : ℕ} (a : CurveMonomial d n) :
    (curveExponent a).sum (fun _ k => k) = curveDegree a := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_two, curveExponent_zero, curveExponent_one, curveDegree]

variable {R : Type*} [CommRing R]

noncomputable def curvePolynomial {d n : ℕ} (a : CurveMonomial d n) :
    MvPolynomial (Fin 2) R := MvPolynomial.monomial (curveExponent a) 1

noncomputable def curveCombination {d n : ℕ} (v : CurveMonomial d n → R) :
    MvPolynomial (Fin 2) R := ∑ a, MvPolynomial.monomial (curveExponent a) (v a)

lemma coeff_curveCombination {d n : ℕ} (v : CurveMonomial d n → R) (a : CurveMonomial d n) :
    (curveCombination v).coeff (curveExponent a) = v a := by
  classical
  simp [curveCombination, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    curveExponent_injective.eq_iff]

lemma curveCombination_ne_zero {d n : ℕ} (v : CurveMonomial d n → R) (hv : ∃ a, v a ≠ 0) :
    curveCombination v ≠ 0 := by
  obtain ⟨a, ha⟩ := hv
  intro h
  have hcoeff := congrArg (MvPolynomial.coeff (curveExponent a)) h
  rw [coeff_curveCombination, MvPolynomial.coeff_zero] at hcoeff
  exact ha hcoeff

lemma degreeOf_curveCombination {d n : ℕ} (v : CurveMonomial d n → R) :
    (curveCombination v).degreeOf 0 ≤ d - 1 := by
  classical
  apply (MvPolynomial.degreeOf_sum_le 0 _ _).trans
  apply Finset.sup_le
  intro a _
  by_cases ha : v a = 0
  · simp [ha]
  · rw [MvPolynomial.degreeOf_monomial_eq _ _ ha, curveExponent_zero]
    exact Nat.le_sub_one_of_lt a.1.isLt

lemma totalDegree_curveCombination {d n : ℕ} (v : CurveMonomial d n → R) :
    (curveCombination v).totalDegree ≤ d + n - 2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  change (curveExponent a).sum (fun _ k => k) ≤ d + n - 2
  rw [sum_curveExponent, curveDegree]
  have h1 := a.1.isLt
  have h2 := a.2.isLt
  omega

lemma eval_curveCombination {d n : ℕ} (v : CurveMonomial d n → R) (z : Fin 2 → R) :
    MvPolynomial.eval z (curveCombination v) = ∑ a, v a * (z 0 ^ a.1.val * z 1 ^ a.2.val) := by
  simp only [curveCombination, map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_two, curveExponent_zero, curveExponent_one]

lemma eval_curvePolynomial {d n : ℕ} (a : CurveMonomial d n) (z : Fin 2 → R) :
    MvPolynomial.eval z (curvePolynomial a) = z 0 ^ a.1.val * z 1 ^ a.2.val := by
  rw [curvePolynomial, MvPolynomial.eval_monomial, one_mul,
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_two, curveExponent_zero, curveExponent_one]

lemma abs_eval_curvePolynomial_le {d n : ℕ} (a : CurveMonomial d n) (z : Fin 2 → ℤ)
    (B : ℝ) (hz : ∀ k, |(z k : ℝ)| ≤ B) :
    |(MvPolynomial.eval z (curvePolynomial a) : ℝ)| ≤ B ^ curveDegree a := by
  have hB : 0 ≤ B := (abs_nonneg (z 0 : ℝ)).trans (hz 0)
  rw [eval_curvePolynomial]
  push_cast
  rw [abs_mul, abs_pow, abs_pow, curveDegree, pow_add]
  gcongr
  · exact hz 0
  · exact hz 1

/-- The rectangular family is independent modulo any curve equation whose
degree in the first variable is exactly d. -/
lemma curve_not_dvd_combination [IsDomain R] {d n : ℕ} (hd : 0 < d)
    (P : MvPolynomial (Fin 2) R) (hP : P.degreeOf 0 = d)
    (v : CurveMonomial d n → R) (hv : ∃ a, v a ≠ 0) : ¬ P ∣ curveCombination v := by
  have hQ := curveCombination_ne_zero v hv
  have hQdegree := degreeOf_curveCombination v
  have hP0 : P ≠ 0 := MvPolynomial.ne_zero_of_degreeOf_ne_zero (hP.trans_ne hd.ne')
  rintro ⟨G, hG⟩
  have hG0 : G ≠ 0 := by intro h; rw [h, mul_zero] at hG; exact hQ hG
  rw [hG, MvPolynomial.degreeOf_mul_eq hP0 hG0, hP] at hQdegree
  omega

#print axioms curve_not_dvd_combination
-- 'Erdos477.Counting.curve_not_dvd_combination' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
