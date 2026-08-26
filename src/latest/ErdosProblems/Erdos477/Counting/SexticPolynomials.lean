/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Distinct sextic monomials, coefficient recovery, and degree bounds.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.SexticMonomials

namespace Erdos477.Counting

open scoped BigOperators

noncomputable def sexticExponent {n : ℕ} (a : SexticMonomial n) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![a.2.val.1, a.2.val.2, 5 - a.1.val]

@[simp] lemma sexticExponent_zero {n : ℕ} (a : SexticMonomial n) :
    sexticExponent a 0 = a.2.val.1 := rfl

@[simp] lemma sexticExponent_one {n : ℕ} (a : SexticMonomial n) :
    sexticExponent a 1 = a.2.val.2 := rfl

@[simp] lemma sexticExponent_two {n : ℕ} (a : SexticMonomial n) :
    sexticExponent a 2 = 5 - a.1.val := rfl

lemma sexticExponent_injective {n : ℕ} :
    Function.Injective (sexticExponent (n := n)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hab
  have hij : i = j := by
    have h := congrArg (fun e : Fin 3 →₀ ℕ => e 2) hab
    simp only [sexticExponent_two] at h
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  subst j
  apply congrArg (Sigma.mk i)
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun e : Fin 3 →₀ ℕ => e 0) hab
  · exact congrArg (fun e : Fin 3 →₀ ℕ => e 1) hab

lemma sum_sexticExponent {n : ℕ} (a : SexticMonomial n) :
    (sexticExponent a).sum (fun _ k => k) = sexticDegree a := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_three, sexticExponent_zero, sexticExponent_one,
    sexticExponent_two, sexticDegree]

noncomputable def sexticPolynomial {n : ℕ} (a : SexticMonomial n) : MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.monomial (sexticExponent a) 1

noncomputable def sexticCombination {n : ℕ} (v : SexticMonomial n → ℤ) :
    MvPolynomial (Fin 3) ℤ :=
  ∑ a, MvPolynomial.monomial (sexticExponent a) (v a)

lemma coeff_sexticCombination {n : ℕ} (v : SexticMonomial n → ℤ) (a : SexticMonomial n) :
    (sexticCombination v).coeff (sexticExponent a) = v a := by
  classical
  simp [sexticCombination, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    sexticExponent_injective.eq_iff]

lemma sexticCombination_ne_zero {n : ℕ} (v : SexticMonomial n → ℤ) (hv : ∃ a, v a ≠ 0) :
    sexticCombination v ≠ 0 := by
  obtain ⟨a, ha⟩ := hv
  intro h
  have hcoeff := congrArg (MvPolynomial.coeff (sexticExponent a)) h
  rw [coeff_sexticCombination, MvPolynomial.coeff_zero] at hcoeff
  exact ha hcoeff

lemma degreeOf_sexticCombination {n : ℕ} (v : SexticMonomial n → ℤ) :
    (sexticCombination v).degreeOf 2 ≤ 5 := by
  classical
  apply (MvPolynomial.degreeOf_sum_le 2 _ _).trans
  apply Finset.sup_le
  intro a _
  by_cases ha : v a = 0
  · simp [ha]
  · rw [MvPolynomial.degreeOf_monomial_eq _ _ ha, sexticExponent_two]
    exact Nat.sub_le _ _

lemma totalDegree_sexticCombination {n : ℕ} (v : SexticMonomial n → ℤ) :
    (sexticCombination v).totalDegree ≤ n + 5 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a _
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans
    ((sum_sexticExponent a).le.trans (sexticDegree_le a))

lemma eval_sexticPolynomial {n : ℕ} (a : SexticMonomial n) (z : Fin 3 → ℤ) :
    MvPolynomial.eval z (sexticPolynomial a) =
      z 0 ^ a.2.val.1 * z 1 ^ a.2.val.2 * z 2 ^ (5 - a.1.val) := by
  rw [sexticPolynomial, MvPolynomial.eval_monomial, one_mul,
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.prod_univ_three, sexticExponent_zero, sexticExponent_one, sexticExponent_two]

lemma eval_sexticCombination {n : ℕ} (v : SexticMonomial n → ℤ) (z : Fin 3 → ℤ) :
    MvPolynomial.eval z (sexticCombination v) =
      ∑ a, v a * MvPolynomial.eval z (sexticPolynomial a) := by
  simp [sexticCombination, sexticPolynomial, MvPolynomial.eval_monomial]

lemma abs_eval_sexticPolynomial_le {n : ℕ} (a : SexticMonomial n) (z : Fin 3 → ℤ)
    (B : ℝ) (hB : 0 ≤ B) (hz : ∀ k, |(z k : ℝ)| ≤ B) :
    |(MvPolynomial.eval z (sexticPolynomial a) : ℝ)| ≤ B ^ sexticDegree a := by
  rw [eval_sexticPolynomial]
  push_cast
  rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_pow]
  calc
    _ ≤ B ^ a.2.val.1 * B ^ a.2.val.2 * B ^ (5 - a.1.val) := by
      gcongr
      · exact hz 0
      · exact hz 1
      · exact hz 2
    _ = _ := by rw [sexticDegree, pow_add, pow_add]

#print axioms sexticCombination_ne_zero
-- 'Erdos477.Counting.sexticCombination_ne_zero' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
