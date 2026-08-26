/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A three-column polynomial Wronskian and its sharp common-degree bound.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.ResultantDegree

namespace Erdos477.Geometry

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

noncomputable def eulerStrip (D : ℕ) (p : K[X]) : K[X] :=
  X * derivative p - C (D : K) * p

lemma coeff_eulerStrip (D k : ℕ) (p : K[X]) :
    (eulerStrip D p).coeff k = ((k : K) - D) * p.coeff k := by
  cases k with
  | zero => simp [eulerStrip]
  | succ k =>
      simp only [eulerStrip, coeff_sub, coeff_X_mul, coeff_derivative, coeff_C_mul]
      push_cast
      ring

lemma natDegree_eulerStrip_le (D : ℕ) (p : K[X]) (hp : p.natDegree ≤ D) :
    (eulerStrip D p).natDegree ≤ D - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_eulerStrip]
  by_cases hkD : k = D
  · subst k
    simp
  · have hDk : D < k := by omega
    rw [coeff_eq_zero_of_natDegree_lt (hp.trans_lt hDk), mul_zero]

noncomputable def wronskianThree (f : Fin 3 → K[X]) : K[X] :=
  Matrix.det (Matrix.of
    ![f, (fun j => derivative (f j)), (fun j => derivative (derivative (f j)))])

lemma wronskianThree_cycle (p q r : K[X]) :
    wronskianThree ![q, r, p] = wronskianThree ![p, q, r] := by
  simp [wronskianThree, Matrix.det_fin_three]
  ring

lemma wronskianThree_swap (p q r : K[X]) :
    wronskianThree ![q, p, r] = -wronskianThree ![p, q, r] := by
  simp [wronskianThree, Matrix.det_fin_three]
  ring

lemma wronskianThree_neg_sum (p q r : K[X]) :
    wronskianThree ![q, r, -(p + q + r)] = -wronskianThree ![p, q, r] := by
  simp [wronskianThree, Matrix.det_fin_three]
  ring

lemma eulerStrip_wronskian_identity (D : ℕ) (f : Fin 3 → K[X]) :
    Matrix.det (Matrix.of ![f, (fun j => eulerStrip D (f j)),
      (fun j => eulerStrip (D - 1) (eulerStrip D (f j)))]) = X ^ 3 * wronskianThree f := by
  simp [wronskianThree, Matrix.det_fin_three, eulerStrip]
  ring

/-- Three polynomial columns of degree at most `D` have Wronskian degree at
most `3D-6`. The six-degree loss includes cancellation of the top coefficients. -/
theorem natDegree_wronskianThree_le (D : ℕ) (hD : 2 ≤ D) (f : Fin 3 → K[X])
    (hf : ∀ j, (f j).natDegree ≤ D) : (wronskianThree f).natDegree ≤ 3 * D - 6 := by
  let M : Matrix (Fin 3) (Fin 3) K[X] :=
    Matrix.of ![f, (fun j => eulerStrip D (f j)),
      (fun j => eulerStrip (D - 1) (eulerStrip D (f j)))]
  have hdet : M.det.natDegree ≤ 3 * D - 3 := by
    apply natDegree_det_le_of_weights M ![D, D - 1, D - 2] 0 (3 * D - 3)
    · simp only [Fin.sum_univ_three]
      change D + (D - 1) + (D - 2) ≤ 3 * D - 3 + (0 + 0 + 0)
      omega
    · intro i j _
      fin_cases i
      · simpa [M] using hf j
      · simpa [M] using natDegree_eulerStrip_le D (f j) (hf j)
      · simpa [M, Nat.sub_sub] using natDegree_eulerStrip_le (D - 1) (eulerStrip D (f j))
          (natDegree_eulerStrip_le D (f j) (hf j))
  rw [show M.det = X ^ 3 * wronskianThree f from
    eulerStrip_wronskian_identity D f] at hdet
  by_cases hzero : wronskianThree f = 0
  · simp [hzero]
  · rw [natDegree_mul (pow_ne_zero 3 X_ne_zero) hzero, natDegree_X_pow] at hdet
    omega

lemma prod_dvd_det_of_dvd_column {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (a : ι → R) (h : ∀ i j, a j ∣ M i j) : (∏ j, a j) ∣ M.det := by
  choose Q hQ using h
  have hM : M = Matrix.of (fun i j => a j * Q i j) := by ext i j; exact hQ i j
  rw [hM]
  change (∏ j, a j) ∣ (Matrix.of (fun i j => a j * (Matrix.of Q) i j)).det
  rw [Matrix.det_mul_row a (Matrix.of Q)]
  exact dvd_mul_right _ _

/-- Each column contributes its undifferentiated factor to the Wronskian,
after at most two derivatives. -/
theorem prod_pow_dvd_wronskianThree (f : Fin 3 → K[X]) (n : ℕ) :
    (∏ j, f j ^ (n - 2)) ∣ wronskianThree (fun j => f j ^ n) := by
  apply prod_dvd_det_of_dvd_column
  intro i j
  have hder (m : ℕ) (hm : m ≤ 2) : f j ^ (n - 2) ∣ derivative^[m] (f j ^ n) :=
    (pow_dvd_pow (f j) (Nat.sub_le_sub_left hm n)).trans
      (pow_sub_dvd_iterate_derivative_pow (f j) n m)
  fin_cases i
  · simpa using hder 0 (by decide)
  · simpa using hder 1 (by decide)
  · simpa using hder 2 (by decide)

#print axioms natDegree_wronskianThree_le
-- 'Erdos477.Geometry.natDegree_wronskianThree_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
