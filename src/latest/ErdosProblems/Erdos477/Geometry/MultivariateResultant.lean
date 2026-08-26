/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Total degree bounds for a resultant with multivariate polynomial coefficients.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

open scoped BigOperators Polynomial

variable {ι σ K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

lemma totalDegree_det_le_of_weights (M : Matrix ι ι (MvPolynomial σ K))
    (a b : ι → ℕ) (N : ℕ) (hsum : (∑ i, a i) ≤ N + ∑ j, b j)
    (hentry : ∀ i j, M i j ≠ 0 → (M i j).totalDegree + b j ≤ a i) :
    M.det.totalDegree ≤ N := by
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  by_cases hzero : (∏ i, M (e i) i) = 0
  · rw [hzero, smul_zero, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  have hne (i) : M (e i) i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hzero) i (Finset.mem_univ i)
  have hsum' := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hentry (e i) i (hne i))
  rw [Finset.sum_add_distrib, Equiv.sum_comp] at hsum'
  rw [Units.smul_def]
  apply (MvPolynomial.totalDegree_smul_le _ _).trans
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  omega

theorem totalDegree_resultant_le (f g : (MvPolynomial σ K)[X]) (m n d e : ℕ)
    (hm : m ≤ d) (hn : n ≤ e)
    (hf : ∀ j, f.coeff j ≠ 0 → (f.coeff j).totalDegree + j ≤ d)
    (hg : ∀ j, g.coeff j ≠ 0 → (g.coeff j).totalDegree + j ≤ e) :
    (f.resultant g m n).totalDegree ≤ d * e := by
  let a : Fin (m + n) → ℕ := fun i =>
    Fin.addCases (fun j : Fin m => e + j.val) (fun j : Fin n => d + j.val) i
  let b : Fin (m + n) → ℕ := fun j => j.val
  have hcross : m * e + n * d ≤ d * e + m * n := by
    rw [← Nat.sub_add_cancel hm, ← Nat.sub_add_cancel hn]
    nlinarith
  have hsum : (∑ i, a i) ≤ d * e + ∑ j, b j := by
    simp only [a, b, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
      Fin.val_castAdd, Fin.val_natAdd, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    nlinarith only [hcross]
  rw [Polynomial.resultant, ← Matrix.det_transpose]
  apply totalDegree_det_le_of_weights _ a b (d * e) hsum
  intro i j hne
  induction i using Fin.addCases with
  | left i =>
      simp only [Polynomial.sylvester, Matrix.transpose_apply, Matrix.of_apply,
        Fin.addCases_left] at hne ⊢
      split_ifs with hij
      · have hcoeff : g.coeff (j.val - i.val) ≠ 0 := by simpa only [if_pos hij] using hne
        have hd := hg _ hcoeff
        have hlow := hij.1
        simp only [a, b, Fin.addCases_left]
        omega
      · exact (hne (if_neg hij)).elim
  | right i =>
      simp only [Polynomial.sylvester, Matrix.transpose_apply, Matrix.of_apply,
        Fin.addCases_right] at hne ⊢
      split_ifs with hij
      · have hcoeff : f.coeff (j.val - i.val) ≠ 0 := by simpa only [if_pos hij] using hne
        have hd := hf _ hcoeff
        have hlow := hij.1
        simp only [a, b, Fin.addCases_right]
        omega
      · exact (hne (if_neg hij)).elim

#print axioms totalDegree_resultant_le
-- 'Erdos477.Geometry.totalDegree_resultant_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
