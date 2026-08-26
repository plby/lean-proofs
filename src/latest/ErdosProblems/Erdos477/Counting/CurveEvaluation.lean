/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Vanishing of bounded-degree evaluation determinants in a smooth curve residue class.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveCoordinates
import ErdosProblems.Erdos477.Counting.CurveDegreeChoice
import ErdosProblems.Erdos477.Counting.HeightDeterminant

namespace Erdos477.Counting

open scoped BigOperators

noncomputable def curveIndex (d n : ℕ) :
    Fin (Fintype.card (CurveMonomial d n)) ≃ CurveMonomial d n :=
  (Fintype.equivFin (CurveMonomial d n)).symm

noncomputable def curveEvaluationMatrix (d n : ℕ)
    (z : Fin (Fintype.card (CurveMonomial d n)) → Fin 2 → ℤ) :
    Matrix (Fin (Fintype.card (CurveMonomial d n)))
      (Fin (Fintype.card (CurveMonomial d n))) ℤ :=
  Matrix.of fun i j => MvPolynomial.eval (z j) (curvePolynomial (curveIndex d n i))

lemma log_pow_le_log_abs_of_dvd (q : ℕ) (hq : 0 < q) (N : ℕ) (D : ℤ) (hD : D ≠ 0)
    (hdiv : (q : ℤ) ^ N ∣ D) : (N : ℝ) * Real.log q ≤ Real.log |(D : ℝ)| := by
  have hle : (q : ℤ) ^ N ≤ |D| :=
    Int.le_of_dvd (abs_pos.mpr hD) ((dvd_abs _ _).mpr hdiv)
  have hle' : (q : ℝ) ^ N ≤ |(D : ℝ)| := by exact_mod_cast hle
  have h := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) N) hle'
  simpa only [Real.log_pow] using h

/-- The degree parameter depends only on d and epsilon. Inside a sufficiently
large smooth residue class, every sampled evaluation determinant vanishes. -/
theorem curveEvaluationMatrix_det_eq_zero (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hεn : 1 ≤ ε * ((n : ℝ) - 1))
    (B : ℝ) (hB : 1 ≤ B) (hlarge : 2 * Real.log (d * n : ℕ) < Real.log B)
    (q : ℕ) (hq : 0 < q) (hqB : (1 / (d : ℝ) + ε) * Real.log B ≤ Real.log q)
    (P : MvPolynomial (Fin 2) ℤ) (a : Fin 2 → ℤ)
    (z : Fin (Fintype.card (CurveMonomial d n)) → Fin 2 → ℤ)
    (hcop : IsCoprime (q : ℤ) (MvPolynomial.eval a (MvPolynomial.pderiv 0 P)))
    (hroot : ∀ j, MvPolynomial.eval (z j) P = 0)
    (hclass : ∀ j k, (q : ℤ) ∣ z j k - a k)
    (hheight : ∀ j k, |(z j k : ℝ)| ≤ B) : (curveEvaluationMatrix d n z).det = 0 := by
  let s := Fintype.card (CurveMonomial d n)
  have hs : 0 < s := by
    dsimp only [s]
    rw [card_curveMonomial]
    exact Nat.mul_pos (by omega) (by omega)
  have hB0 : 0 < B := by linarith
  by_contra hD
  let M := curveEvaluationMatrix d n z
  let φ : ℤ →+* ℝ := Int.castRingHom ℝ
  let Mr := M.map φ
  have hmap : (M.det : ℝ) = Mr.det := φ.map_det M
  have hMr : Mr.det ≠ 0 := by rw [← hmap]; exact_mod_cast hD
  have hentry (i j : Fin s) : |Mr i j| ≤ B ^ curveDegree (curveIndex d n i) :=
    abs_eval_curvePolynomial_le (curveIndex d n i) (z j) B (hheight j)
  have hupp := log_abs_det_le hs Mr hMr B hB0
    (fun i => curveDegree (curveIndex d n i)) hentry
  have hw : (∑ i : Fin s, curveDegree (curveIndex d n i)) =
      ∑ a : CurveMonomial d n, curveDegree a := (curveIndex d n).sum_comp curveDegree
  rw [← hmap, hw] at hupp
  have hdiv := pow_dvd_curve_mv_eval_det_of_congruence P
    (fun i => curvePolynomial (curveIndex d n i)) (q : ℤ) a z hcop hroot hclass
  have hlow := log_pow_le_log_abs_of_dvd q hq (s.choose 2) M.det hD hdiv
  have hsize := curve_log_determinant_inequality d n hd hn ε hε hεn B q hB hlarge hqB
  have hsval : s = d * n := card_curveMonomial d n
  rw [hsval] at hupp hlow
  exact (not_lt_of_ge hupp) (hsize.trans_le hlow)

#print axioms curveEvaluationMatrix_det_eq_zero
-- 'Erdos477.Counting.curveEvaluationMatrix_det_eq_zero' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
