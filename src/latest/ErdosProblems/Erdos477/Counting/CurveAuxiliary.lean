/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An auxiliary polynomial of fixed degree on one smooth plane-curve residue class.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveEvaluation
import ErdosProblems.Erdos477.Counting.DeterminantKernel

namespace Erdos477.Counting

open scoped BigOperators

lemma exists_curve_combination_of_det_eq_zero (d n : ℕ) (S : Finset (Fin 2 → ℤ))
    (hdet : ∀ z : Fin (Fintype.card (CurveMonomial d n)) → Fin 2 → ℤ,
      (∀ j, z j ∈ S) → (curveEvaluationMatrix d n z).det = 0) :
    ∃ v : CurveMonomial d n → ℤ, (∃ a, v a ≠ 0) ∧
      ∀ z ∈ S, MvPolynomial.eval z (curveCombination v) = 0 := by
  classical
  let s := Fintype.card (CurveMonomial d n)
  let V : ↥S → Fin s → ℤ := fun z i =>
    MvPolynomial.eval z.val (curvePolynomial (curveIndex d n i))
  have hdet' (f : Fin s → ↥S) : (Matrix.of fun i j => V (f i) j).det = 0 := by
    change (curveEvaluationMatrix d n (fun j => (f j).val)).transpose.det = 0
    rw [Matrix.det_transpose]
    exact hdet _ (fun j => (f j).property)
  obtain ⟨w, ⟨i, hi⟩, hw⟩ := exists_integer_kernel_of_det_eq_zero V hdet'
  let v : CurveMonomial d n → ℤ := fun a => w ((curveIndex d n).symm a)
  refine ⟨v, ⟨curveIndex d n i, by simpa only [v, Equiv.symm_apply_apply] using hi⟩, ?_⟩
  intro z hz
  rw [eval_curveCombination]
  simp_rw [← eval_curvePolynomial]
  have hsum := (curveIndex d n).sum_comp
    (fun a => v a * MvPolynomial.eval z (curvePolynomial a))
  rw [← hsum]
  simpa only [v, Equiv.symm_apply_apply, V] using hw ⟨z, hz⟩

/-- This degree bound is independent of the height and the coefficients of
the original curve. The degree parameter n is chosen in `CurveDegreeChoice`. -/
theorem exists_curve_auxiliary_of_congruence (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hεn : 1 ≤ ε * ((n : ℝ) - 1))
    (B : ℝ) (hB : 1 ≤ B) (hlarge : 2 * Real.log (d * n : ℕ) < Real.log B)
    (q : ℕ) (hq : 0 < q) (hqB : (1 / (d : ℝ) + ε) * Real.log B ≤ Real.log q)
    (P : MvPolynomial (Fin 2) ℤ) (hPdegree : P.degreeOf 0 = d)
    (a : Fin 2 → ℤ) (S : Finset (Fin 2 → ℤ))
    (hcop : IsCoprime (q : ℤ) (MvPolynomial.eval a (MvPolynomial.pderiv 0 P)))
    (hroot : ∀ z ∈ S, MvPolynomial.eval z P = 0)
    (hclass : ∀ z ∈ S, ∀ k, (q : ℤ) ∣ z k - a k)
    (hheight : ∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) :
    ∃ Q : MvPolynomial (Fin 2) ℤ, Q ≠ 0 ∧ Q.degreeOf 0 ≤ d - 1 ∧
      Q.totalDegree ≤ d + n - 2 ∧ ¬ P ∣ Q ∧ ∀ z ∈ S, MvPolynomial.eval z Q = 0 := by
  have hdet (z : Fin (Fintype.card (CurveMonomial d n)) → Fin 2 → ℤ) (hz : ∀ j, z j ∈ S) :
      (curveEvaluationMatrix d n z).det = 0 :=
    curveEvaluationMatrix_det_eq_zero d n hd hn ε hε hεn B hB hlarge q hq hqB P a z hcop
      (fun j => hroot (z j) (hz j)) (fun j => hclass (z j) (hz j))
      (fun j => hheight (z j) (hz j))
  obtain ⟨v, hv, hzero⟩ := exists_curve_combination_of_det_eq_zero d n S hdet
  exact ⟨curveCombination v, curveCombination_ne_zero v hv, degreeOf_curveCombination v,
    totalDegree_curveCombination v, curve_not_dvd_combination hd P hPdegree v hv, hzero⟩

#print axioms exists_curve_auxiliary_of_congruence
-- 'Erdos477.Counting.exists_curve_auxiliary_of_congruence' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
