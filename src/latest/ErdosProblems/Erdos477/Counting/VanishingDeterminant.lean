/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Combining global and archimedean bounds to force sextic evaluation determinants to vanish.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.OptimizedDeterminant
import ErdosProblems.Erdos477.Counting.HeightDeterminant
import ErdosProblems.Erdos477.Counting.SurfacePolynomial

namespace Erdos477.Counting

open scoped BigOperators

noncomputable def sexticIndex (n : ℕ) :
    Fin (Fintype.card (SexticMonomial n)) ≃ SexticMonomial n :=
  (Fintype.equivFin (SexticMonomial n)).symm

def sexticWeight (n : ℕ) : ℕ := ∑ a : SexticMonomial n, sexticDegree a

noncomputable def sexticEvaluationMatrix (n : ℕ)
    (z : Fin (Fintype.card (SexticMonomial n)) → Fin 3 → ℤ) :
    Matrix (Fin (Fintype.card (SexticMonomial n))) (Fin (Fintype.card (SexticMonomial n))) ℤ :=
  Matrix.of fun i j => MvPolynomial.eval (z j) (sexticPolynomial (sexticIndex n i))

/-- The determinant vanishes whenever the explicit size inequality holds.
The constant in that inequality has already been proved to exist from local
expansions, finite-field counting, and prime sums. -/
theorem exists_sextic_determinant_vanishing (c : ℤ) (hc : c ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (B : ℝ), 0 < B →
      let s := Fintype.card (SexticMonomial n)
      (s : ℝ) * Real.log s + sexticWeight n * Real.log B <
        Real.sqrt 2 / 3 * s * Real.sqrt s * Real.log s - C * s * Real.sqrt s →
      ∀ (z : Fin s → Fin 3 → ℤ),
      (∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c) →
      (∀ j k, |(z j k : ℝ)| ≤ B) →
      (sexticEvaluationMatrix n z).det = 0 := by
  obtain ⟨C, hC, hbound⟩ := exists_global_det_lower_sqrt c hc
  refine ⟨C, hC, ?_⟩
  intro n B hB s hsmall z hz hheight
  by_contra hD
  have hs : 0 < s := by
    dsimp only [s]
    rw [card_sexticMonomial]
    omega
  let M := sexticEvaluationMatrix n z
  let φ : ℤ →+* ℝ := Int.castRingHom ℝ
  let Mr : Matrix (Fin s) (Fin s) ℝ := M.map φ
  have hmap : (M.det : ℝ) = Mr.det := φ.map_det M
  have hMr : Mr.det ≠ 0 := by
    rw [← hmap]
    exact_mod_cast hD
  have hentry (i j : Fin s) : |Mr i j| ≤ B ^ sexticDegree (sexticIndex n i) :=
    abs_eval_sexticPolynomial_le (sexticIndex n i) (z j) B hB.le (hheight j)
  have hw : (∑ i : Fin s, sexticDegree (sexticIndex n i)) = sexticWeight n :=
    (sexticIndex n).sum_comp sexticDegree
  have hupp := log_abs_det_le hs Mr hMr B hB
    (fun i => sexticDegree (sexticIndex n i)) hentry
  rw [← hmap, hw] at hupp
  have hlow := hbound s hs z hz (fun i => sexticPolynomial (sexticIndex n i)) hD
  have hcontra := hsmall.trans_le hlow
  exact (not_lt_of_ge hupp) hcontra

#print axioms exists_sextic_determinant_vanishing
-- 'Erdos477.Counting.exists_sextic_determinant_vanishing' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
