/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An auxiliary polynomial on every bounded part of a nonzero affine sextic surface.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.DegreeChoice
import ErdosProblems.Erdos477.Counting.DeterminantKernel
import ErdosProblems.Erdos477.Counting.IntegerBox

namespace Erdos477.Counting

open scoped BigOperators

lemma exists_sextic_combination_of_det_eq_zero (n : ℕ) (S : Finset (Fin 3 → ℤ))
    (hdet : ∀ z : Fin (Fintype.card (SexticMonomial n)) → Fin 3 → ℤ,
      (∀ j, z j ∈ S) → (sexticEvaluationMatrix n z).det = 0) :
    ∃ v : SexticMonomial n → ℤ, (∃ a, v a ≠ 0) ∧
      ∀ z ∈ S, MvPolynomial.eval z (sexticCombination v) = 0 := by
  classical
  let s := Fintype.card (SexticMonomial n)
  let V : ↥S → Fin s → ℤ := fun z i =>
    MvPolynomial.eval z.val (sexticPolynomial (sexticIndex n i))
  have hdet' (f : Fin s → ↥S) : (Matrix.of fun i j => V (f i) j).det = 0 := by
    change (sexticEvaluationMatrix n (fun j => (f j).val)).transpose.det = 0
    rw [Matrix.det_transpose]
    exact hdet _ (fun j => (f j).property)
  obtain ⟨w, ⟨i, hi⟩, hw⟩ := exists_integer_kernel_of_det_eq_zero V hdet'
  let v : SexticMonomial n → ℤ := fun a => w ((sexticIndex n).symm a)
  refine ⟨v, ⟨sexticIndex n i, by simpa only [v, Equiv.symm_apply_apply] using hi⟩, ?_⟩
  intro z hz
  rw [eval_sexticCombination]
  have hsum := (sexticIndex n).sum_comp
    (fun a => v a * MvPolynomial.eval z (sexticPolynomial a))
  rw [← hsum]
  simpa only [v, Equiv.symm_apply_apply, V] using hw ⟨z, hz⟩

/-- For fixed nonzero `c`, all integral points of height at most `B` on the
sextic surface lie on another nonzero polynomial of degree `O_c(B^(41/100))`.
The new polynomial is not a multiple of the surface equation. -/
theorem exists_sextic_auxiliary_polynomial (c : ℤ) (hc : c ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ B : ℝ, 1 ≤ B →
      ∃ P : MvPolynomial (Fin 3) ℤ, P ≠ 0 ∧ P.degreeOf 2 ≤ 5 ∧
        (P.totalDegree : ℝ) ≤ K * B ^ ((41 : ℝ) / 100) ∧
        ¬ sexticSurface c ∣ P ∧
        ∀ z : Fin 3 → ℤ, z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c →
          (∀ k, |(z k : ℝ)| ≤ B) → MvPolynomial.eval z P = 0 := by
  classical
  obtain ⟨C, hC, hvanish⟩ := exists_sextic_determinant_vanishing c hc
  obtain ⟨K, hK, hdegree⟩ := exists_sextic_degree_bound C hC
  refine ⟨K, hK, ?_⟩
  intro B hB
  obtain ⟨n, _, hn, hsmall⟩ := hdegree B hB
  have hdet (z : Fin (Fintype.card (SexticMonomial n)) → Fin 3 → ℤ)
      (hz : ∀ j, z j ∈ sexticBox c B) : (sexticEvaluationMatrix n z).det = 0 := by
    have hpoints (j) := (mem_sexticBox c B (z j)).mp (hz j)
    exact hvanish n B (by linarith) hsmall z
      (fun j => (hpoints j).1) (fun j => (hpoints j).2)
  obtain ⟨v, hv, heval⟩ := exists_sextic_combination_of_det_eq_zero n (sexticBox c B) hdet
  refine ⟨sexticCombination v, sexticCombination_ne_zero v hv,
    degreeOf_sexticCombination v, ?_, sexticSurface_not_dvd_combination c v hv, ?_⟩
  · have hd : ((sexticCombination v).totalDegree : ℝ) ≤ (n : ℝ) + 5 := by
      exact_mod_cast totalDegree_sexticCombination v
    exact hd.trans hn
  · intro z hz hheight
    exact heval z ((mem_sexticBox c B z).mpr ⟨hz, hheight⟩)

#print axioms exists_sextic_auxiliary_polynomial
-- 'Erdos477.Counting.exists_sextic_auxiliary_polynomial' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
