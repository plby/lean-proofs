/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTRoughSupport
import ErdosProblems.Erdos4b.FGKMTLocalTelescoping
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite box sums for the multivariate sieve

Every coordinate ranges over the literal integers from zero to `R`.
Zero coordinates have zero arithmetic weight; the product weight also
enforces squarefreeness and pairwise coprimality. No additional tuples
are counted by encoding the range using `Fin (R + 1)`.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def tensorSieveSum (M : ℕ) (g : ℕ → ℝ) (R j : ℕ) (G : ℝ → ℝ) : ℝ :=
  ∑ e : Fin j → Fin (R + 1),
    (∏ i, G (Real.log (e i).val / Real.log R)) *
      roughSieveWeight M g (∏ i, (e i).val)

theorem tensorSieveSum_zero (M R : ℕ) (g : ℕ → ℝ) (G : ℝ → ℝ) :
    tensorSieveSum M g R 0 G = 1 := by
  simp [tensorSieveSum, roughSieveWeight]

theorem log_coordinate_mem_unit {R : ℕ} (hR : 1 < R) (n : Fin (R + 1)) :
    Real.log n.val / Real.log R ∈ Set.Icc (0 : ℝ) 1 := by
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  by_cases hn : n.val = 0
  · simp [hn]
  · have hnpos : 0 < n.val := Nat.pos_of_ne_zero hn
    have hlogn : 0 ≤ Real.log n.val := Real.log_nonneg (by exact_mod_cast hnpos)
    have hlogle : Real.log n.val ≤ Real.log R :=
      Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast Nat.le_of_lt_succ n.isLt)
    exact ⟨div_nonneg hlogn hlogR.le, (div_le_one hlogR).mpr hlogle⟩

theorem tensorSieveSum_nonneg {M R j : ℕ} (hR : 1 < R) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → 0 ≤ g p) {G : ℝ → ℝ}
    (hG : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) : 0 ≤ tensorSieveSum M g R j G := by
  apply Finset.sum_nonneg
  intro e he
  exact mul_nonneg
    (Finset.prod_nonneg (fun i hi => hG _ (log_coordinate_mem_unit hR (e i))))
    (roughSieveWeight_nonneg M g hg _)

theorem tensor_coordinate_product_le {R j : ℕ} (e : Fin j → Fin (R + 1)) :
    (∏ i, (e i).val) ≤ R ^ j := by
  calc
    _ ≤ ∏ _i : Fin j, R := Finset.prod_le_prod' (fun i _ => Nat.le_of_lt_succ (e i).isLt)
    _ = _ := by simp

theorem sum_fin_succ_eq_sum_Icc (R : ℕ) (f : ℕ → ℝ) :
    (∑ n : Fin (R + 1), f n.val) = ∑ n ∈ Finset.Icc 0 R, f n := by
  rw [Fin.sum_univ_eq_sum_range, Nat.range_succ_eq_Icc_zero]

theorem tensorSieveSum_succ (M R j : ℕ) (g : ℕ → ℝ) (G : ℝ → ℝ) :
    tensorSieveSum M g R (j + 1) G =
      ∑ e : Fin j → Fin (R + 1), (∏ i, G (Real.log (e i).val / Real.log R)) *
        (∑ n ∈ Finset.Icc 0 R,
          G (Real.log n / Real.log R) * roughSieveWeight M g ((∏ i, (e i).val) * n)) := by
  classical
  unfold tensorSieveSum
  rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => Fin (R + 1))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum, ← sum_fin_succ_eq_sum_Icc]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Nat.mul_comm n.val]
  ring

theorem multivariateSieveConstant_zero (M : ℕ) (g : ℕ → ℝ) :
    multivariateSieveConstant M g 0 = 1 := by simp [multivariateSieveConstant]

theorem multivariateSieveConstant_succ_shift (M j : ℕ) (g : ℕ → ℝ) :
    multivariateSieveConstant M g (j + 1) =
      sieveMainConstant M g * multivariateSieveConstant M (fun p => g p + 1) j := by
  unfold multivariateSieveConstant
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  congr 1
  funext p
  push_cast
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.tensorSieveSum_succ
