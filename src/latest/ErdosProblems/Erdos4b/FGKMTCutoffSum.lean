/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTensorSum
import ErdosProblems.Erdos4b.FGKMTCutoffTest

/-!
# The literal sieve sum with a sum-dependent cutoff

The extra real parameter records a frozen sum of coordinates. Splitting
the first coordinate leaves precisely the translated test function
whose smooth error was bounded in `FGKMTCutoffTest`.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def cutoffSieveSum (M : ℕ) (g : ℕ → ℝ) (R j : ℕ) (G Φ : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ e : Fin j → Fin (R + 1),
    (∏ i, G (Real.log (e i).val / Real.log R)) *
      Φ (u + ∑ i, Real.log (e i).val / Real.log R) *
        roughSieveWeight M g (∏ i, (e i).val)

theorem cutoffSieveSum_zero (M R : ℕ) (g : ℕ → ℝ) (G Φ : ℝ → ℝ) (u : ℝ) :
    cutoffSieveSum M g R 0 G Φ u = Φ u := by
  simp [cutoffSieveSum, roughSieveWeight]

theorem cutoffSieveSum_one (M R j : ℕ) (g : ℕ → ℝ) (G : ℝ → ℝ) (u : ℝ) :
    cutoffSieveSum M g R j G (fun _ => 1) u = tensorSieveSum M g R j G := by
  simp [cutoffSieveSum, tensorSieveSum]

theorem cutoffSieveSum_succ (M R j : ℕ) (g : ℕ → ℝ) (G Φ : ℝ → ℝ) (u : ℝ) :
    cutoffSieveSum M g R (j + 1) G Φ u =
      ∑ e : Fin j → Fin (R + 1), (∏ i, G (Real.log (e i).val / Real.log R)) *
        (∑ n ∈ Finset.Icc 0 R,
          cutoffTest G Φ (u + ∑ i, Real.log (e i).val / Real.log R)
              (Real.log n / Real.log R) *
            roughSieveWeight M g ((∏ i, (e i).val) * n)) := by
  classical
  unfold cutoffSieveSum
  rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => Fin (R + 1))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum, ← sum_fin_succ_eq_sum_Icc]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, cutoffTest]
  rw [Nat.mul_comm n.val]
  have harg : u + (Real.log n.val / Real.log R + ∑ i, Real.log (e i).val / Real.log R) =
      (u + ∑ i, Real.log (e i).val / Real.log R) + Real.log n.val / Real.log R := by ring
  rw [harg]
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.cutoffSieveSum_succ
