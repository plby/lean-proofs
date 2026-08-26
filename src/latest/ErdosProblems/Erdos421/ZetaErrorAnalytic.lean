import ErdosProblems.Erdos421.ZetaErrorTerms
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Holomorphy of the sum--integral remainder on the positive half-plane -/

namespace Erdos421

theorem zetaErrorTerm_uniform_norm_le {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (n : ℕ) {s : ℂ} (hs : a < s.re) (hsB : ‖s‖ < B) :
    ‖zetaErrorTerm n s‖ ≤ (B + 1) * B * ((n + 1 : ℕ) : ℝ) ^ (-a - 1) := by
  have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hp := Real.rpow_le_rpow_of_exponent_le hn (show -s.re - 1 ≤ -a - 1 by linarith)
  have hsnorm : ‖s - 1‖ ≤ B + 1 := by
    have ht := norm_sub_le s 1
    rw [norm_one] at ht
    linarith
  calc
    _ ≤ ‖s - 1‖ * ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
      zetaErrorTerm_norm_le n (ha.trans hs)
    _ ≤ (B + 1) * B * ((n + 1 : ℕ) : ℝ) ^ (-a - 1) := by
      apply mul_le_mul (mul_le_mul hsnorm hsB.le (norm_nonneg _) (by positivity)) hp
      · positivity
      · positivity

theorem differentiableOn_tsum_zetaErrorTerm_bounded {a B : ℝ} (ha : 0 < a) (hB : 0 < B) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∑' n : ℕ, zetaErrorTerm n s)
      {s : ℂ | a < s.re ∧ ‖s‖ < B} := by
  have hp : Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-a - 1)) :=
    (summable_nat_add_iff 1 (f := fun n : ℕ ↦ (n : ℝ) ^ (-a - 1))).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  have hU : IsOpen {s : ℂ | a < s.re ∧ ‖s‖ < B} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  exact Complex.differentiableOn_tsum_of_summable_norm (hp.mul_left ((B + 1) * B))
    (fun n ↦ (differentiable_zetaErrorTerm n).differentiableOn) hU
    (fun n s hs ↦ zetaErrorTerm_uniform_norm_le ha hB n hs.1 hs.2)

theorem differentiableAt_tsum_zetaErrorTerm {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun s : ℂ ↦ ∑' n : ℕ, zetaErrorTerm n s) s := by
  have hB : 0 < ‖s‖ + 1 := by positivity
  have ha : 0 < s.re / 2 := by linarith
  have hU : IsOpen {z : ℂ | s.re / 2 < z.re ∧ ‖z‖ < ‖s‖ + 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  exact (differentiableOn_tsum_zetaErrorTerm_bounded ha hB).differentiableAt
    (hU.mem_nhds ⟨by linarith, by linarith⟩)

noncomputable def zetaErrorSum (s : ℂ) : ℂ := 1 + ∑' n : ℕ, zetaErrorTerm n s

theorem differentiableOn_zetaErrorSum :
    DifferentiableOn ℂ zetaErrorSum {s : ℂ | 0 < s.re} := by
  intro s hs
  exact ((differentiableAt_const 1).add
    (differentiableAt_tsum_zetaErrorTerm hs)).differentiableWithinAt

end Erdos421
