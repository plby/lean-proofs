import ErdosProblems.Erdos1148.HighCuspVisitCover
import ErdosProblems.Erdos1148.CuspVisitTimePatterns

/-! # A refined measurable cover with arbitrarily small overhead and fixed cusp endpoints -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_refined_local_cusp_cover {η ε : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) (hε : 0 < ε) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (E : Set SL(2, ℝ)) (A : ℝ), LiftForwardClose η 0 E →
      ∃ (N : ℕ) (B : Fin N → Set ModularOrbitSpace),
        (N : ℝ) ≤ C * Real.exp ((1 + ε) * n - A / 2) ∧
        (∀ i, IsCompact (B i)) ∧ (∀ i, MeasurableSet (B i)) ∧
        modularMk '' highCuspVisitsWithBoundedEndpoints H n A E ⊆ ⋃ i, B i ∧
        ∀ i, B i ×ˢ B i ⊆ modularForwardBowenPairs (32 * η) ((n : ℝ) + 4 * Real.log H) := by
  obtain ⟨K, hK, hcover⟩ := exists_high_cusp_visit_lift_cover hηpos hη
  obtain ⟨Hp, Cp, hHp, hCp, hpatterns⟩ :=
    exists_cusp_visit_time_patterns_small_rate (half_pos hε)
  let R := (2 * Real.log K + 1 / 2) / (2 * ε)
  let H₀ := 2 + Hp + Real.exp 1 + 96 / cuspEndpointLengthSqLower + Real.exp R
  have hquot : 0 < 96 / cuspEndpointLengthSqLower :=
    div_pos (by norm_num) cuspEndpointLengthSqLower_pos
  have hH₀ : 1 < H₀ := by dsimp only [H₀]; linarith [Real.exp_pos 1, Real.exp_pos R]
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  have hH1 : 1 < H := hH₀.trans_le hH
  have hHpos : 0 < H := by linarith
  have hHpH : Hp ≤ H := by dsimp only [H₀] at hH; linarith [Real.exp_pos 1, Real.exp_pos R]
  have hlarge : 96 / cuspEndpointLengthSqLower ≤ H := by
    dsimp only [H₀] at hH
    linarith [Real.exp_pos 1, Real.exp_pos R]
  have hwindow : Real.exp 1 ≤ H ^ 4 := by
    have hExp : Real.exp 1 ≤ H := by dsimp only [H₀] at hH; linarith [Real.exp_pos R]
    exact hExp.trans (by nlinarith [sq_nonneg (H ^ 2 - 1)])
  have hR : R ≤ Real.log H := by
    have hExp : Real.exp R ≤ H := by dsimp only [H₀] at hH; linarith [Real.exp_pos 1]
    have h := Real.log_le_log (Real.exp_pos R) hExp
    simpa only [Real.log_exp] using h
  have hrate : (2 * Real.log K + 1 / 2) / (4 * Real.log H) ≤ ε / 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos hH1))).mpr
    have h := (div_le_iff₀ (show 0 < 2 * ε by positivity)).mp hR
    nlinarith
  let C₁ := Real.exp (3 * Real.log K + 4 * Real.log H + 1 / 2)
  refine ⟨Cp * C₁, mul_pos hCp (Real.exp_pos _), ?_⟩
  intro n E A hE
  obtain ⟨P, hP, hPcover⟩ := hpatterns H hHpH n
  have hc := hcover H (ε / 2) hH1 hwindow hlarge hrate n P hPcover E A hE
  have hcost : (P.card : ℝ) *
      (C₁ * Real.exp ((1 + ε / 2) * n - A / 2)) ≤
      (Cp * C₁) * Real.exp ((1 + ε) * n - A / 2) := by
    calc
      _ ≤ (Cp * Real.exp (ε / 2 * n)) *
          (C₁ * Real.exp ((1 + ε / 2) * n - A / 2)) :=
        mul_le_mul_of_nonneg_right hP (by dsimp only [C₁]; positivity)
      _ = (Cp * C₁) * (Real.exp (ε / 2 * n) *
          Real.exp ((1 + ε / 2) * n - A / 2)) := by ring
      _ = _ := by
        rw [← Real.exp_add, show ε / 2 * (n : ℝ) + ((1 + ε / 2) * n - A / 2) =
          (1 + ε) * n - A / 2 by ring]
  have hT : 0 ≤ (n : ℝ) + 4 * Real.log H := by
    have hlog := (Real.log_pos hH1).le
    positivity
  exact (hc.mono_bound hcost).measurable_modular_cover hηpos.le hη hT

end Erdos1148.DukeArithmetic
