import ErdosProblems.Erdos1148.ShortReturningScale
import ErdosProblems.Erdos1148.ReturningVectors
import ErdosProblems.Erdos1148.LiftCoverRefinement
import ErdosProblems.Erdos1148.OrdinaryLiftRefinement
import ErdosProblems.Erdos1148.FiniteLiftCoverComposition

/-! # Returning refinements with a cubic moving-height cost -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_long_height_returning_lift_refinement {η : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y S T : ℝ), 1 ≤ Y → 0 ≤ S → 0 ≤ T →
      96 * Real.exp (-T) ≤ (Y ^ 2)⁻¹ → ∀ E : Set SL(2, ℝ), LiftForwardClose η S E →
      (∀ g ∈ E, modularMk (g * diagonalFlow S) ∉ modularCusp Y) →
      (∀ g ∈ E, HasReturningVector T ((Y ^ 2)⁻¹) (g * diagonalFlow S)) →
      LiftCoverBound η (S + T) E (C * (Y + 1) ^ 3 * Real.exp (T / 2)) := by
  have hδ : 0 < η / 8 := div_pos hηpos (by norm_num)
  let C := 67601 * (32 / (η / 8) + 1) * (2 / (η / 8) + 1) ^ 2
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Y S T hY hS hT hsmall E hE hheight hreturn
  have hYpos : 0 < Y := by linarith
  by_cases hne : E.Nonempty
  · obtain ⟨g₀, hg₀⟩ := hne
    obtain ⟨γ, hγ⟩ := exists_integral_bounded_lift_of_not_cusp hYpos
      (g₀ * diagonalFlow S) (hheight g₀ hg₀)
    let a : SL(2, ℝ) := γ
    let base := a * (g₀ * diagonalFlow S)
    obtain ⟨N, B, hN, _, hcov, hB⟩ := exists_quantitative_returningGauss_lift_cover
      (A := 2 * (Y + 2)) (c := (Y ^ 2)⁻¹) (by positivity) (by positivity) hδ base hγ hT hsmall
    have hN' : (N : ℝ) ≤ C * (Y + 1) ^ 3 * Real.exp (T / 2) :=
      hN.trans (mul_le_mul_of_nonneg_right (returning_cover_constant_le_cubic hY hδ)
        (Real.exp_pos _).le)
    have hB' : ∀ i, LiftForwardClose η T (B i) := by
      have hscale : 8 * (η / 8) = η := by ring
      simpa only [hscale] using hB
    have hcov' : (fun g => a * (g * diagonalFlow S)) '' E ⊆ ⋃ i, B i := by
      rintro _ ⟨g, hg, rfl⟩
      apply hcov
      have hclose : EntryCloseOne η (base⁻¹ * (a * (g * diagonalFlow S))) := by
        have heq : base⁻¹ * (a * (g * diagonalFlow S)) =
            (g₀ * diagonalFlow S)⁻¹ * (g * diagonalFlow S) := by dsimp only [base]; group
        rw [heq]
        exact hE g₀ hg₀ g hg S ⟨hS, le_rfl⟩
      exact exists_returningGaussParameters_of_close hη base _ hclose
        ((hreturn g hg).integral_mul γ)
    obtain ⟨F, hF, hclose⟩ := exists_lift_cover_refinement hE a B hcov' hB'
    exact ⟨N, F, hN', hF, hclose⟩
  · have hEmpty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero]
      positivity
    · simp [hEmpty]
    · intro i
      exact Fin.elim0 i

theorem exists_height_returning_lift_refinement {η : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y S T : ℝ), 1 ≤ Y → 0 ≤ S → 0 ≤ T →
      ∀ E : Set SL(2, ℝ), LiftForwardClose η S E →
      (∀ g ∈ E, modularMk (g * diagonalFlow S) ∉ modularCusp Y) →
      (∀ g ∈ E, HasReturningVector T ((Y ^ 2)⁻¹) (g * diagonalFlow S)) →
      LiftCoverBound η (S + T) E (C * (Y + 1) ^ 3 * Real.exp (T / 2)) := by
  obtain ⟨C₀, hC₀, hlong⟩ := exists_long_height_returning_lift_refinement hηpos hη
  obtain ⟨Ko, hKo, hord⟩ := exists_ordinary_lift_refinement hηpos hη
  let C := max C₀ (10 * Ko)
  have hC : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro Y S T hY hS hT E hE hheight hreturn
  by_cases hsmall : 96 * Real.exp (-T) ≤ (Y ^ 2)⁻¹
  · have hc := hlong Y S T hY hS hT hsmall E hE hheight hreturn
    apply hc.mono_bound
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hc : LiftCoverBound η (S + T) E (Ko * Real.exp T) := hord hS hT E hE
    apply hc.mono_bound
    have hYpos : 0 < Y := by linarith
    have hpoly : Y ≤ (Y + 1) ^ 3 := by
      nlinarith [sq_nonneg Y, pow_nonneg hYpos.le 3]
    calc
      _ ≤ Ko * (10 * Y * Real.exp (T / 2)) :=
        mul_le_mul_of_nonneg_left (exp_le_ten_height_mul_exp_half hYpos hsmall) hKo.le
      _ = (10 * Ko) * Y * Real.exp (T / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul (le_max_right C₀ (10 * Ko)) hpoly hYpos.le hC.le) (Real.exp_pos _).le

end Erdos1148.DukeArithmetic
