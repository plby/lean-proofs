import ErdosProblems.Erdos1148.MovingHighCuspVisitCover
import ErdosProblems.Erdos1148.CuspVisitTimePatterns
import ErdosProblems.Erdos1148.CuspCoverHeightThreshold
import ErdosProblems.Erdos1148.MeasurableLiftCover

/-! # Refined measurable local covers with a cubic moving-height cost -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_refined_moving_local_lift_cover {η ε : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) (hε : 0 < ε) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 1 ≤ Y → ∀ (n : ℕ) (E : Set SL(2, ℝ)) (A : ℝ), LiftForwardClose η 0 E →
      LiftCoverBound η ((n : ℝ) + 4 * Real.log H) (highCuspVisitsWithInitialHeight H Y n A E)
        (C * (Y + 1) ^ 3 * Real.exp ((1 + ε) * n - A / 2)) := by
  obtain ⟨K, C₀, hK, hC₀, hcover⟩ := exists_moving_high_cusp_visit_lift_cover hηpos hη
  obtain ⟨Hp, Cp, hHp, hCp, hpatterns⟩ :=
    exists_cusp_visit_time_patterns_small_rate (half_pos hε)
  obtain ⟨H₀, hH₀, hthreshold⟩ := exists_cusp_cover_height_threshold K Hp (half_pos hε) hHp
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  have hH1 : 1 < H := hH₀.trans_le hH
  obtain ⟨hHpH, hwindow, hlarge, hrate⟩ := hthreshold H hH
  let F := Real.exp (3 * Real.log K + 4 * Real.log H + 1 / 2)
  let D := C₀ * (H + 1) ^ 3 * F
  have hC₀pos : 0 < C₀ := by linarith
  have hD : 0 < D := by dsimp only [D, F]; positivity
  refine ⟨Cp * D, mul_pos hCp hD, ?_⟩
  intro Y hY n E A hE
  obtain ⟨P, hP, hPcover⟩ := hpatterns H hHpH n
  have hc := hcover H Y (ε / 2) hH1 hY hwindow hlarge hrate n P hPcover E A hE
  have hheight : (Y * H + 1) ^ 3 ≤ (H + 1) ^ 3 * (Y + 1) ^ 3 := by
    have hbase : Y * H + 1 ≤ (H + 1) * (Y + 1) := by nlinarith
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ Y * H + 1) hbase 3
  have hfactor : C₀ * (Y * H + 1) ^ 3 * F ≤ D * (Y + 1) ^ 3 := by
    calc
      _ ≤ (C₀ * ((H + 1) ^ 3 * (Y + 1) ^ 3)) * F :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hheight hC₀pos.le) (Real.exp_pos _).le
      _ = _ := by dsimp only [D]; ring
  have hcost : (P.card : ℝ) * (C₀ * (Y * H + 1) ^ 3 * F *
      Real.exp ((1 + ε / 2) * n - A / 2)) ≤
      (Cp * D) * (Y + 1) ^ 3 * Real.exp ((1 + ε) * n - A / 2) := by
    calc
      _ ≤ (Cp * Real.exp (ε / 2 * n)) *
          ((D * (Y + 1) ^ 3) * Real.exp ((1 + ε / 2) * n - A / 2)) :=
        mul_le_mul hP (mul_le_mul_of_nonneg_right hfactor (Real.exp_pos _).le)
          (by dsimp only [F]; positivity) (by positivity)
      _ = (Cp * D) * (Y + 1) ^ 3 * (Real.exp (ε / 2 * n) *
          Real.exp ((1 + ε / 2) * n - A / 2)) := by ring
      _ = _ := by
        rw [← Real.exp_add, show ε / 2 * (n : ℝ) + ((1 + ε / 2) * n - A / 2) =
          (1 + ε) * n - A / 2 by ring]
  exact hc.mono_bound hcost

theorem exists_refined_moving_local_cusp_cover {η ε : ℝ}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2) (hε : 0 < ε) :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∃ C : ℝ, 0 < C ∧
      ∀ Y : ℝ, 1 ≤ Y → ∀ (n : ℕ) (E : Set SL(2, ℝ)) (A : ℝ), LiftForwardClose η 0 E →
      ∃ (N : ℕ) (B : Fin N → Set ModularOrbitSpace),
        (N : ℝ) ≤ C * (Y + 1) ^ 3 * Real.exp ((1 + ε) * n - A / 2) ∧
        (∀ i, IsCompact (B i)) ∧ (∀ i, MeasurableSet (B i)) ∧
        modularMk '' highCuspVisitsWithInitialHeight H Y n A E ⊆ ⋃ i, B i ∧
        ∀ i, B i ×ˢ B i ⊆ modularForwardBowenPairs (32 * η) ((n : ℝ) + 4 * Real.log H) := by
  obtain ⟨H₀, hH₀, hcover⟩ := exists_refined_moving_local_lift_cover hηpos hη hε
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  obtain ⟨C, hC, hlocal⟩ := hcover H hH
  refine ⟨C, hC, ?_⟩
  intro Y hY n E A hE
  have hT : 0 ≤ (n : ℝ) + 4 * Real.log H := by
    have hlog := (Real.log_pos (hH₀.trans_le hH)).le
    positivity
  exact (hlocal Y hY n E A hE).measurable_modular_cover hηpos.le hη hT

end Erdos1148.DukeArithmetic
