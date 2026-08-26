import ErdosProblems.Erdos1148.MovingHeightPatternCover
import ErdosProblems.Erdos1148.RefinedCoverExponent

/-! # Small-overhead covers of moving-height pattern classes -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def movingHeightCuspPatternClass (H Y : ℝ) (n : ℕ) (V : Finset ℕ) : Set SL(2, ℝ) :=
  {g | let entry := g * diagonalFlow (2 * Real.log H)
    modularMk entry ∉ modularCusp Y ∧ modularCuspVisitTimes H n (modularMk entry) = V}

theorem exists_small_rate_moving_pattern_cover {η : ℝ} (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K C : ℝ, 1 ≤ K ∧ 1 ≤ C ∧ ∀ (H Y ε : ℝ), 1 < H → 1 ≤ Y → Real.exp 1 ≤ H ^ 4 →
      96 / cuspEndpointLengthSqLower ≤ H →
      (2 * Real.log K + 1 / 2) / (4 * Real.log H) ≤ ε →
      ∀ (n : ℕ) (V : Finset ℕ) (E : Set SL(2, ℝ)), LiftForwardClose η 0 E →
      E ⊆ movingHeightCuspPatternClass H Y n V →
      LiftCoverBound η ((n : ℝ) + 4 * Real.log H) E
        (C * (Y * H + 1) ^ 3 * Real.exp (3 * Real.log K + 4 * Real.log H + 1 / 2) *
          Real.exp ((1 + ε) * n - (V.card : ℝ) / 2)) := by
  obtain ⟨K, C, hK, hC, hcover⟩ := exists_moving_height_pattern_lift_cover hηpos hη
  refine ⟨K, C, hK, hC, ?_⟩
  intro H Y ε hH hY hwindow hlarge hrate n V E hclose hE
  by_cases hne : E.Nonempty
  · obtain ⟨g, hg⟩ := hne
    let g₀ := g * diagonalFlow (2 * Real.log H)
    have hV : modularCuspVisitTimes H n (modularMk g₀) = V := (hE hg).2
    have hheight : ∀ h ∈ E, modularMk (h * diagonalFlow (2 * Real.log H)) ∉ modularCusp Y :=
      fun h hh => (hE hh).1
    have htimes : ∀ h ∈ E,
        modularCuspVisitTimes H n (modularMk (h * diagonalFlow (2 * Real.log H))) =
          modularCuspVisitTimes H n (modularMk g₀) :=
      fun h hh => (hE hh).2.trans hV.symm
    have hc := hcover g₀ H Y hH.le hY hwindow hlarge n E hclose hheight htimes
    dsimp only at hc
    rw [hV] at hc
    apply hc.mono_bound
    have hr : ((maximalNatRuns V).card : ℝ) ≤ (n : ℝ) / (4 * Real.log H) + 1 := by
      simpa only [hV] using card_maximal_cusp_runs_le g₀ hH n
    have hcost := fixed_pattern_cost_small_rate hK hH hrate n V.card (maximalNatRuns V).card hr
    calc
      _ = (C * (Y * H + 1) ^ 3) * (K ^ (2 * (maximalNatRuns V).card + 1) *
          Real.exp ((n : ℝ) + 4 * Real.log H - ((V.card : ℝ) - (maximalNatRuns V).card) / 2)) := by ring
      _ ≤ (C * (Y * H + 1) ^ 3) * (Real.exp (3 * Real.log K + 4 * Real.log H + 1 / 2) *
          Real.exp ((1 + ε) * n - (V.card : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = _ := by ring
  · have hEmpty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero]
      positivity
    · simp [hEmpty]
    · intro i
      exact Fin.elim0 i

end Erdos1148.DukeArithmetic
