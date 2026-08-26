import ErdosProblems.Erdos1148.FixedPatternLiftCover
import ErdosProblems.Erdos1148.RefinedCoverExponent

/-! # Refined covers of fixed visit-pattern classes with compact observation endpoints -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def fixedCuspPatternClass (H : ℝ) (n : ℕ) (V : Finset ℕ) : Set SL(2, ℝ) :=
  {g | let entry := g * diagonalFlow (2 * Real.log H)
    modularMk entry ∉ modularCusp H ∧
    modularMk (entry * diagonalFlow (n : ℝ)) ∉ modularCusp H ∧
    modularCuspVisitTimes H n (modularMk entry) = V}

theorem exists_small_rate_fixed_pattern_cover {η : ℝ} (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (H ε : ℝ), 1 < H → Real.exp 1 ≤ H ^ 4 →
      96 / cuspEndpointLengthSqLower ≤ H →
      (2 * Real.log K + 1 / 2) / (4 * Real.log H) ≤ ε →
      ∀ (n : ℕ) (V : Finset ℕ) (E : Set SL(2, ℝ)), LiftForwardClose η 0 E →
      E ⊆ fixedCuspPatternClass H n V →
      LiftCoverBound η ((n : ℝ) + 4 * Real.log H) E
        (Real.exp (3 * Real.log K + 4 * Real.log H + 1 / 2) *
          Real.exp ((1 + ε) * n - (V.card : ℝ) / 2)) := by
  obtain ⟨K, hK, hcover⟩ := exists_fixed_pattern_lift_cover hηpos hη
  refine ⟨K, hK, ?_⟩
  intro H ε hH hwindow hlarge hrate n V E hclose hE
  by_cases hne : E.Nonempty
  · obtain ⟨g, hg⟩ := hne
    let g₀ := g * diagonalFlow (2 * Real.log H)
    have hV : modularCuspVisitTimes H n (modularMk g₀) = V := (hE hg).2.2
    have hsame : ∀ h ∈ E, let entry := h * diagonalFlow (2 * Real.log H)
        modularMk entry ∉ modularCusp H ∧
        modularMk (entry * diagonalFlow (n : ℝ)) ∉ modularCusp H ∧
        modularCuspVisitTimes H n (modularMk entry) = modularCuspVisitTimes H n (modularMk g₀) := by
      intro h hh
      have hx := hE hh
      exact ⟨hx.1, hx.2.1, hx.2.2.trans hV.symm⟩
    have hc := hcover g₀ H hH.le hwindow hlarge n E hclose hsame
    dsimp only at hc
    rw [hV] at hc
    apply hc.mono_bound
    apply fixed_pattern_cost_small_rate hK hH hrate
    simpa only [hV] using card_maximal_cusp_runs_le g₀ hH n
  · have hEmpty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero]
      positivity
    · simp [hEmpty]
    · intro i
      exact Fin.elim0 i

end Erdos1148.DukeArithmetic
