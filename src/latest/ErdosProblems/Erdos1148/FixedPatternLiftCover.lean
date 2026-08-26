import ErdosProblems.Erdos1148.FixedPatternExcursionData
import ErdosProblems.Erdos1148.OrderedExcursionCover
import ErdosProblems.Erdos1148.MeasurableLiftCover

/-! # A refined coherent cover for one fixed cusp visit pattern -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_fixed_pattern_lift_cover {η : ℝ} (hηpos : 0 < η) (hη : η ≤ 1 / 2) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (g₀ : SL(2, ℝ)) (H : ℝ), 1 ≤ H → Real.exp 1 ≤ H ^ 4 →
      96 / cuspEndpointLengthSqLower ≤ H → ∀ (n : ℕ) (E : Set SL(2, ℝ)),
      LiftForwardClose η 0 E →
      (∀ g ∈ E, let entry := g * diagonalFlow (2 * Real.log H)
        modularMk entry ∉ modularCusp H ∧
        modularMk (entry * diagonalFlow (n : ℝ)) ∉ modularCusp H ∧
        modularCuspVisitTimes H n (modularMk entry) = modularCuspVisitTimes H n (modularMk g₀)) →
      let V := modularCuspVisitTimes H n (modularMk g₀)
      let r := (maximalNatRuns V).card
      LiftCoverBound η ((n : ℝ) + 4 * Real.log H) E
        (K ^ (2 * r + 1) * Real.exp
          ((n : ℝ) + 4 * Real.log H - ((V.card : ℝ) - r) / 2)) := by
  obtain ⟨K₀, hK₀, hcover⟩ := exists_ordered_excursion_lift_cover hηpos hη
  let K := max K₀ 1
  have hK : 1 ≤ K := le_max_right _ _
  refine ⟨K, hK, ?_⟩
  intro g₀ H hH hwindow hlarge n E hclose hE
  let V := modularCuspVisitTimes H n (modularMk g₀)
  let r := (maximalNatRuns V).card
  obtain ⟨l, hpair, hbounds, hlen, hsum, hexc⟩ :=
    exists_fixed_pattern_excursion_data g₀ hH hwindow hlarge n E hE
  have hT : 0 ≤ (n : ℝ) + 4 * Real.log H := by
    have hlog := Real.log_nonneg hH
    positivity
  have hret : ∀ p ∈ l, ∃ H' L : ℝ, 1 ≤ H' ∧ 1 ≤ L ∧
      p.2 - p.1 = L + 4 * Real.log H' ∧
      96 * Real.exp (-(p.2 - p.1)) ≤ cuspEndpointLengthSqLower ∧
      ∀ g ∈ E, BufferedCuspExcursion H' L (g * diagonalFlow p.1) := by
    intro p hp
    obtain ⟨L, hL, heq, hsmall, hreturn⟩ := hexc p hp
    exact ⟨H, L, hH, hL, heq, hsmall, hreturn⟩
  have hc := hcover E l 0 ((n : ℝ) + 4 * Real.log H) le_rfl hT hclose hpair hbounds hret
  simp only [sub_zero] at hc
  apply hc.mono_bound
  have hlen' : l.length ≤ r := hlen
  have hsum' : (V.card : ℝ) - r ≤ (l.map (fun p => p.2 - p.1)).sum := hsum
  have hpowers : K₀ ^ (2 * l.length + 1) ≤ K ^ (2 * r + 1) := by
    calc
      _ ≤ K ^ (2 * l.length + 1) := pow_le_pow_left₀ hK₀.le (le_max_left _ _) _
      _ ≤ K ^ (2 * r + 1) := pow_le_pow_right₀ hK
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hlen') 1)
  exact mul_le_mul hpowers (Real.exp_le_exp.mpr (by linarith [hsum']))
    (Real.exp_pos _).le (by positivity)

end Erdos1148.DukeArithmetic
