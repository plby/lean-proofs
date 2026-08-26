import ErdosProblems.Erdos520.HarperMovingHeightVerticalCumulative

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory ProbabilityTheory Topology
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Numerical cumulative constants for the positive-log bridge

The sharp checkpoint theorems retain summable tails.  This file packages
those tails into constants independent of the path length, the moving height
cutoff, and the central dyadic depth.
-/

/-- After the logarithmic height shift, the complete moving-height
oscillation-envelope tail is bounded by one numerical constant. -/
theorem exists_harperScheduledMovingHeightOscillationTail_constant_bound
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ K ≥ 0, ∃ J : ℕ, ∀ M start : ℕ,
      J + Nat.clog 2 (M + 1) ≤ start →
        harperScheduledErrorTail
          (harperScheduledOscillationEnvelope M c C) start ≤ K := by
  obtain ⟨J, htheta⟩ := Filter.eventually_atTop.1
    (eventually_harperScheduledThetaEnvelope_le_invLog_sq hc hC)
  let A : ℝ := 1 + 5 * (C + 1)
  let K : ℝ := 2 * A * (1 / 2 : ℝ) ^ J
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, J, ?_⟩
  intro M start hstart
  have hterm : ∀ k : ℕ,
      harperScheduledOscillationEnvelope M c C (k + start) ≤
        A * (1 / 2 : ℝ) ^ (J + k) := by
    intro k
    have hshiftK :
        (J + k) + Nat.clog 2 (M + 1) ≤ k + start := by omega
    have hthetaK : harperScheduledThetaEnvelope c C (k + start) ≤
        (C + 1) * invLog (harperBlockEndpoint (k + start)) ^ 2 :=
      htheta (k + start) (by omega)
    have henv := harperScheduledOscillationEnvelope_le_clog_shift
      hC hshiftK hthetaK
    have hpow : (1 / 2 : ℝ) ^ (2 * (J + k)) ≤
        (1 / 2 : ℝ) ^ (J + k) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc
      harperScheduledOscillationEnvelope M c C (k + start) ≤
          (1 / 2 : ℝ) ^ (J + k) +
            5 * (C + 1) * (1 / 2 : ℝ) ^ (2 * (J + k)) := henv
      _ ≤ (1 / 2 : ℝ) ^ (J + k) +
            5 * (C + 1) * (1 / 2 : ℝ) ^ (J + k) := by
        gcongr
      _ = A * (1 / 2 : ℝ) ^ (J + k) := by
        dsimp [A]
        ring
  have hleft : Summable (fun k : ℕ ↦
      harperScheduledOscillationEnvelope M c C (k + start)) :=
    (summable_nat_add_iff start).2
      (summable_harperScheduledOscillationEnvelope M hc hC)
  have hright : Summable (fun k : ℕ ↦
      A * (1 / 2 : ℝ) ^ (J + k)) := by
    apply (summable_geometric_two.mul_left (A * (1 / 2 : ℝ) ^ J)).congr
    intro k
    rw [pow_add]
    ring
  calc
    harperScheduledErrorTail
        (harperScheduledOscillationEnvelope M c C) start =
        ∑' k : ℕ,
          harperScheduledOscillationEnvelope M c C (k + start) := rfl
    _ ≤ ∑' k : ℕ, A * (1 / 2 : ℝ) ^ (J + k) :=
      hleft.tsum_le_tsum hterm hright
    _ = ∑' k : ℕ,
        (A * (1 / 2 : ℝ) ^ J) * (1 / 2 : ℝ) ^ k := by
      congr 1
      funext k
      rw [pow_add]
      ring
    _ = (A * (1 / 2 : ℝ) ^ J) * 2 := by
      rw [summable_geometric_two.tsum_mul_left, tsum_geometric_two]
    _ = K := by
      dsimp [K]
      ring

/-- Numerical reciprocal and drift constants for every moving noncentral
window. -/
theorem
    exists_harperScheduledMovingHeightVerticalCumulativeUniformConstants :
    ∃ E ≥ 0, ∃ D ≥ 0, ∃ J : ℕ,
      ∀ M start n y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ start →
          harperBlockEndpoint (start + n) ≤ y →
            ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ k : Fin n,
              |(∑ i ∈ Finset.Iic k,
                  harperScheduledReciprocalMass y
                    (start + (i : ℕ))) -
                  ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ E ∧
                |harperScheduledVerticalCumulativeDrift y start n t k -
                    ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ D := by
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, Jclose, hclose⟩ :=
    exists_harperScheduledMovingHeightVerticalCumulativeDrift_close
  obtain ⟨Kosc, hKosc, Josc, hosc⟩ :=
    exists_harperScheduledMovingHeightOscillationTail_constant_bound
      hc hC.le
  let E : ℝ :=
    ∑' j : ℕ, harperScheduledReciprocalEnvelope c₀ C₀ j
  let D : ℝ := E + (1 / 2 : ℝ) * Kosc +
    2 * (∑' j : ℕ, harperScheduledSquareEnvelope j) +
    (9 / 64 : ℝ)
  let J := max Jclose Josc
  have hE : 0 ≤ E := by
    dsimp [E]
    exact tsum_nonneg (harperScheduledReciprocalEnvelope_nonneg hC₀.le)
  have hsquareTsum : 0 ≤
      ∑' j : ℕ, harperScheduledSquareEnvelope j :=
    tsum_nonneg harperScheduledSquareEnvelope_nonneg
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  refine ⟨E, hE, D, hD, J, ?_⟩
  intro M start n y hstart hy t htLower htUpper k
  have h := hclose M start n y (by omega) hy t htLower htUpper k
  have hrecTail :
      harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c₀ C₀) start ≤ E := by
    dsimp [E]
    exact harperScheduledErrorTail_le_tsum
      (harperScheduledReciprocalEnvelope_nonneg hC₀.le)
      (summable_harperScheduledReciprocalEnvelope hc₀ hC₀.le) start
  have hoscTail :
      harperScheduledErrorTail
          (harperScheduledOscillationEnvelope M c C) start ≤ Kosc :=
    hosc M start (by omega)
  have hsquareTail :
      harperScheduledErrorTail harperScheduledSquareEnvelope start ≤
        ∑' j : ℕ, harperScheduledSquareEnvelope j :=
    harperScheduledErrorTail_le_tsum
      harperScheduledSquareEnvelope_nonneg
      summable_harperScheduledSquareEnvelope start
  constructor
  · exact h.1.trans hrecTail
  · exact h.2.trans (by
      dsimp [D]
      nlinarith)

/-- Numerical reciprocal and drift constants for every central dyadic band.
-/
theorem
    exists_harperScheduledCentralBandVerticalCumulativeUniformConstants :
    ∃ E ≥ 0, ∃ D ≥ 0, ∃ J : ℕ,
      ∀ d start n y : ℕ, J + d ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ,
            (1 / 2 : ℝ) ^ (d + 1) < |t| →
            |t| ≤ (1 / 2 : ℝ) ^ d → ∀ k : Fin n,
              |(∑ i ∈ Finset.Iic k,
                  harperScheduledReciprocalMass y
                    (start + (i : ℕ))) -
                  ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ E ∧
                |harperScheduledVerticalCumulativeDrift y start n t k -
                    ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ D := by
  obtain ⟨K, hK, J, hbound⟩ :=
    exists_harperScheduledCentralBandVerticalCumulativeDrift_constant_bound
  exact ⟨K, hK, K, hK, J, hbound⟩

/-- One common pair of numerical constants works simultaneously for moving
noncentral windows and for all shrinking central dyadic bands. -/
theorem
    exists_harperScheduledMovingAndCentralVerticalCumulativeUniformConstants :
    ∃ E ≥ 0, ∃ D ≥ 0, ∃ J : ℕ,
      (∀ M start n y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ start →
          harperBlockEndpoint (start + n) ≤ y →
            ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ k : Fin n,
              |(∑ i ∈ Finset.Iic k,
                  harperScheduledReciprocalMass y
                    (start + (i : ℕ))) -
                  ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ E ∧
                |harperScheduledVerticalCumulativeDrift y start n t k -
                    ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ D) ∧
      (∀ d start n y : ℕ, J + d ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ,
            (1 / 2 : ℝ) ^ (d + 1) < |t| →
            |t| ≤ (1 / 2 : ℝ) ^ d → ∀ k : Fin n,
              |(∑ i ∈ Finset.Iic k,
                  harperScheduledReciprocalMass y
                    (start + (i : ℕ))) -
                  ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ E ∧
                |harperScheduledVerticalCumulativeDrift y start n t k -
                    ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ D) := by
  obtain ⟨E₁, hE₁, D₁, hD₁, J₁, hnoncentral⟩ :=
    exists_harperScheduledMovingHeightVerticalCumulativeUniformConstants
  obtain ⟨E₂, hE₂, D₂, hD₂, J₂, hcentral⟩ :=
    exists_harperScheduledCentralBandVerticalCumulativeUniformConstants
  let E := max E₁ E₂
  let D := max D₁ D₂
  let J := max J₁ J₂
  have hE : 0 ≤ E := hE₁.trans (le_max_left E₁ E₂)
  have hD : 0 ≤ D := hD₁.trans (le_max_left D₁ D₂)
  refine ⟨E, hE, D, hD, J, ?_, ?_⟩
  · intro M start n y hstart hy t htLower htUpper k
    have h := hnoncentral M start n y (by omega) hy t htLower htUpper k
    exact ⟨h.1.trans (le_max_left E₁ E₂),
      h.2.trans (le_max_left D₁ D₂)⟩
  · intro d start n y hstart hy t htLower htUpper k
    have h := hcentral d start n y (by omega) hy t htLower htUpper k
    exact ⟨h.1.trans (le_max_right E₁ E₂),
      h.2.trans (le_max_right D₁ D₂)⟩

end Problem520
end Erdos
