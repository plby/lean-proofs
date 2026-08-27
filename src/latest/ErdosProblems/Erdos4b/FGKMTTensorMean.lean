/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTensorStep
import ErdosProblems.Erdos4b.FGKMTGeometricError

/-!
# Dimension-uniform smooth tensor means

The same constant works for all dimensions and all successive sieve
denominators. The geometric error is explicit, and the arithmetic main
constant is the finite product already identified with the multivariate
Euler product. This is the positive tensor majorant used in the more
general cutoff-profile induction.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_tensorSieveSum_geometric_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j J : ℕ}, 0 < k → 0 < M → 1 < R → j ≤ J →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ s : ℕ, s < j → ∀ p : ℕ, p.Prime → ¬p ∣ M →
        (p : ℝ) / 2 ≤ g p + s ∧ |g p + s - p| ≤ 2 * (k : ℝ) ∧ g p + s ≤ p - 1) →
      ∀ {G : ℝ → ℝ}, ContDiff ℝ 1 G →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) → ∀ {V : ℝ},
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) →
      |tensorSieveSum M g R j G -
          multivariateSieveConstant M g j * (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j| ≤
        multivariateSieveConstant M g j *
          ((Real.log R * (∫ x in (0 : ℝ)..1, G x) +
              C * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)) ^ j -
            (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j) := by
  obtain ⟨C, hC, hstep⟩ := exists_tensorSieveSum_coordinate_error
  refine ⟨C, hC, ?_⟩
  intro k M R j J hk hM hR hj hsmall g hchain G hG hG0 V hV
  let A : ℝ := Real.log R * (∫ x in (0 : ℝ)..1, G x)
  let B : ℝ := C * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)
  have hA : 0 ≤ A := mul_nonneg (Real.log_nonneg (by exact_mod_cast hR.le))
    (intervalIntegral.integral_nonneg zero_le_one hG0)
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, zero_le_one⟩)
  have hscale : 0 ≤ modulusLogScale (M * R ^ J) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  change |tensorSieveSum M g R j G - multivariateSieveConstant M g j * A ^ j| ≤
    multivariateSieveConstant M g j * ((A + B) ^ j - A ^ j)
  revert g
  revert hj
  induction j with
  | zero =>
      intro hj g hchain
      simp [tensorSieveSum_zero, multivariateSieveConstant_zero]
  | succ j ih =>
      intro hj g hchain
      have hb0 (p : ℕ) (hp : p.Prime) (hpM : ¬p ∣ M) :
          (p : ℝ) / 2 ≤ g p ∧ |g p - p| ≤ 2 * (k : ℝ) ∧ g p ≤ p - 1 := by
        simpa only [Nat.cast_zero, add_zero] using hchain 0 (Nat.zero_lt_succ j) p hp hpM
      have hc := sieveMainConstant_pos hk hM hsmall g
        (fun p hp hpM => (hb0 p hp hpM).1)
        (fun p hp hpM => (hb0 p hp hpM).2.1)
        (fun p hp hpM => (hb0 p hp hpM).2.2)
      have hchain' : ∀ s : ℕ, s < j → ∀ p : ℕ, p.Prime → ¬p ∣ M →
          (p : ℝ) / 2 ≤ (g p + 1) + s ∧
            |(g p + 1) + s - p| ≤ 2 * (k : ℝ) ∧ (g p + 1) + s ≤ p - 1 := by
        intro s hs p hp hpM
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
          hchain (s + 1) (Nat.succ_lt_succ hs) p hp hpM
      have htail := ih (by omega : j ≤ J) (fun p => g p + 1) hchain'
      have hcoordinate := hstep hk hM hR (by omega : j ≤ J) hsmall g
        (fun p hp hpM => (hb0 p hp hpM).1)
        (fun p hp hpM => (hb0 p hp hpM).2.1)
        (fun p hp hpM => (hb0 p hp hpM).2.2) hG hG0 hV
      have herror := geometric_error_step j hA hB hc.le hcoordinate htail
      rw [multivariateSieveConstant_succ_shift]
      exact herror

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_tensorSieveSum_geometric_error
