/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCutoffStep
import ErdosProblems.Erdos4b.FGKMTCutoffIntegral
import ErdosProblems.Erdos4b.FGKMTTensorRelative

/-!
# Uniform multivariate means with a sum-dependent cutoff

The cutoff is averaged after each coordinate, and its bound is multiplied
by the profile mass. The signed error is controlled using the proved
positive tensor majorant. The main term remains the genuine cube integral.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_cutoffSieveSum_geometric_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R J : ℕ}, 0 < k → 0 < M → 1 < R →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) →
      ∀ {G : ℝ → ℝ}, ContDiff ℝ 1 G →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) → ∀ {V : ℝ},
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) →
      ∀ j : ℕ, j ≤ J → ∀ g : ℕ → ℝ,
      (∀ s : ℕ, s < j → ∀ p : ℕ, p.Prime → ¬p ∣ M →
        (p : ℝ) / 2 ≤ g p + s ∧ |g p + s - p| ≤ 2 * (k : ℝ) ∧ g p + s ≤ p - 1) →
      ∀ (Φ : ℝ → ℝ) (K : ℝ), BoundedCutoff Φ K → ∀ u : ℝ,
      |cutoffSieveSum M g R j G Φ u -
          multivariateSieveConstant M g j * Real.log R ^ j * cutoffCubeIntegral G Φ j u| ≤
        K * multivariateSieveConstant M g j *
          ((Real.log R * (∫ x in (0 : ℝ)..1, G x) +
              C * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)) ^ j -
            (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j) := by
  obtain ⟨C₁, hC₁, htensor⟩ := exists_tensorSieveSum_geometric_error
  obtain ⟨C₂, hC₂, hstep⟩ := exists_cutoffSieveSum_coordinate_error
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro k M R J hk hM hR hsmall G hG hG0 V hV
  let a : ℝ := ∫ x in (0 : ℝ)..1, G x
  let A : ℝ := Real.log R * a
  let B : ℝ := (C₁ + C₂) * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)
  have ha : 0 ≤ a := intervalIntegral.integral_nonneg zero_le_one hG0
  have hlog : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hA : 0 ≤ A := mul_nonneg hlog.le ha
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV 0 ⟨le_rfl, zero_le_one⟩)
  have hscale : 0 ≤ modulusLogScale (M * R ^ J) :=
    zero_le_one.trans (one_le_modulusLogScale _)
  have hcost : 0 ≤ |G 1| + V := add_nonneg (abs_nonneg _) hV0
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hB₁ : C₁ * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V) ≤ B :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C₁ ≤ C₁ + C₂) (by positivity)) hcost
  have hB₂ : C₂ * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V) ≤ B :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C₂ ≤ C₁ + C₂) (by positivity)) hcost
  intro j
  induction j with
  | zero =>
      intro hj g hchain Φ K hΦ u
      simp [cutoffSieveSum_zero, cutoffCubeIntegral_zero, multivariateSieveConstant_zero]
  | succ j ih =>
      intro hj g hchain Φ K hΦ u
      have hK := hΦ.constant_nonneg
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
      let Q := multivariateSieveConstant M (fun p => g p + 1) j
      let T := tensorSieveSum M (fun p => g p + 1) R j G
      let Z := cutoffSieveSum M (fun p => g p + 1) R j G (cutoffAverage G Φ) u
      let I := cutoffCubeIntegral G (cutoffAverage G Φ) j u
      have hQ : 0 < Q := multivariateSieveConstant_pos hk hM hsmall _ hchain'
      have hT0 : 0 ≤ T := tensorSieveSum_nonneg hR _ (fun p hp hpM => by
        have hgp := (hb0 p hp hpM).1
        have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        linarith) hG0
      have hTsmall := htensor hk hM hR (by omega : j ≤ J) hsmall
        (fun p => g p + 1) hchain' hG hG0 hV
      change |T - Q * A ^ j| ≤ Q *
        ((A + C₁ * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)) ^ j - A ^ j) at hTsmall
      have hTupperSmall : T ≤ Q *
          (A + C₁ * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)) ^ j := by
        have h := (le_abs_self (T - Q * A ^ j)).trans hTsmall
        nlinarith
      have hTupper : T ≤ Q * (A + B) ^ j := hTupperSmall.trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (add_le_add le_rfl hB₁) j) hQ.le)
      have hcoordinate := hstep hk hM hR (by omega : j ≤ J) hsmall g
        (fun p hp hpM => (hb0 p hp hpM).1)
        (fun p hp hpM => (hb0 p hp hpM).2.1)
        (fun p hp hpM => (hb0 p hp hpM).2.2) hG hG0 hΦ hV u
      have hcoord : |cutoffSieveSum M g R (j + 1) G Φ u -
          (sieveMainConstant M g * Real.log R) * Z| ≤
            K * sieveMainConstant M g * B * T := hcoordinate.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hB₂ (mul_nonneg hK hc.le)) hT0)
      have htail := ih (by omega : j ≤ J) (fun p => g p + 1) hchain'
        (cutoffAverage G Φ) (K * a) (hΦ.average_mass hG.continuous hG0) u
      change |Z - Q * Real.log R ^ j * I| ≤ (K * a) * Q * ((A + B) ^ j - A ^ j) at htail
      rw [multivariateSieveConstant_succ_shift, cutoffCubeIntegral_succ hG.continuous hΦ]
      change |cutoffSieveSum M g R (j + 1) G Φ u -
          (sieveMainConstant M g * Q) * Real.log R ^ (j + 1) * I| ≤
        K * (sieveMainConstant M g * Q) * ((A + B) ^ (j + 1) - A ^ (j + 1))
      have heq : cutoffSieveSum M g R (j + 1) G Φ u -
          (sieveMainConstant M g * Q) * Real.log R ^ (j + 1) * I =
        (cutoffSieveSum M g R (j + 1) G Φ u - (sieveMainConstant M g * Real.log R) * Z) +
          (sieveMainConstant M g * Real.log R) * (Z - Q * Real.log R ^ j * I) := by
        rw [pow_succ]
        ring
      rw [heq]
      calc
        _ ≤ |cutoffSieveSum M g R (j + 1) G Φ u - (sieveMainConstant M g * Real.log R) * Z| +
            |(sieveMainConstant M g * Real.log R) * (Z - Q * Real.log R ^ j * I)| :=
          abs_add_le _ _
        _ = |cutoffSieveSum M g R (j + 1) G Φ u - (sieveMainConstant M g * Real.log R) * Z| +
            (sieveMainConstant M g * Real.log R) * |Z - Q * Real.log R ^ j * I| := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg hc.le hlog.le)]
        _ ≤ K * sieveMainConstant M g * B * T +
            (sieveMainConstant M g * Real.log R) * ((K * a) * Q * ((A + B) ^ j - A ^ j)) :=
          add_le_add hcoord (mul_le_mul_of_nonneg_left htail (mul_nonneg hc.le hlog.le))
        _ ≤ K * sieveMainConstant M g * B * (Q * (A + B) ^ j) +
            (sieveMainConstant M g * Real.log R) * ((K * a) * Q * ((A + B) ^ j - A ^ j)) :=
          add_le_add (mul_le_mul_of_nonneg_left hTupper (by positivity)) le_rfl
        _ = _ := by rw [pow_succ, pow_succ]; dsimp only [A]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_cutoffSieveSum_geometric_error
