/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMixedTensorStep
import ErdosProblems.Erdos4b.FGKMTMixedError
import ErdosProblems.Erdos4b.FGKMTTensorRelative

/-!
# A uniform relative mean with one distinct tensor factor

The constant is fixed before all dimensions, arithmetic parameters,
and both test functions. Each test has its own positive mass and
derivative bound; a common normalized cost controls the error.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem exists_mixedTensorSieveSum_relative_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j J : ℕ}, 0 < k → 0 < M → 1 < R → j + 1 ≤ J →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ s : ℕ, s < j + 1 → ∀ p : ℕ, p.Prime → ¬p ∣ M →
        (p : ℝ) / 2 ≤ g p + s ∧ |g p + s - p| ≤ 2 * (k : ℝ) ∧ g p + s ≤ p - 1) →
      ∀ {H G : ℝ → ℝ}, ContDiff ℝ 1 H → ContDiff ℝ 1 G →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) →
      0 < (∫ x in (0 : ℝ)..1, H x) → 0 < (∫ x in (0 : ℝ)..1, G x) →
      ∀ {VH VG Ω : ℝ}, 0 ≤ Ω →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv H x| ≤ VH) →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ VG) →
      |H 1| + VH ≤ Ω * (∫ x in (0 : ℝ)..1, H x) →
      |G 1| + VG ≤ Ω * (∫ x in (0 : ℝ)..1, G x) →
      (j + 1 : ℕ) * (C * Ω * modulusLogScale (M * R ^ J) ^ 3 / Real.log R) ≤ 1 →
      |mixedTensorSieveSum M g R j H G -
          multivariateSieveConstant M g (j + 1) * (Real.log R * (∫ x in (0 : ℝ)..1, H x)) *
            (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j| /
        (multivariateSieveConstant M g (j + 1) * (Real.log R * (∫ x in (0 : ℝ)..1, H x)) *
          (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j) ≤
        4 * (j + 1 : ℕ) * (C * Ω * modulusLogScale (M * R ^ J) ^ 3 / Real.log R) := by
  obtain ⟨Ch, hCh, hheadBound⟩ := exists_mixedTensorSieveSum_coordinate_error
  obtain ⟨Ct, hCt, htailBound⟩ := exists_tensorSieveSum_relative_error
  let C := Ch + Ct
  refine ⟨C, add_pos hCh hCt, ?_⟩
  intro k M R j J hk hM hR hj hsmall g hchain H G hH hG hG0 hHmass hGmass
    VH VG Ω hΩ hVH hVG hHcost hGcost htotal
  let L := Real.log R
  let Λ := modulusLogScale (M * R ^ J)
  let εh : ℝ := Ch * Ω * Λ ^ 3 / L
  let εt : ℝ := Ct * Ω * Λ ^ 3 / L
  let ε : ℝ := C * Ω * Λ ^ 3 / L
  let a := sieveMainConstant M g * (L * (∫ x in (0 : ℝ)..1, H x))
  let P := multivariateSieveConstant M (fun p => g p + 1) j *
    (L * (∫ x in (0 : ℝ)..1, G x)) ^ j
  let S := tensorSieveSum M (fun p => g p + 1) R j G
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hR)
  have hΛ : 0 ≤ Λ := zero_le_one.trans (one_le_modulusLogScale _)
  have hεh : 0 ≤ εh := by dsimp only [εh]; positivity
  have hεt : 0 ≤ εt := by dsimp only [εt]; positivity
  have heq : ε = εh + εt := by dsimp only [ε, εh, εt, C]; ring
  have hε : 0 ≤ ε := by rw [heq]; positivity
  have hεhle : εh ≤ ε := by rw [heq]; linarith
  have hεtle : εt ≤ ε := by rw [heq]; linarith
  have hjε : (j : ℝ) * ε ≤ 1 := by
    have ht : ((j : ℝ) + 1) * ε ≤ 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using htotal
    nlinarith
  have hb0 (p : ℕ) (hp : p.Prime) (hpM : ¬p ∣ M) :
      (p : ℝ) / 2 ≤ g p ∧ |g p - p| ≤ 2 * (k : ℝ) ∧ g p ≤ p - 1 := by
    simpa only [Nat.cast_zero, add_zero] using hchain 0 (Nat.zero_lt_succ j) p hp hpM
  have hchain' : ∀ s : ℕ, s < j → ∀ p : ℕ, p.Prime → ¬p ∣ M →
      (p : ℝ) / 2 ≤ (g p + 1) + s ∧
        |(g p + 1) + s - p| ≤ 2 * (k : ℝ) ∧ (g p + 1) + s ≤ p - 1 := by
    intro s hs p hp hpM
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      hchain (s + 1) (Nat.succ_lt_succ hs) p hp hpM
  have hc : 0 < sieveMainConstant M g := sieveMainConstant_pos hk hM hsmall g
    (fun p hp hpM => (hb0 p hp hpM).1)
    (fun p hp hpM => (hb0 p hp hpM).2.1)
    (fun p hp hpM => (hb0 p hp hpM).2.2)
  have ha : 0 < a := mul_pos hc (mul_pos hL hHmass)
  have hP : 0 < P := mul_pos (multivariateSieveConstant_pos hk hM hsmall _ hchain')
    (pow_pos (mul_pos hL hGmass) j)
  have hS : 0 ≤ S := tensorSieveSum_nonneg hR _ (fun p hp hpM => by
    have hgp := (hb0 p hp hpM).1
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    linarith) hG0
  have hB : Ch * Λ ^ 3 * (|H 1| + VH) ≤ (L * (∫ x in (0 : ℝ)..1, H x)) * ε := by
    calc
      _ ≤ (Ch * Λ ^ 3) * (Ω * (∫ x in (0 : ℝ)..1, H x)) :=
        mul_le_mul_of_nonneg_left hHcost (by positivity)
      _ = (L * (∫ x in (0 : ℝ)..1, H x)) * εh := by
        dsimp only [εh]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hεhle (mul_nonneg hL.le hHmass.le)
  have hh := hheadBound hk hM hR (by omega : j ≤ J) hsmall g
    (fun p hp hpM => (hb0 p hp hpM).1)
    (fun p hp hpM => (hb0 p hp hpM).2.1)
    (fun p hp hpM => (hb0 p hp hpM).2.2) hH hG0 hVH
  have hhead : |mixedTensorSieveSum M g R j H G - a * S| ≤ a * ε * S := by
    calc
      _ ≤ (sieveMainConstant M g * (Ch * Λ ^ 3 * (|H 1| + VH))) * S := hh
      _ ≤ (sieveMainConstant M g * ((L * (∫ x in (0 : ℝ)..1, H x)) * ε)) * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB hc.le) hS
      _ = _ := by dsimp only [a]; ring
  have ht := htailBound hk hM hR (by omega : j ≤ J) hsmall (fun p => g p + 1)
    hchain' hG hG0 hGmass hΩ hVG hGcost
    ((mul_le_mul_of_nonneg_left hεtle (Nat.cast_nonneg j)).trans hjε)
  have htail : |S - P| ≤ (2 * (j : ℝ) * ε) * P := by
    have ht' : |S - P| / P ≤ 2 * (j : ℝ) * εt := ht
    exact ((div_le_iff₀ hP).mp ht').trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hεtle (by positivity)) hP.le)
  have hmain : multivariateSieveConstant M g (j + 1) *
      (Real.log R * (∫ x in (0 : ℝ)..1, H x)) *
      (Real.log R * (∫ x in (0 : ℝ)..1, G x)) ^ j = a * P := by
    rw [multivariateSieveConstant_succ_shift]
    dsimp only [a, P, L]
    ring
  rw [hmain]
  apply (div_le_iff₀ (mul_pos ha hP)).mpr
  simpa only [Nat.cast_add, Nat.cast_one] using
    mixed_error_from_head_tail ha.le hP hε hjε hhead htail

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_mixedTensorSieveSum_relative_error
