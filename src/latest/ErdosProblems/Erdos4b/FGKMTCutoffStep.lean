/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCutoffSum
import ErdosProblems.Erdos4b.FGKMTSmoothCoordinate

/-!
# Summing one coordinate with the genuine coupled cutoff

The main term averages the cutoff and shifts the arithmetic denominator.
The error is bounded by the positive tensor majorant, not by a signed
cutoff sum. All constants are uniform in the frozen coordinate sum.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_cutoffSieveSum_coordinate_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j J : ℕ}, 0 < k → 0 < M → 1 < R → j ≤ J →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) →
      ∀ {G Φ : ℝ → ℝ} {K V : ℝ}, ContDiff ℝ 1 G →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) → BoundedCutoff Φ K →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) → ∀ u : ℝ,
      |cutoffSieveSum M g R (j + 1) G Φ u -
        (sieveMainConstant M g * Real.log R) *
          cutoffSieveSum M (fun p => g p + 1) R j G (cutoffAverage G Φ) u| ≤
        K * sieveMainConstant M g * (C * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)) *
          tensorSieveSum M (fun p => g p + 1) R j G := by
  obtain ⟨C, hC, hbound⟩ := exists_roughSieveWeight_smooth_coordinate_error
  refine ⟨2 * C, by positivity, ?_⟩
  intro k M R j J hk hM hR hj hsmall g hg hclose hupper G Φ K V hG hG0 hΦ hV u
  let B : ℝ := (2 * C) * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)
  let P := fun e : Fin j → Fin (R + 1) => ∏ i, G (Real.log (e i).val / Real.log R)
  let W := fun e : Fin j → Fin (R + 1) =>
    roughSieveWeight M (fun p => g p + 1) (∏ i, (e i).val)
  let v := fun e : Fin j → Fin (R + 1) => u + ∑ i, Real.log (e i).val / Real.log R
  let S := fun e : Fin j → Fin (R + 1) =>
    ∑ n ∈ Finset.Icc 0 R,
      cutoffTest G Φ (v e) (Real.log n / Real.log R) *
        roughSieveWeight M g ((∏ i, (e i).val) * n)
  have hP (e : Fin j → Fin (R + 1)) : 0 ≤ P e :=
    Finset.prod_nonneg (fun i _ => hG0 _ (log_coordinate_mem_unit hR (e i)))
  have hW (e : Fin j → Fin (R + 1)) : 0 ≤ W e :=
    roughSieveWeight_nonneg M _ (fun p hp hpM => by
      have hgp := hg p hp hpM
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      linarith) _
  have hc := (sieveMainConstant_pos hk hM hsmall g hg hclose hupper).le
  have hscale := zero_le_one.trans (one_le_modulusLogScale (M * R ^ J))
  have hb (e : Fin j → Fin (R + 1)) :
      |S e - (sieveMainConstant M g * Real.log R) *
          (cutoffAverage G Φ (v e) * W e)| ≤ K * sieveMainConstant M g * B * W e := by
    have hWe := hW e
    have he : (∏ i, (e i).val) ≤ R ^ J :=
      (tensor_coordinate_product_le e).trans (Nat.pow_le_pow_right (by omega) hj)
    have hcost := cutoffTest_cost hG hΦ hV (v e)
    have h := hbound hk hM hR he hsmall g hg hclose hupper
      (cutoffTest_contDiff hG hΦ.smooth (v e)) hcost.1
    have havg : (∫ t in (0 : ℝ)..1, cutoffTest G Φ (v e) t) = cutoffAverage G Φ (v e) :=
      (cutoffAverage_eq_interval G Φ (v e)).symm
    rw [havg] at h
    calc
      _ = |S e - sieveMainConstant M g * W e * Real.log R * cutoffAverage G Φ (v e)| := by
        congr 1
        ring
      _ ≤ C * sieveMainConstant M g * W e * modulusLogScale (M * R ^ J) ^ 3 *
          (|cutoffTest G Φ (v e) 1| + K * (|G 1| + 2 * V)) := h
      _ ≤ C * sieveMainConstant M g * W e * modulusLogScale (M * R ^ J) ^ 3 *
          (2 * K * (|G 1| + V)) :=
        mul_le_mul_of_nonneg_left hcost.2 (by positivity)
      _ = _ := by dsimp only [B]; ring
  rw [cutoffSieveSum_succ]
  change |(∑ e, P e * S e) - (sieveMainConstant M g * Real.log R) *
      (∑ e, P e * cutoffAverage G Φ (v e) * W e)| ≤
    (K * sieveMainConstant M g * B) * (∑ e, P e * W e)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e he
  have heq : P e * S e - (sieveMainConstant M g * Real.log R) *
      (P e * cutoffAverage G Φ (v e) * W e) =
    P e * (S e - (sieveMainConstant M g * Real.log R) *
      (cutoffAverage G Φ (v e) * W e)) := by ring
  rw [heq, abs_mul, abs_of_nonneg (hP e)]
  calc
    _ ≤ P e * (K * sieveMainConstant M g * B * W e) :=
      mul_le_mul_of_nonneg_left (hb e) (hP e)
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_cutoffSieveSum_coordinate_error
