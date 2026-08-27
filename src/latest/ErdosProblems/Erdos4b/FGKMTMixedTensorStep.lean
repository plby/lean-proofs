/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMixedTensorSum
import ErdosProblems.Erdos4b.FGKMTSmoothCoordinate

/-!
# Integrating the distinguished factor first

Only the remaining product must be nonnegative. The same absolute
one-coordinate constant controls the distinct factor and leaves the
proved equal-factor tensor sum with the shifted denominator.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_mixedTensorSieveSum_coordinate_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j J : ℕ}, 0 < k → 0 < M → 1 < R → j ≤ J →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) →
      ∀ {H G : ℝ → ℝ}, ContDiff ℝ 1 H →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) → ∀ {V : ℝ},
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv H x| ≤ V) →
      |mixedTensorSieveSum M g R j H G -
        (sieveMainConstant M g * (Real.log R * (∫ x in (0 : ℝ)..1, H x))) *
          tensorSieveSum M (fun p => g p + 1) R j G| ≤
        (sieveMainConstant M g * (C * modulusLogScale (M * R ^ J) ^ 3 * (|H 1| + V))) *
          tensorSieveSum M (fun p => g p + 1) R j G := by
  obtain ⟨C, hC, hbound⟩ := exists_roughSieveWeight_smooth_coordinate_error
  refine ⟨C, hC, ?_⟩
  intro k M R j J hk hM hR hj hsmall g hg hclose hupper H G hH hG0 V hV
  let A : ℝ := Real.log R * (∫ x in (0 : ℝ)..1, H x)
  let B : ℝ := C * modulusLogScale (M * R ^ J) ^ 3 * (|H 1| + V)
  let P := fun e : Fin j → Fin (R + 1) => ∏ i, G (Real.log (e i).val / Real.log R)
  let W := fun e : Fin j → Fin (R + 1) =>
    roughSieveWeight M (fun p => g p + 1) (∏ i, (e i).val)
  let S := fun e : Fin j → Fin (R + 1) =>
    ∑ n ∈ Finset.Icc 0 R,
      H (Real.log n / Real.log R) * roughSieveWeight M g ((∏ i, (e i).val) * n)
  have hP (e : Fin j → Fin (R + 1)) : 0 ≤ P e :=
    Finset.prod_nonneg (fun i _ => hG0 _ (log_coordinate_mem_unit hR (e i)))
  have hb (e : Fin j → Fin (R + 1)) :
      |S e - sieveMainConstant M g * A * W e| ≤ sieveMainConstant M g * B * W e := by
    have he : (∏ i, (e i).val) ≤ R ^ J :=
      (tensor_coordinate_product_le e).trans (Nat.pow_le_pow_right (by omega) hj)
    have h := hbound hk hM hR he hsmall g hg hclose hupper hH hV
    convert h using 1
    · dsimp only [S, A, W]
      congr 1
      ring
    · dsimp only [B, W]
      ring
  rw [mixedTensorSieveSum_split]
  change |(∑ e, P e * S e) - (sieveMainConstant M g * A) * (∑ e, P e * W e)| ≤
    (sieveMainConstant M g * B) * (∑ e, P e * W e)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e he
  have heq : P e * S e - (sieveMainConstant M g * A) * (P e * W e) =
      P e * (S e - sieveMainConstant M g * A * W e) := by ring
  rw [heq, abs_mul, abs_of_nonneg (hP e)]
  calc
    _ ≤ P e * (sieveMainConstant M g * B * W e) := mul_le_mul_of_nonneg_left (hb e) (hP e)
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_mixedTensorSieveSum_coordinate_error
