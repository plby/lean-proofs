/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSmoothCoordinate
import ErdosProblems.Erdos4b.FGKMTTensorSum

/-!
# The finite multivariate coordinate error

Summing the one-coordinate error against the remaining nonnegative
profile gives the actual lower-dimensional sieve sum with denominator
`g + 1`. The modulus envelope is fixed before the induction dimension.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem exists_tensorSieveSum_coordinate_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j J : ℕ}, 0 < k → 0 < M → 1 < R → j ≤ J →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) →
      (∀ p : ℕ, p.Prime → ¬p ∣ M → g p ≤ p - 1) →
      ∀ {G : ℝ → ℝ}, ContDiff ℝ 1 G →
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ G x) → ∀ {V : ℝ},
      (∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv G x| ≤ V) →
      |tensorSieveSum M g R (j + 1) G -
        (sieveMainConstant M g * (Real.log R * (∫ x in (0 : ℝ)..1, G x))) *
          tensorSieveSum M (fun p => g p + 1) R j G| ≤
        (sieveMainConstant M g * (C * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V))) *
          tensorSieveSum M (fun p => g p + 1) R j G := by
  obtain ⟨C, hC, hbound⟩ := exists_roughSieveWeight_smooth_coordinate_error
  refine ⟨C, hC, ?_⟩
  intro k M R j J hk hM hR hj hsmall g hg hclose hupper G hG hG0 V hV
  let A : ℝ := Real.log R * (∫ x in (0 : ℝ)..1, G x)
  let B : ℝ := C * modulusLogScale (M * R ^ J) ^ 3 * (|G 1| + V)
  let P := fun e : Fin j → Fin (R + 1) => ∏ i, G (Real.log (e i).val / Real.log R)
  let W := fun e : Fin j → Fin (R + 1) =>
    roughSieveWeight M (fun p => g p + 1) (∏ i, (e i).val)
  let S := fun e : Fin j → Fin (R + 1) =>
    ∑ n ∈ Finset.Icc 0 R,
      G (Real.log n / Real.log R) * roughSieveWeight M g ((∏ i, (e i).val) * n)
  have hP (e : Fin j → Fin (R + 1)) : 0 ≤ P e :=
    Finset.prod_nonneg (fun i _ => hG0 _ (log_coordinate_mem_unit hR (e i)))
  have hb (e : Fin j → Fin (R + 1)) :
      |S e - sieveMainConstant M g * A * W e| ≤ sieveMainConstant M g * B * W e := by
    have he : (∏ i, (e i).val) ≤ R ^ J :=
      (tensor_coordinate_product_le e).trans (Nat.pow_le_pow_right (by omega) hj)
    have h := hbound hk hM hR he hsmall g hg hclose hupper hG hV
    convert h using 1
    · dsimp only [S, A, W]
      congr 1
      ring
    · dsimp only [B, W]
      ring
  rw [tensorSieveSum_succ]
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

#print axioms Erdos4b.FGKMT.exists_tensorSieveSum_coordinate_error
