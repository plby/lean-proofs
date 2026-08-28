import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# Taylor control on the high-order vanishing locus

This is the quantitative part of the high-order vanishing step in Sard's
theorem. The derivatives and Taylor remainder are the native Fréchet ones;
no measure-zero or regular-value conclusion is assumed.
-/

open scoped ContDiff NNReal
open Set

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def flatPoints (f : E → F) (k : ℕ) : Set E :=
  {x | ∀ j : ℕ, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0}

theorem taylorSum_eq_of_flat {f : E → F} {k : ℕ} {x : E}
    (hx : x ∈ flatPoints f k) (v : E) :
    (∑ j ∈ Finset.range (k + 1), (j.factorial : ℝ)⁻¹ •
      iteratedFDeriv ℝ j f x (fun _ ↦ v)) = f x := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [hx j (Nat.one_le_iff_ne_zero.mpr hj0) (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
    simp
  · simp

theorem norm_sub_le_of_flat [CompleteSpace F] {f : E → F} {k : ℕ} {x y : E}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ∞ f (x + t • (y - x)))
    (hx : x ∈ flatPoints f k) (C : ℝ≥0)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (k + 1) f (x + t • (y - x))‖ ≤ C) :
    ‖f y - f x‖ ≤ ((k.factorial : ℝ)⁻¹ * C) * ‖y - x‖ ^ (k + 1) := by
  let R := fun t : ℝ ↦ (1 - t) ^ k •
    iteratedFDeriv ℝ (k + 1) f (x + t • (y - x)) (fun _ ↦ y - x)
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (n := k) (x := x) (y := y - x) (fun t ht ↦ (hf t ht).of_le (by
      exact_mod_cast (le_top : (k + 1 : ℕ∞) ≤ ⊤)))
  rw [show x + (y - x) = y by abel, taylorSum_eq_of_flat hx] at hTaylor
  have hEq : f y - f x = (k.factorial : ℝ)⁻¹ • ∫ t in (0 : ℝ)..1, R t := by
    rw [hTaylor, add_sub_cancel_left]
  have hR : ∀ t ∈ Icc (0 : ℝ) 1, ‖R t‖ ≤ C * ‖y - x‖ ^ (k + 1) := by
    intro t ht
    have hp : ‖(1 - t) ^ k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by linarith [ht.2]) _)]
      exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])
    have hD : ‖iteratedFDeriv ℝ (k + 1) f (x + t • (y - x)) (fun _ ↦ y - x)‖ ≤
        C * ‖y - x‖ ^ (k + 1) := by
      calc
        _ ≤ ‖iteratedFDeriv ℝ (k + 1) f (x + t • (y - x))‖ * ‖y - x‖ ^ (k + 1) := by
          simpa using (iteratedFDeriv ℝ (k + 1) f (x + t • (y - x))).le_opNorm (fun _ ↦ y - x)
        _ ≤ C * ‖y - x‖ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right (hC t ht) (pow_nonneg (norm_nonneg _) _)
    change ‖(1 - t) ^ k • _‖ ≤ _
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans hD
  have hInt : ‖∫ t in (0 : ℝ)..1, R t‖ ≤ C * ‖y - x‖ ^ (k + 1) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := C * ‖y - x‖ ^ (k + 1)) (f := R) (fun t ht ↦ hR t (by
        rw [uIoc_of_le zero_le_one] at ht
        exact ⟨ht.1.le, ht.2⟩))
    simpa using h
  rw [hEq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (k.factorial : ℝ)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hInt (by positivity)).trans_eq (mul_assoc _ _ _).symm

end NoExoticSixSphere.Sard
