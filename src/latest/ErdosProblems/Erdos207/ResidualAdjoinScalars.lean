/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LaterTriangleScaleUpdate

/-! # Exact old-edge density and constant budgets in the residual adjoin step -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem laterTriangleScale_mul_pow_le_factor
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k next : Fin (ell + 1)) (p p' beta factor : ℝ≥0)
    (D S : TripleSystemOn V) (hSD : S ⊆ D)
    (hold : ∀ T ∈ S, p / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) ≤
      p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0))
    (hnew : ∀ T ∈ D \ S, beta ≤ factor * (p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0))) :
    laterTriangleScale W k p S * beta ^ (D \ S).card ≤
      factor ^ (D \ S).card * laterTriangleScale W next p' D := by
  let f := fun T : TripleOn V ↦ p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)
  have hOld : laterTriangleScale W k p S ≤ ∏ T ∈ S, f T := prod_le_prod' hold
  have hNew : beta ^ (D \ S).card ≤ ∏ T ∈ D \ S, factor * f T := by
    rw [← prod_const]
    exact prod_le_prod' hnew
  calc
    _ ≤ (∏ T ∈ S, f T) * ∏ T ∈ D \ S, factor * f T := mul_le_mul hOld hNew zero_le zero_le
    _ = factor ^ (D \ S).card * ((∏ T ∈ D \ S, f T) * ∏ T ∈ S, f T) := by
      rw [prod_mul_distrib]
      simp only [prod_const]
      ring
    _ = _ := by rw [prod_sdiff hSD]; rfl

theorem residualAdjoinPartitionTerm_le
    (p alpha C factor b nInv oldScale newScale : ℝ≥0) (a s e t d : ℕ)
    (hcard : d = s + t) (hC : 1 ≤ C) (hfactor : 1 ≤ factor) (halpha : alpha ≤ 1)
    (hscale : oldScale * (alpha * p ^ 3) ^ t ≤ factor ^ t * newScale) :
    alpha ^ t * (C ^ (a + s + (3 * t + e)) *
      (p ^ (3 * t + e) * nInv ^ a * oldScale + b)) ≤
      (C ^ 3 * factor) ^ (a + d + e) * (p ^ e * nInv ^ a * newScale + b) := by
  have hcExp : C ^ (a + s + (3 * t + e)) ≤ (C ^ 3) ^ (a + d + e) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hC (by omega)
  have hfExp : factor ^ t ≤ factor ^ (a + d + e) := pow_le_pow_right₀ hfactor (by omega)
  have hbase : C ^ (a + s + (3 * t + e)) * factor ^ t ≤
      (C ^ 3 * factor) ^ (a + d + e) := by
    rw [mul_pow]
    exact mul_le_mul hcExp hfExp zero_le zero_le
  have herror : alpha ^ t * b ≤ factor ^ t * b :=
    mul_le_mul_of_nonneg_right ((pow_le_one₀ zero_le halpha).trans (one_le_pow₀ hfactor)) zero_le
  have hmain : (p ^ e * nInv ^ a) * (oldScale * (alpha * p ^ 3) ^ t) ≤
      factor ^ t * (p ^ e * nInv ^ a * newScale) := by
    exact (mul_le_mul_of_nonneg_left hscale zero_le).trans_eq (by ring)
  have hp : p ^ (3 * t + e) = (p ^ 3) ^ t * p ^ e := by rw [pow_add, pow_mul]
  calc
    _ = C ^ (a + s + (3 * t + e)) *
        ((p ^ e * nInv ^ a) * (oldScale * (alpha * p ^ 3) ^ t) + alpha ^ t * b) := by
      rw [hp, mul_pow]
      ring
    _ ≤ C ^ (a + s + (3 * t + e)) *
        (factor ^ t * (p ^ e * nInv ^ a * newScale) + factor ^ t * b) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain herror) zero_le
    _ = (C ^ (a + s + (3 * t + e)) * factor ^ t) * (p ^ e * nInv ^ a * newScale + b) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbase zero_le

theorem residualReserveAdjoinPartitionTerm_le
    (p alpha C factor b nInv oldScale newScale r : ℝ≥0) (a s e t d l : ℕ)
    (hcard : d = s + t) (hC : 1 ≤ C) (hfactor : 1 ≤ factor) (halpha : alpha ≤ 1)
    (hscale : oldScale * (alpha * p ^ 3) ^ t ≤ factor ^ t * newScale) :
    alpha ^ t * (C ^ (a + s + (3 * t + e) + l) *
      (p ^ (3 * t + e) * r ^ l * nInv ^ a * oldScale + b)) ≤
      (C ^ 3 * factor) ^ (a + d + e + l) *
        (p ^ e * r ^ l * nInv ^ a * newScale + b) := by
  have hscale' : (r ^ l * oldScale) * (alpha * p ^ 3) ^ t ≤
      factor ^ t * (r ^ l * newScale) := by
    calc
      _ = r ^ l * (oldScale * (alpha * p ^ 3) ^ t) := by ring
      _ ≤ r ^ l * (factor ^ t * newScale) := mul_le_mul_of_nonneg_left hscale zero_le
      _ = _ := by ring
  have hterm := residualAdjoinPartitionTerm_le p alpha C factor b nInv
    (r ^ l * oldScale) (r ^ l * newScale) a s e t d hcard hC hfactor halpha hscale'
  have hCf : C ≤ C ^ 3 * factor := by
    calc
      C = C ^ 1 := by simp
      _ ≤ C ^ 3 := pow_le_pow_right₀ hC (by omega)
      _ ≤ _ := le_mul_of_one_le_right zero_le hfactor
  calc
    _ = C ^ l * (alpha ^ t * (C ^ (a + s + (3 * t + e)) *
        (p ^ (3 * t + e) * nInv ^ a * (r ^ l * oldScale) + b))) := by
      rw [pow_add]
      ring
    _ ≤ (C ^ 3 * factor) ^ l * ((C ^ 3 * factor) ^ (a + d + e) *
        (p ^ e * nInv ^ a * (r ^ l * newScale) + b)) :=
      mul_le_mul (pow_le_pow_left' hCf l) hterm zero_le zero_le
    _ = _ := by rw [pow_add]; ring

end

end Erdos207
