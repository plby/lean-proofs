/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TwoFamilyRootExposure

/-! # Two-family exposure with a prescribed surviving ambient-size power -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem rootedTwoFamilyExtensions_card_mul_inv_pow_le_pow
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W))
    (R R' : Finset W) (b m A B n a e f d : ℕ)
    (hcard : ∀ S ∈ F, S.card ≤ m)
    (hfirst : (familyExtensions F R).card ≤ A * n ^ a)
    (hsecond : ∀ Q : Finset W, Q.card = b → (familyExtensions G Q).card ≤ B * n ^ e)
    (hn : 1 ≤ n) (hexp : a + e ≤ f + d) :
    ((rootedTwoFamilyExtensions F G R R' b).card : ℝ≥0) * (n : ℝ≥0)⁻¹ ^ f ≤
      ((A : ℝ≥0) * 2 ^ (m + R'.card) * B) * (n : ℝ≥0) ^ d := by
  have hbound := rootedTwoFamilyExtensions_card_mul_inv_pow_le F G R R' b m A B n a e (f + d)
    hcard hfirst hsecond hn hexp
  have hpos : (0 : ℝ≥0) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    _ = (((rootedTwoFamilyExtensions F G R R' b).card : ℝ≥0) *
        (n : ℝ≥0)⁻¹ ^ (f + d)) * (n : ℝ≥0) ^ d := by
      simp only [pow_add, inv_pow, mul_assoc,
        inv_mul_cancel₀ (ne_of_gt (pow_pos hpos d)), mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound zero_le

end

end Erdos207
