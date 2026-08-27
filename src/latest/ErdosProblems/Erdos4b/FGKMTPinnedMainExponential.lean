/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProfileExponentialLower

/-!
# Cubic dimension loss for the original pinned main term

Only the presieve modulus size enters the exponential loss. The possibly
large exceptional prime contributes a factor at least one half to density.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem commonPinnedMainTerm_ge_exp_cube {m B0 W R : ℕ} {H : ℝ}
    (hH : 0 ≤ H) (hm : 1 ≤ m) (hlog : 10000 ≤ Real.log (m + 1 : ℕ))
    (hB0 : B0 = 1 ∨ B0.Prime) (hW : 0 < W) (hBW : B0.Coprime W)
    (hR : 1 ≤ Real.log (R : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B0 * W)
    (hsize : (W : ℝ) ≤ Real.exp (H * (m + 1 : ℕ) ^ 2)) :
    Real.exp (-(3 * H + 20) * (m + 1 : ℕ) ^ 3) ≤ commonPinnedMainTerm m (B0 * W) R := by
  let k : ℝ := (m + 1 : ℕ)
  let b : ℝ := ((B0 * W).totient : ℝ) / (B0 * W)
  have hk1 : 1 ≤ k := by dsimp [k]; exact_mod_cast (by omega : 1 ≤ m + 1)
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have hk23 : k ^ 2 ≤ k ^ 3 := pow_le_pow_right₀ hk1 (by omega)
  have hmR : (m : ℝ) ≤ k := by dsimp [k]; push_cast; linarith
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb : Real.exp (-(H + 1) * k ^ 2) ≤ b :=
    totientDensity_ge_exp_dimension hB0 hW hBW (by omega : 1 ≤ m + 1) hsize
  have htwo : Real.exp (-2) ≤ (1 / 2 : ℝ) :=
    exp_neg_le_inv_of_le_exp (by norm_num) (by linarith [Real.add_one_le_exp 2])
  have hnorm : Real.exp (-(H + 3) * k ^ 2) ≤ b / 2 := by
    calc
      _ ≤ Real.exp (-(H + 1) * k ^ 2) * Real.exp (-2) := by
        rw [← Real.exp_add]
        apply Real.exp_monotone
        nlinarith
      _ ≤ b * (1 / 2) := mul_le_mul hb htwo (Real.exp_pos _).le hb0
      _ = _ := by ring
  have hnormSq := pow_le_pow_left₀ (Real.exp_pos _).le hnorm 2
  have hpower : Real.exp (-(H + 1) * k ^ 3) ≤ b ^ m := by
    calc
      _ ≤ Real.exp (-(H + 1) * k ^ 2) ^ m := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_monotone
        calc
          _ = -((H + 1) * k ^ 2 * k) := by ring
          _ ≤ -((H + 1) * k ^ 2 * (m : ℝ)) :=
            neg_le_neg (mul_le_mul_of_nonneg_left hmR (by positivity))
          _ = _ := by ring
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hb m
  have hJ := faceLowerFormula_ge_exp_square (Nat.succ_pos m) hlog (by omega : m ≤ m + 1)
  have hcombined : Real.exp (-(3 * H + 20) * k ^ 3) ≤
      Real.exp (-(H + 3) * k ^ 2) ^ 2 * Real.exp (-(H + 1) * k ^ 3) *
        Real.exp (-10 * k ^ 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_monotone
    norm_num only [Nat.cast_ofNat]
    have hcost := mul_le_mul_of_nonneg_left hk23 (by positivity : 0 ≤ 2 * H + 16)
    nlinarith [show 0 ≤ k ^ 3 by positivity]
  have hBpos : 0 < B0 := hB0.elim (by rintro rfl; omega) Nat.Prime.pos
  have hM : 0 < B0 * W := Nat.mul_pos hBpos hW
  have hfinite := commonPinnedMainTerm_explicit_lower hm hlog hM hR hsmall
  simp only [Nat.cast_mul] at hfinite
  apply hcombined.trans
  apply le_trans _ hfinite
  exact mul_le_mul (mul_le_mul hnormSq hpower (Real.exp_pos _).le (sq_nonneg _))
    hJ (Real.exp_pos _).le (by positivity)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPinnedMainTerm_ge_exp_cube
