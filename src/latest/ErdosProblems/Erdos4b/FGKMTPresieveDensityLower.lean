/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimePreSieveNormalization
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Elementary lower bounds for the retained totient density

The excluded factor is one or a prime. Its size therefore does not enter
the density loss; only the actual presieve modulus W appears.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem half_le_totientDensity_of_one_or_prime {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    (1 / 2 : ℝ) ≤ (B.totient : ℝ) / B := by
  rcases hB with rfl | hB
  · norm_num
  · have hB2 : (2 : ℝ) ≤ B := by exact_mod_cast hB.two_le
    rw [Nat.totient_prime hB, Nat.cast_sub hB.one_le, Nat.cast_one]
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < B)).mpr
    linarith

theorem inv_two_mul_presieve_le_totientDensity {B W : ℕ}
    (hB : B = 1 ∨ B.Prime) (hW : 0 < W) (hBW : B.Coprime W) :
    1 / (2 * (W : ℝ)) ≤ ((B * W).totient : ℝ) / (B * W) := by
  have hBpos : 0 < B := hB.elim (by rintro rfl; omega) Nat.Prime.pos
  have hWpos : (0 : ℝ) < W := by exact_mod_cast hW
  have hphi : (1 : ℝ) ≤ W.totient := by exact_mod_cast Nat.totient_pos.mpr hW
  have hWratio : 1 / (W : ℝ) ≤ (W.totient : ℝ) / W :=
    div_le_div_of_nonneg_right hphi hWpos.le
  calc
    _ = (1 / 2 : ℝ) * (1 / (W : ℝ)) := by ring
    _ ≤ ((B.totient : ℝ) / B) * ((W.totient : ℝ) / W) :=
      mul_le_mul (half_le_totientDensity_of_one_or_prime hB) hWratio (by positivity) (by positivity)
    _ = _ := by rw [Nat.totient_mul hBW, Nat.cast_mul]; ring

theorem exp_neg_le_inv_of_le_exp {A t : ℝ} (hA : 0 < A) (h : A ≤ Real.exp t) :
    Real.exp (-t) ≤ 1 / A := by
  simpa only [Real.exp_neg, one_div] using (one_div_le_one_div_of_le hA h)

theorem totientDensity_ge_exp_dimension {B W k : ℕ} {H : ℝ}
    (hB : B = 1 ∨ B.Prime) (hW : 0 < W) (hBW : B.Coprime W) (hk : 1 ≤ k)
    (hsize : (W : ℝ) ≤ Real.exp (H * (k : ℝ) ^ 2)) :
    Real.exp (-(H + 1) * (k : ℝ) ^ 2) ≤ ((B * W).totient : ℝ) / (B * W) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hkR
  have htwo : (2 : ℝ) ≤ Real.exp ((k : ℝ) ^ 2) := by
    have h := Real.add_one_le_exp ((k : ℝ) ^ 2)
    linarith
  have hsize2 : 2 * (W : ℝ) ≤ Real.exp ((H + 1) * (k : ℝ) ^ 2) := by
    calc
      _ ≤ Real.exp ((k : ℝ) ^ 2) * Real.exp (H * (k : ℝ) ^ 2) :=
        mul_le_mul htwo hsize (Nat.cast_nonneg W) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hA : (0 : ℝ) < 2 * W := by exact_mod_cast Nat.mul_pos (by omega : 0 < 2) hW
  have h := exp_neg_le_inv_of_le_exp hA hsize2
  have he : Real.exp (-(H + 1) * (k : ℝ) ^ 2) ≤ 1 / (2 * (W : ℝ)) := by
    simpa only [neg_mul] using h
  exact he.trans (inv_two_mul_presieve_le_totientDensity hB hW hBW)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.inv_two_mul_presieve_le_totientDensity
#print axioms Erdos4b.FGKMT.totientDensity_ge_exp_dimension
