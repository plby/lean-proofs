/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterKernelBounds

/-!
# Numerical parameters for the localized kernel
-/

open scoped BigOperators

namespace Erdos984

noncomputable section

/-- A convenient elementary polynomial upper bound for a negative
exponential. -/
lemma exp_neg_le_div_pow {x : ℝ} (hx : 0 < x) (n : ℕ) (hn : 0 < n) :
    Real.exp (-x) ≤ ((n : ℝ) / x) ^ n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hratio : 0 < x / n := div_pos hx hnreal
  have hbase : x / n ≤ Real.exp (x / n) := by
    calc
      x / n ≤ x / n + 1 := by linarith
      _ ≤ Real.exp (x / n) := Real.add_one_le_exp _
  have hpow : (x / n) ^ n ≤ Real.exp x := by
    calc
      (x / n) ^ n ≤ (Real.exp (x / n)) ^ n :=
        pow_le_pow_left₀ hratio.le hbase n
      _ = Real.exp x := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
  rw [Real.exp_neg]
  have hinv := (inv_le_inv₀ (Real.exp_pos x)
    (pow_pos hratio n)).2 hpow
  rw [← inv_pow, inv_div] at hinv
  exact hinv

/-- The zero Fourier coefficient of the product kernel. -/
def hunterKernelMean (D : ℕ) : ℝ :=
  kernelMean1 (hunterKernelPower D) ^ D

/-- The constant removed from the kernel. -/
def hunterKernelCutoff (D : ℕ) : ℝ := hunterKernelMean D / 2

lemma hunterKernelMean_pos (D : ℕ) : 0 < hunterKernelMean D := by
  exact pow_pos (kernelMean1_pos _) _

lemma hunterKernelCutoff_pos (D : ℕ) : 0 < hunterKernelCutoff D := by
  exact div_pos (hunterKernelMean_pos D) (by norm_num)

lemma hunterKernelMean_lower (D : ℕ) :
    ((1 : ℝ) / (2 * hunterKernelPower D + 1)) ^ D ≤
      hunterKernelMean D := by
  exact pow_le_pow_left₀ (by positivity)
    (one_div_two_mul_add_one_le_kernelMean1 _) D

lemma two_mul_hunterKernelPower_add_one_le (D : ℕ) (hD : 2 ≤ D) :
    2 * hunterKernelPower D + 1 ≤ D ^ 252 := by
  have hp : 0 < D ^ 250 := pow_pos (by omega) _
  calc
    2 * hunterKernelPower D + 1 ≤ 3 * D ^ 250 := by
      simp only [hunterKernelPower]
      omega
    _ ≤ D ^ 2 * D ^ 250 := by
      gcongr
      nlinarith
    _ = D ^ 252 := by rw [← pow_add]

lemma hunterKernel_exp_le_cutoff (D : ℕ) (hD : 4 ≤ D) :
    Real.exp (-4 * hunterKernelPower D * hunterRho D ^ 2) ≤
      hunterKernelCutoff D := by
  have hDpos : (0 : ℝ) < D := by positivity
  have hDtwo : (2 : ℝ) ≤ D := by exact_mod_cast (show 2 ≤ D by omega)
  have hx : 0 < 4 * (hunterKernelPower D : ℝ) * hunterRho D ^ 2 := by
    exact mul_pos (mul_pos (by norm_num)
      (by exact_mod_cast hunterKernelPower_pos (by omega)))
      (sq_pos_of_pos (hunterRho_pos (by omega)))
  have hexp := exp_neg_le_div_pow hx (6 * D) (by omega)
  have hx_eq : 4 * (hunterKernelPower D : ℝ) * hunterRho D ^ 2 =
      4 * (D : ℝ) ^ 50 := by
    simp only [hunterKernelPower, hunterRho, Nat.cast_pow]
    rw [inv_pow]
    field_simp
  rw [hx_eq] at hexp
  have hratio : ((6 * D : ℕ) : ℝ) / (4 * (D : ℝ) ^ 50) ≤
      ((D : ℝ) ^ 48)⁻¹ := by
    push_cast
    rw [inv_eq_one_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hcoef : (6 : ℝ) ≤ 4 * D := by linarith
    calc
      (6 : ℝ) * (D : ℝ) * (D : ℝ) ^ 48 =
          6 * (D : ℝ) ^ 49 := by ring
      _ ≤ (4 * (D : ℝ)) * (D : ℝ) ^ 49 :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = 4 * (D : ℝ) ^ 50 := by ring
      _ = 1 * (4 * (D : ℝ) ^ 50) := by ring
  have hfirst :
      (((6 * D : ℕ) : ℝ) / (4 * (D : ℝ) ^ 50)) ^ (6 * D) ≤
        (((D : ℝ) ^ 48)⁻¹) ^ (6 * D) := by
    exact pow_le_pow_left₀ (by positivity) hratio _
  have hpowcut : (((D : ℝ) ^ 48)⁻¹) ^ (6 * D) ≤
      (1 : ℝ) / 2 * (((D : ℝ) ^ 252)⁻¹) ^ D := by
    rw [inv_pow, ← pow_mul, inv_pow, ← pow_mul]
    have htwo : (2 : ℝ) ≤ (D : ℝ) ^ (36 * D) := by
      calc
        (2 : ℝ) ≤ D := hDtwo
        _ ≤ (D : ℝ) ^ (36 * D) := by
          rw [show 36 * D = (36 * D - 1) + 1 by omega, pow_succ]
          exact le_mul_of_one_le_left hDpos.le
            (one_le_pow₀ (by linarith : (1 : ℝ) ≤ D))
    have hden : (1 : ℝ) / 2 * ((D : ℝ) ^ (252 * D))⁻¹ =
        (2 * (D : ℝ) ^ (252 * D))⁻¹ := by
      field_simp
    rw [hden]
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    calc
      2 * (D : ℝ) ^ (252 * D) ≤
          (D : ℝ) ^ (36 * D) * (D : ℝ) ^ (252 * D) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = (D : ℝ) ^ (48 * (6 * D)) := by
        rw [← pow_add]
        congr 1
        ring
  calc
    Real.exp (-4 * hunterKernelPower D * hunterRho D ^ 2) ≤
        (((6 * D : ℕ) : ℝ) / (4 * (D : ℝ) ^ 50)) ^ (6 * D) := by
      rw [show -4 * (hunterKernelPower D : ℝ) * hunterRho D ^ 2 =
          -(4 * (D : ℝ) ^ 50) by
        calc
          -4 * (hunterKernelPower D : ℝ) * hunterRho D ^ 2 =
              -(4 * (hunterKernelPower D : ℝ) * hunterRho D ^ 2) := by ring
          _ = -(4 * (D : ℝ) ^ 50) := congrArg Neg.neg hx_eq]
      exact hexp
    _ ≤ (((D : ℝ) ^ 48)⁻¹) ^ (6 * D) := hfirst
    _ ≤ (1 : ℝ) / 2 * (((D : ℝ) ^ 252)⁻¹) ^ D := hpowcut
    _ ≤ (1 : ℝ) / 2 *
        ((1 : ℝ) / (2 * hunterKernelPower D + 1)) ^ D := by
      gcongr
      rw [one_div]
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      exact_mod_cast two_mul_hunterKernelPower_add_one_le D (by omega)
    _ ≤ hunterKernelCutoff D := by
      rw [hunterKernelCutoff]
      nlinarith [hunterKernelMean_lower D]

lemma torusCosineKernel_re_le_cutoff_of_lt_norm
    (D : ℕ) (hD : 4 ≤ D) (x : UnitAddTorus (Fin D))
    (hx : hunterRho D < ‖x‖) :
    (torusCosineKernel (hunterKernelPower D) x).re ≤
      hunterKernelCutoff D := by
  let _ : Nonempty (Fin D) := ⟨⟨0, by omega⟩⟩
  exact (torusCosineKernel_re_le_exp_of_lt_norm _ x
    (hunterRho_pos (by omega)).le hx).trans (hunterKernel_exp_le_cutoff D hD)

lemma torusCosineKernel_re_le_cutoff_of_rho_sq_le_squaredNorm
    (D : ℕ) (hD : 4 ≤ D) (x : UnitAddTorus (Fin D))
    (hx : hunterRho D ^ 2 ≤ squaredNorm (centeredTorusLift x)) :
    (torusCosineKernel (hunterKernelPower D) x).re ≤
      hunterKernelCutoff D := by
  calc
    (torusCosineKernel (hunterKernelPower D) x).re ≤
        Real.exp (-4 * hunterKernelPower D *
          squaredNorm (centeredTorusLift x)) :=
      torusCosineKernel_re_le_exp_squaredNorm _ _
    _ ≤ Real.exp (-4 * hunterKernelPower D * hunterRho D ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hk : (0 : ℝ) ≤ hunterKernelPower D := by positivity
      nlinarith
    _ ≤ hunterKernelCutoff D := hunterKernel_exp_le_cutoff D hD

end

end Erdos984
