/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffineCoprime

open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

private lemma mul_affine_slope_core
    (p n m c q : ℕ) (hpc : p * c = q) :
    p * (n * m * c * q) = n * (m * q ^ 2) := by
  rw [pow_two]
  calc
    p * (n * m * c * q) = (p * c) * (n * m * q) := by ac_rfl
    _ = q * (n * m * q) := by rw [hpc]
    _ = n * (m * (q * q)) := by ac_rfl

private lemma mul_affine_form_core
    (p n m c q t r : ℕ) (hpc : p * c = q) :
    p * (n * m * c * q * t) + (n * m * r + 1) =
      n * (m * q ^ 2 * t + m * r) + 1 := by
  rw [← hpc]
  ring

lemma affineSlope16_factorization (i : Fin 16) :
    affineSlope16 i =
      keyNumber16 i * keyCommonMultiplier16 * affinePower16Cofactor i *
        affinePower16Product := rfl

lemma keyPower16_mul_affineConstant16_common (i : Fin 16) :
    keyPower16 i * affineConstant16 i =
      keyNumber16 i * (keyCommonMultiplier16 * affineCRT16Parameter) + 1 := by
  rw [keyPower16_mul_affineConstant16, keyCongruence16Coefficient, mul_assoc]

lemma keyPower16_dvd_affinePower16Product (i : Fin 16) :
    keyPower16 i ∣ affinePower16Product := by
  simpa only [affinePower16Product] using
    (Finset.dvd_prod_of_mem keyPower16 (Finset.mem_univ i))

lemma keyPower16_mul_affinePower16Cofactor (i : Fin 16) :
    keyPower16 i * affinePower16Cofactor i = affinePower16Product := by
  exact Nat.mul_div_cancel' (keyPower16_dvd_affinePower16Product i)

lemma affineConstant16_coprime_keyPower16_all (i j : Fin 16) :
    (affineConstant16 i).Coprime (keyPower16 j) := by
  rw [keyPower16]
  exact Nat.Coprime.pow_right _ (affineConstant16_coprime_keyAuxPrime16 i j)

lemma affineConstant16_coprime_affinePower16Product (i : Fin 16) :
    (affineConstant16 i).Coprime affinePower16Product := by
  rw [affinePower16Product]
  exact Nat.Coprime.prod_right fun j _ ↦
    affineConstant16_coprime_keyPower16_all i j

lemma affineConstant16_coprime_commonCore16 (i : Fin 16) :
    (affineConstant16 i).Coprime
      (keyCommonMultiplier16 * affinePower16Product) :=
  (affineConstant16_coprime_keyCommonMultiplier16 i).mul_right
    (affineConstant16_coprime_affinePower16Product i)

lemma affineForm16_coprime_keyPower16 (i : Fin 16) (t : ℕ) :
    (affineForm16 i t).Coprime (keyPower16 i) := by
  have hdiv : keyPower16 i ∣
      keyCongruence16Coefficient i * affinePower16Cofactor i *
        affinePower16Product * t := by
    apply dvd_mul_of_dvd_left _ t
    apply dvd_mul_of_dvd_right (keyPower16_dvd_affinePower16Product i) _
  rw [affineForm16, Nat.add_coprime_iff_right hdiv]
  exact affineConstant16_coprime_keyPower16 i

/-- Multiplication by the attached prime power puts every affine form on a
single common linear core. -/
lemma keyPower16_mul_affineForm16 (i : Fin 16) (t : ℕ) :
    keyPower16 i * affineForm16 i t =
      keyNumber16 i *
          (keyCommonMultiplier16 * affinePower16Product ^ 2 * t +
            keyCommonMultiplier16 * affineCRT16Parameter) + 1 := by
  rw [affineForm16, mul_add, keyPower16_mul_affineConstant16,
    keyCongruence16Coefficient]
  exact mul_affine_form_core _ _ _ _ _ _ _
    (keyPower16_mul_affinePower16Cofactor i)

/-- Coefficient comparison in the common-core identity. -/
lemma keyPower16_mul_affineSlope16 (i : Fin 16) :
    keyPower16 i * affineSlope16 i =
      keyNumber16 i * (keyCommonMultiplier16 * affinePower16Product ^ 2) := by
  rw [affineSlope16, keyCongruence16Coefficient]
  exact mul_affine_slope_core _ _ _ _ _
    (keyPower16_mul_affinePower16Cofactor i)

lemma keyNumber16_dvd_commonMultiplier (i : Fin 16) :
    keyNumber16 i ∣ keyCommonMultiplier16 := by
  rw [keyCommonMultiplier16]
  apply dvd_mul_of_dvd_right _ (Nat.factorial 16)
  exact Finset.dvd_prod_of_mem (f := keyNumber16) (Finset.mem_univ i)

lemma keyGcdQuotient_dvd_commonMultiplier (i j : Fin 16) :
    keyNumber16 i / (keyNumber16 i).gcd (keyNumber16 j) ∣
      keyCommonMultiplier16 := by
  apply dvd_trans _ (keyNumber16_dvd_commonMultiplier i)
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

lemma affineConstant16_pos (i : Fin 16) : 0 < affineConstant16 i := by
  have hnum : 0 <
      keyCongruence16Coefficient i * affineCRT16Parameter + 1 := by positivity
  have hr : 0 < keyPower16 i := (keyPower16_gt_one i).trans' Nat.zero_lt_one
  have heq := keyPower16_mul_affineConstant16 i
  by_contra h
  have hy : affineConstant16 i = 0 := Nat.eq_zero_of_not_pos h
  rw [hy, mul_zero] at heq
  omega

lemma affinePower16Product_pos : 0 < affinePower16Product := by
  exact Finset.prod_pos fun i _ => (keyPower16_gt_one i).trans' Nat.zero_lt_one

lemma keyCommonMultiplier16_pos : 0 < keyCommonMultiplier16 := by
  rw [keyCommonMultiplier16]
  exact mul_pos (Nat.factorial_pos 16) (Finset.prod_pos fun i _ ↦
    (keyNumber16_gt_one i).trans' Nat.zero_lt_one)

lemma affinePower16Cofactor_pos (i : Fin 16) : 0 < affinePower16Cofactor i := by
  have heq := keyPower16_mul_affinePower16Cofactor i
  by_contra h
  have hz : affinePower16Cofactor i = 0 := Nat.eq_zero_of_not_pos h
  rw [hz, mul_zero] at heq
  exact (Nat.ne_of_gt affinePower16Product_pos) heq.symm

lemma affineSlope16_pos (i : Fin 16) : 0 < affineSlope16 i := by
  unfold affineSlope16 keyCongruence16Coefficient
  exact mul_pos (mul_pos (mul_pos (keyNumber16_gt_one i |>.trans' Nat.zero_lt_one)
    keyCommonMultiplier16_pos) (affinePower16Cofactor_pos i)) affinePower16Product_pos

end Erdos946.SixteenAffine
