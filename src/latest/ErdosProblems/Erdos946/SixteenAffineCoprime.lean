/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffineCRT

open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

/-- Constant term of the `i`th affine form. -/
noncomputable def affineConstant16 (i : Fin 16) : ℕ :=
  (keyCongruence16Coefficient i * affineCRT16Parameter + 1) / keyPower16 i

/-- Product of the sixteen attached prime powers. -/
noncomputable def affinePower16Product : ℕ :=
  ∏ i : Fin 16, keyPower16 i

/-- The product of all attached powers except the `i`th one. -/
noncomputable def affinePower16Cofactor (i : Fin 16) : ℕ :=
  affinePower16Product / keyPower16 i

/-- Heath-Brown's sixteen affine forms. -/
noncomputable def affineForm16 (i : Fin 16) (t : ℕ) : ℕ :=
  keyCongruence16Coefficient i * affinePower16Cofactor i *
      affinePower16Product * t + affineConstant16 i

/-- Slope of the `i`th member of the explicit affine family. -/
noncomputable def affineSlope16 (i : Fin 16) : ℕ :=
  keyCongruence16Coefficient i * affinePower16Cofactor i * affinePower16Product

@[simp] lemma affineForm16_eq_slope_mul_add (i : Fin 16) (t : ℕ) :
    affineForm16 i t = affineSlope16 i * t + affineConstant16 i := rfl

lemma keyPower16_dvd_affineNumerator (i : Fin 16) :
    keyPower16 i ∣ keyCongruence16Coefficient i * affineCRT16Parameter + 1 := by
  have h := Nat.ModEq.of_dvd
    (show keyPower16 i ∣ (keyPower16 i) ^ 2 by
      exact ⟨keyPower16 i, by simp [pow_two]⟩)
    (affineCRT16_congruence i)
  exact Nat.modEq_zero_iff_dvd.mp (h.trans Nat.modulus_modEq_zero)

lemma keyPower16_mul_affineConstant16 (i : Fin 16) :
    keyPower16 i * affineConstant16 i =
      keyCongruence16Coefficient i * affineCRT16Parameter + 1 := by
  exact Nat.mul_div_cancel' (keyPower16_dvd_affineNumerator i)

lemma affineConstant16_modEq_one (i : Fin 16) :
    affineConstant16 i ≡ 1 [MOD keyPower16 i] := by
  apply Nat.ModEq.mul_left_cancel'
    (Nat.ne_of_gt ((keyPower16_gt_one i).trans' Nat.zero_lt_one))
  have h := affineCRT16_congruence i
  rw [← keyPower16_mul_affineConstant16 i] at h
  simpa [pow_two] using h

lemma affineConstant16_coprime_keyPower16 (i : Fin 16) :
    (affineConstant16 i).Coprime (keyPower16 i) := by
  apply Nat.coprime_of_mul_modEq_one 1
  simpa using affineConstant16_modEq_one i

lemma affineConstant16_coprime_keyCommonMultiplier16 (i : Fin 16) :
    (affineConstant16 i).Coprime keyCommonMultiplier16 := by
  apply Nat.coprime_of_dvd'
  intro p hp hpc hpM
  have hleft : p ∣ keyPower16 i * affineConstant16 i :=
    dvd_mul_of_dvd_right hpc _
  rw [keyPower16_mul_affineConstant16] at hleft
  let T := keyCongruence16Coefficient i * affineCRT16Parameter
  have hterm : p ∣ T := by
    apply dvd_mul_of_dvd_left _ _
    dsimp [keyCongruence16Coefficient]
    exact dvd_mul_of_dvd_right hpM _
  change p ∣ T + 1 at hleft
  have hone : p ∣ 1 := by
    simpa using Nat.dvd_sub hleft hterm
  exact hone

lemma keyAuxPrime16_dvd_keyPower16 (i : Fin 16) :
    keyAuxPrime16 i ∣ keyPower16 i := by
  rw [keyPower16]
  exact dvd_pow_self _
    (Nat.sub_ne_zero_of_lt (sigma_zero_keyNumber16_ge_two i))

/-- A constant term is prime to every attached auxiliary prime, including
the seven primes belonging to the other forms. -/
lemma affineConstant16_coprime_keyAuxPrime16 (i j : Fin 16) :
    (affineConstant16 i).Coprime (keyAuxPrime16 j) := by
  have hp := keyAuxPrime16_prime j
  apply Nat.Coprime.symm
  rw [hp.coprime_iff_not_dvd]
  intro hqConst
  by_cases hij : i = j
  · subst j
    have hc : (affineConstant16 i).Coprime (keyAuxPrime16 i) :=
      Nat.Coprime.of_dvd_right (keyAuxPrime16_dvd_keyPower16 i)
        (affineConstant16_coprime_keyPower16 i)
    exact (hp.coprime_iff_not_dvd.mp hc.symm) hqConst
  · have hqNumeratorI : keyAuxPrime16 j ∣
        keyCongruence16Coefficient i * affineCRT16Parameter + 1 := by
      rw [← keyPower16_mul_affineConstant16 i]
      exact dvd_mul_of_dvd_right hqConst _
    have hqNumeratorJ : keyAuxPrime16 j ∣
        keyCongruence16Coefficient j * affineCRT16Parameter + 1 := by
      rw [← keyPower16_mul_affineConstant16 j]
      exact dvd_mul_of_dvd_left (keyAuxPrime16_dvd_keyPower16 j) _
    have hXnot : ¬keyAuxPrime16 j ∣ affineCRT16Parameter := by
      intro hqX
      let T := keyCongruence16Coefficient j * affineCRT16Parameter
      have hterm : keyAuxPrime16 j ∣ T :=
        dvd_mul_of_dvd_right hqX _
      change keyAuxPrime16 j ∣ T + 1 at hqNumeratorJ
      have hone : keyAuxPrime16 j ∣ 1 :=
        by simpa using Nat.dvd_sub hqNumeratorJ hterm
      exact hp.not_dvd_one hone
    have hcommon :
        (keyCommonMultiplier16 * affineCRT16Parameter).Coprime
          (keyAuxPrime16 j) :=
      (keyAuxPrime16_coprime_commonMultiplier j).symm.mul_left
        ((hp.coprime_iff_not_dvd.mpr hXnot).symm)
    have hiZero : keyNumber16 i *
          (keyCommonMultiplier16 * affineCRT16Parameter) + 1 ≡ 0
          [MOD keyAuxPrime16 j] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      simpa [keyCongruence16Coefficient, mul_assoc] using hqNumeratorI
    have hjZero : keyNumber16 j *
          (keyCommonMultiplier16 * affineCRT16Parameter) + 1 ≡ 0
          [MOD keyAuxPrime16 j] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      simpa [keyCongruence16Coefficient, mul_assoc] using hqNumeratorJ
    have hmul : keyNumber16 i *
          (keyCommonMultiplier16 * affineCRT16Parameter) ≡
        keyNumber16 j * (keyCommonMultiplier16 * affineCRT16Parameter)
          [MOD keyAuxPrime16 j] :=
      Nat.ModEq.add_right_cancel (Nat.ModEq.refl 1) (hiZero.trans hjZero.symm)
    have hnumbers : keyNumber16 i ≡ keyNumber16 j [MOD keyAuxPrime16 j] :=
      Nat.ModEq.cancel_right_of_coprime hcommon.symm.gcd_eq_one hmul
    have hnot : ¬keyNumber16 i ≡ keyNumber16 j [MOD keyAuxPrime16 j] := by
      intro hnumber
      have hdelta : 1 + keyDelta16 i ≡ 1 + keyDelta16 j
          [MOD keyAuxPrime16 j] :=
        (SixteenKey.keyNumber16_modEq_aux i j).symm.trans
          (hnumber.trans (SixteenKey.keyNumber16_modEq_aux j j))
      exact keyDelta16_aux_separated i j hij hdelta
    exact hnot hnumbers


end Erdos946.SixteenAffine
