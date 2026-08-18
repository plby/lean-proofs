/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterResonance

/-!
# Bounds for character sums along finite torus orbits
-/

open Set Function MeasureTheory AddCircle
open scoped BigOperators

namespace Erdos984

noncomputable section

lemma torusFourier_eq_character_fourier
    {D : Type*} [Fintype D] (xi : D → ℤ) (x : UnitAddTorus D) :
    torusFourier xi x = fourier 1 (integerCharacter xi x) := by
  classical
  rw [torusFourier, integerCharacter_apply]
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih]
      simp only [fourier_apply, one_zsmul]
      rw [← Circle.coe_mul, ← toCircle_add]

lemma torusFourier_point_zero {D : Type*} [Fintype D] (xi : D → ℤ) :
    torusFourier xi (0 : UnitAddTorus D) = 1 := by
  simp [torusFourier, fourier_apply]

lemma torusFourier_nsmul {D : Type*} [Fintype D]
    (xi : D → ℤ) (x : UnitAddTorus D) (n : ℕ) :
    torusFourier xi (n • x) = torusFourier xi x ^ n := by
  induction n with
  | zero => simpa using torusFourier_point_zero xi
  | succ n ih =>
      rw [succ_nsmul, torusFourier_add_point, ih, pow_succ]

/-- Chord length on the unit circle dominates four times the quotient
distance from zero. -/
lemma four_mul_norm_le_norm_fourier_sub_one (y : UnitAddCircle) :
    4 * ‖y‖ ≤ ‖fourier 1 y - 1‖ := by
  let t := centeredCircleLift y
  have ht : |t| ≤ (1 : ℝ) / 2 := centeredCircleLift_abs_le y
  have hangle : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hangle
  have htwo : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    calc
      2 * |t| = 2 / Real.pi * |Real.pi * t| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * t)| := hsin
  rw [norm_eq_abs_centeredCircleLift]
  calc
    4 * |centeredCircleLift y| ≤
        2 * |Real.sin (Real.pi * centeredCircleLift y)| := by
      dsimp [t] at htwo
      linarith
    _ = ‖Complex.exp (Complex.I *
          (2 * Real.pi * centeredCircleLift y : ℝ)) - 1‖ := by
      rw [Complex.norm_exp_I_mul_ofReal_sub_one]
      rw [show (2 * Real.pi * centeredCircleLift y : ℝ) / 2 =
          Real.pi * centeredCircleLift y by ring]
      simp [Real.norm_eq_abs, abs_mul]
    _ = ‖fourier 1 y - 1‖ := by
      congr 2
      calc
        Complex.exp (Complex.I *
            (2 * Real.pi * centeredCircleLift y : ℝ)) =
            fourier 1 ((centeredCircleLift y : ℝ) : UnitAddCircle) := by
          rw [fourier_coe_apply]
          congr 1
          push_cast
          ring
        _ = fourier 1 y := by rw [coe_centeredCircleLift]

lemma norm_geom_sum_le_two_div
    (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (X : ℕ) :
    ‖∑ t ∈ Finset.range X, z ^ t‖ ≤ 2 / ‖z - 1‖ := by
  have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  rw [le_div_iff₀ hden]
  calc
    ‖∑ t ∈ Finset.range X, z ^ t‖ * ‖z - 1‖ =
        ‖(∑ t ∈ Finset.range X, z ^ t) * (z - 1)‖ := norm_mul _ _ |>.symm
    _ = ‖z ^ X - 1‖ := by rw [geom_sum_mul]
    _ ≤ ‖z ^ X‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz]; norm_num

def hunterGeomSum (D : ℕ) (theta : UnitAddTorus (Fin D)) (d : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) : ℂ :=
  ∑ t ∈ Finset.range (hunterX D),
    torusFourier (kernelFrequency (hunterKernelPower D) q) (t • (d • theta))

lemma norm_hunterGeomSum_le_X (D : ℕ)
    (theta : UnitAddTorus (Fin D)) (d : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D)) :
    ‖hunterGeomSum D theta d q‖ ≤ hunterX D := by
  rw [hunterGeomSum]
  calc
    ‖∑ t ∈ Finset.range (hunterX D),
        torusFourier (kernelFrequency (hunterKernelPower D) q)
          (t • (d • theta))‖ ≤
        ∑ _t ∈ Finset.range (hunterX D), (1 : ℝ) := by
      apply norm_sum_le_of_le
      intro t _ht
      exact (norm_torusFourier _ _).le
    _ = hunterX D := by simp

lemma norm_hunterGeomSum_le_of_nonresonant
    (D : ℕ) (hD : 4 ≤ D) (theta : UnitAddTorus (Fin D)) (d : ℕ)
    (q : Fin D → HunterKernelDigit (hunterKernelPower D))
    (hq : q ∉ hunterResonantDigits D theta d) :
    ‖hunterGeomSum D theta d q‖ ≤ 1 / hunterPhaseTolerance D := by
  have hphase : hunterPhaseTolerance D <
      ‖integerCharacter (kernelFrequency (hunterKernelPower D) q) (d • theta)‖ := by
    simpa [hunterResonantDigits] using hq
  let y := integerCharacter (kernelFrequency (hunterKernelPower D) q) (d • theta)
  let z := fourier 1 y
  have hzeq : torusFourier (kernelFrequency (hunterKernelPower D) q)
      (d • theta) = z := torusFourier_eq_character_fourier _ _
  have hz : ‖z‖ = 1 := by
    rw [← hzeq]
    exact norm_torusFourier _ _
  have hchord : 4 * hunterPhaseTolerance D < ‖z - 1‖ := by
    exact (mul_lt_mul_of_pos_left hphase (by norm_num)).trans_le
      (four_mul_norm_le_norm_fourier_sub_one y)
  have hz1 : z ≠ 1 := by
    intro hz1
    rw [hz1, sub_self, norm_zero] at hchord
    have := hunterPhaseTolerance_nonneg D
    linarith
  have hgeom := norm_geom_sum_le_two_div z hz hz1 (hunterX D)
  rw [hunterGeomSum]
  have horbit : (∑ t ∈ Finset.range (hunterX D),
      torusFourier (kernelFrequency (hunterKernelPower D) q)
        (t • (d • theta))) =
      ∑ t ∈ Finset.range (hunterX D), z ^ t := by
    apply Finset.sum_congr rfl
    intro t _ht
    rw [torusFourier_nsmul, hzeq]
  rw [horbit]
  refine hgeom.trans ?_
  have htol : 0 < hunterPhaseTolerance D := by
    unfold hunterPhaseTolerance
    have hDreal : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have hX : (0 : ℝ) < hunterX D := by
      exact_mod_cast pow_pos (show 0 < D by omega) (100000 * D)
    exact div_pos (pow_pos hDreal _) hX
  rw [div_le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz1)) htol]
  nlinarith

end

end Erdos984
