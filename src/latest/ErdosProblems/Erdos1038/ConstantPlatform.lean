import Mathlib

/-!
# Algebraic data for constant-platform reference measures

This file records the elementary parameter identities behind equations
`(4.2)`--`(4.10)` of the manuscript.  In particular it proves the sharp
nonnegativity threshold for the reference density and positivity of the
endpoint-corrected adjoint numerator.  The integral identities defining the
actual reference measures are developed separately.
-/

open Set

namespace Erdos1038

noncomputable section

def platformCenter (a : ℝ) : ℝ := (a + 2) / 2

def platformRadius (a : ℝ) : ℝ := (2 - a) / 2

def platformCapacity (a : ℝ) : ℝ := (2 - a) / 4

def platformD0 (a : ℝ) : ℝ :=
  (a + 2 + 2 * Real.sqrt (2 * a)) / 4

def platformDensityCoefficient (k a d : ℝ) : ℝ :=
  k + 1 - k * Real.sqrt (2 * a) / d

def platformThreshold (k : ℝ) : ℝ :=
  2 * (k / (k + 1)) ^ 2

lemma platformCenter_sub_radius (a : ℝ) :
    platformCenter a - platformRadius a = a := by
  simp [platformCenter, platformRadius]
  ring

lemma platformCenter_add_radius (a : ℝ) :
    platformCenter a + platformRadius a = 2 := by
  simp [platformCenter, platformRadius]
  ring

lemma platformRadius_pos {a : ℝ} (ha : a < 2) :
    0 < platformRadius a := by
  simp [platformRadius]
  linarith

lemma platformCapacity_pos {a : ℝ} (ha : a < 2) :
    0 < platformCapacity a := by
  simp [platformCapacity]
  linarith

lemma platformThreshold_nonneg {k : ℝ} : 0 ≤ platformThreshold k := by
  exact mul_nonneg (by norm_num) (sq_nonneg _)

lemma platformDensityCoefficient_monoOn {k a : ℝ}
    (hk : 0 ≤ k) (ha : 0 < a) :
    MonotoneOn (platformDensityCoefficient k a) (Ici a) := by
  intro d hd e he hde
  have hd0 : 0 < d := ha.trans_le hd
  have he0 : 0 < e := hd0.trans_le hde
  have hsqrt : 0 ≤ Real.sqrt (2 * a) := Real.sqrt_nonneg _
  have hdiv : Real.sqrt (2 * a) / e ≤ Real.sqrt (2 * a) / d := by
    exact div_le_div_of_nonneg_left hsqrt hd0 hde
  unfold platformDensityCoefficient
  apply sub_le_sub_left
  simpa [mul_div_assoc] using! mul_le_mul_of_nonneg_left hdiv hk

lemma platformThreshold_iff_square {k a : ℝ} (hk : 0 ≤ k) :
    platformThreshold k ≤ a ↔ 2 * k ^ 2 ≤ a * (k + 1) ^ 2 := by
  have hk1 : 0 < k + 1 := by linarith
  rw [platformThreshold]
  constructor
  · intro h
    have hmul := mul_le_mul_of_nonneg_right h (sq_nonneg (k + 1))
    field_simp [hk1.ne'] at hmul
    nlinarith
  · intro h
    rw [show k / (k + 1) = k * (k + 1)⁻¹ by ring]
    rw [mul_pow]
    field_simp [hk1.ne']
    nlinarith

lemma platformDensityCoefficient_at_left_nonneg_iff
    {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) :
    0 ≤ platformDensityCoefficient k a a ↔ platformThreshold k ≤ a := by
  have hk1 : 0 < k + 1 := by linarith
  have hsqrt0 : 0 ≤ Real.sqrt (2 * a) := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt (2 * a)) ^ 2 = 2 * a :=
    Real.sq_sqrt (by positivity)
  rw [platformThreshold_iff_square hk]
  unfold platformDensityCoefficient
  rw [sub_nonneg, div_le_iff₀ ha]
  have hleft : 0 ≤ k * Real.sqrt (2 * a) := mul_nonneg hk hsqrt0
  have hright : 0 ≤ (k + 1) * a := mul_nonneg hk1.le ha.le
  rw [← (sq_le_sq₀ hleft hright)]
  rw [mul_pow, hsqrtSq, mul_pow]
  constructor <;> intro h
  · nlinarith [mul_pos ha (show 0 < a by exact ha)]
  · nlinarith [mul_pos ha (show 0 < a by exact ha)]

theorem platformDensityCoefficient_nonneg_iff
    {k a : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (ha2 : a ≤ 2) :
    (∀ d ∈ Icc a 2, 0 ≤ platformDensityCoefficient k a d) ↔
      platformThreshold k ≤ a := by
  constructor
  · intro h
    exact (platformDensityCoefficient_at_left_nonneg_iff hk ha).1
      (h a ⟨le_rfl, by linarith⟩)
  · intro hthreshold d hd
    have hleft :=
      (platformDensityCoefficient_at_left_nonneg_iff hk ha).2 hthreshold
    exact hleft.trans
      (platformDensityCoefficient_monoOn hk ha
        (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hd.1) hd.1)

def platformCrossingScale (a x : ℝ) : ℝ :=
  Real.sqrt ((a - x) * (2 - x))

def adjointNormalization
    (a xMinus xPlus sigmaMinus sigmaPlus : ℝ) : ℝ :=
  sigmaMinus * platformCrossingScale a xMinus / (a - xMinus) +
    sigmaPlus * platformCrossingScale a xPlus / (a - xPlus)

def adjointNumerator
    (a xMinus xPlus sigmaMinus sigmaPlus d : ℝ) : ℝ :=
  adjointNormalization a xMinus xPlus sigmaMinus sigmaPlus -
    sigmaMinus * platformCrossingScale a xMinus / (d - xMinus) -
    sigmaPlus * platformCrossingScale a xPlus / (d - xPlus)

lemma platformCrossingScale_pos {a x : ℝ} (hxa : x < a) (ha2 : a < 2) :
    0 < platformCrossingScale a x := by
  rw [platformCrossingScale]
  apply Real.sqrt_pos.2
  exact mul_pos (sub_pos.mpr hxa) (sub_pos.mpr (hxa.trans ha2))

@[simp]
lemma adjointNumerator_at_left
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a) :
    adjointNumerator a xMinus xPlus sigmaMinus sigmaPlus a = 0 := by
  unfold adjointNumerator adjointNormalization
  field_simp [(sub_pos.mpr hxMinus).ne', (sub_pos.mpr hxPlus).ne']
  ring

lemma adjoint_fraction_strictMonoOn
    {a x sigma : ℝ} (hxa : x < a) (hsigma : 0 < sigma) :
    StrictMonoOn (fun d ↦ -(sigma / (d - x))) (Ici a) := by
  intro d hd e he hde
  have hdx : 0 < d - x := sub_pos.mpr (hxa.trans_le hd)
  have hex : 0 < e - x := sub_pos.mpr (hxa.trans_le he)
  have hrecip : sigma / (e - x) < sigma / (d - x) := by
    exact div_lt_div_of_pos_left hsigma hdx (sub_lt_sub_right hde x)
  linarith

theorem adjointNumerator_strictMonoOn
    {a xMinus xPlus sigmaMinus sigmaPlus : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) :
    StrictMonoOn
      (adjointNumerator a xMinus xPlus sigmaMinus sigmaPlus) (Ici a) := by
  have hKMinus := platformCrossingScale_pos hxMinus ha2
  have hKPlus := platformCrossingScale_pos hxPlus ha2
  have hminus := adjoint_fraction_strictMonoOn hxMinus
    (mul_pos hsigmaMinus hKMinus)
  have hplus := adjoint_fraction_strictMonoOn hxPlus
    (mul_pos hsigmaPlus hKPlus)
  intro d hd e he hde
  have hm := hminus hd he hde
  have hp := hplus hd he hde
  unfold adjointNumerator
  dsimp only at hm hp
  linarith

theorem adjointNumerator_nonneg_on
    {a xMinus xPlus sigmaMinus sigmaPlus d : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (hd : d ∈ Icc a 2) :
    0 ≤ adjointNumerator a xMinus xPlus sigmaMinus sigmaPlus d := by
  rw [← adjointNumerator_at_left hxMinus hxPlus]
  exact (adjointNumerator_strictMonoOn hxMinus hxPlus
    hsigmaMinus hsigmaPlus ha2).monotoneOn
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hd.1) hd.1

theorem adjointNumerator_pos_of_left_lt
    {a xMinus xPlus sigmaMinus sigmaPlus d : ℝ}
    (hxMinus : xMinus < a) (hxPlus : xPlus < a)
    (hsigmaMinus : 0 < sigmaMinus) (hsigmaPlus : 0 < sigmaPlus)
    (ha2 : a < 2) (had : a < d) :
    0 < adjointNumerator a xMinus xPlus sigmaMinus sigmaPlus d := by
  rw [← adjointNumerator_at_left hxMinus hxPlus]
  exact adjointNumerator_strictMonoOn hxMinus hxPlus
    hsigmaMinus hsigmaPlus ha2
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr had.le) had

end

end Erdos1038
