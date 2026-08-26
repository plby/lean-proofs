import ErdosProblems.Erdos421.ZetaPolynomialParameters
import ErdosProblems.Erdos421.ZetaPolynomialEnvelopePower

/-! # Explicit exponential domination of the polynomial-degree envelope -/

namespace Erdos421

theorem two_pow_le_real_exp (n : ℕ) : (2 : ℝ) ^ n ≤ Real.exp (n : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ (Real.exp 1) ^ n := pow_le_pow_left₀ (by norm_num) htwo n
    _ = _ := by rw [← Real.exp_nat_mul]; simp only [mul_one]

theorem polynomialZetaStripConstant_exp_bound (K : ℕ) :
    polynomialZetaStripConstant K + 64 ≤ Real.exp (1807 * ((K : ℝ) + 1) ^ 11) := by
  have hb := (polynomialZetaStripConstant_add_sixty_four_le K).trans
    (two_pow_le_real_exp (1807 * (K + 1) ^ 11))
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hb

theorem polynomialDetector_height_growth_bound {K : ℕ} (hK : 0 < K) {T : ℝ}
    (hT : 0 < T) (hlog : Real.log T ≤ ((K : ℝ) + 1) ^ 16) :
    T ^ (polynomialDetectorScale K / (K : ℝ)) ≤
      Real.exp (((K : ℝ) + 1) ^ 12 / 8) := by
  have hKp : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hx : 0 < (K : ℝ) + 1 := by positivity
  have hR := polynomialDetectorScale_pos K
  rw [Real.rpow_def_of_pos hT]
  apply Real.exp_le_exp.mpr
  have hl := mul_le_mul_of_nonneg_right hlog (div_nonneg hR.le hKp.le)
  apply hl.trans
  have he : ((K : ℝ) + 1) ^ 16 * (polynomialDetectorScale K / (K : ℝ)) =
      (((K : ℝ) + 1) / (131072 * (K : ℝ))) * ((K : ℝ) + 1) ^ 12 := by
    unfold polynomialDetectorScale
    field_simp
  rw [he]
  have hc : ((K : ℝ) + 1) / (131072 * (K : ℝ)) ≤ 1 / 8 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right hc (pow_nonneg hx.le 12)
  nlinarith only [hm]

theorem polynomialDetector_envelope_exp_bound {K : ℕ} (hK : 7228 ≤ K)
    {B T : ℝ} (hB : 0 ≤ B) (hBX : 1 + 13107200 * (B + 2) ≤ (K : ℝ) + 1)
    (hT : 3 ≤ T) (hlog : 1 ≤ Real.log T) (hlogupper : Real.log T ≤ ((K : ℝ) + 1) ^ 16) :
    polynomialZetaEnvelope K (polynomialDetectorScale K)
        (2 * T + polynomialDetectorScale K) * (1 + 1 / polynomialDetectorRadius K B) ≤
      Real.exp (polynomialDetectorAmplitude K) := by
  let x : ℝ := (K : ℝ) + 1
  have hx : 1 ≤ x := by dsimp only [x]; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have hxlarge : 7228 ≤ x := by
    have h : (7228 : ℝ) ≤ K := by exact_mod_cast hK
    dsimp only [x]
    linarith
  have hTp : 0 < T := by linarith
  have hR := polynomialDetectorScale_pos K
  have hR1 := polynomialDetectorScale_le_one K
  have hu := polynomialDetectorRadius_pos K hB
  have henv := polynomialZetaEnvelope_dilated_bound (by omega : 0 < K) hR.le hR1 hT hlog
  have hconst := polynomialZetaStripConstant_exp_bound K
  have hheight := polynomialDetector_height_growth_bound (by omega : 0 < K) hTp hlogupper
  have hrecip := polynomialDetectorRadius_reciprocal_le K hB hBX
  have hmain : polynomialZetaEnvelope K (polynomialDetectorScale K)
      (2 * T + polynomialDetectorScale K) ≤
        Real.exp (1807 * x ^ 11) * Real.exp (x ^ 12 / 8) * x ^ 16 :=
    henv.trans (mul_le_mul
      (mul_le_mul hconst hheight (by positivity) (Real.exp_pos _).le)
      hlogupper (by linarith) (by positivity))
  have hprod := mul_le_mul hmain hrecip (by positivity) (by positivity)
  have hpow : x ^ 32 ≤ Real.exp (32 * x) := by
    have hxe : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    calc
      _ ≤ (Real.exp x) ^ 32 := pow_le_pow_left₀ (by linarith) hxe _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hcoeff : 1807 * x ^ 11 ≤ x ^ 12 / 4 := by
    have hm := mul_le_mul_of_nonneg_right hxlarge (pow_nonneg (by linarith : 0 ≤ x) 11)
    rw [pow_succ x 11]
    nlinarith only [hm, hx]
  have hlin : 32 * x ≤ x ^ 12 / 8 := by
    have hp : (2 : ℝ) ^ 11 ≤ x ^ 11 := pow_le_pow_left₀ (by norm_num) (by linarith) 11
    norm_num at hp
    have hm := mul_le_mul_of_nonneg_right hp (by linarith : 0 ≤ x)
    rw [pow_succ x 11]
    nlinarith only [hm, hx]
  calc
    _ ≤ (Real.exp (1807 * x ^ 11) * Real.exp (x ^ 12 / 8) * x ^ 16) * x ^ 16 := hprod
    _ = (Real.exp (1807 * x ^ 11) * Real.exp (x ^ 12 / 8)) * x ^ 32 := by ring
    _ ≤ (Real.exp (1807 * x ^ 11) * Real.exp (x ^ 12 / 8)) * Real.exp (32 * x) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Real.exp (1807 * x ^ 11 + x ^ 12 / 8 + 32 * x) := by rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (x ^ 12) := Real.exp_le_exp.mpr (by
      nlinarith [pow_nonneg (by linarith : 0 ≤ x) 12])
    _ = _ := rfl

end Erdos421
