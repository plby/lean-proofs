import ErdosProblems.Erdos4.FGKMTRoundAccuracy

/-! Scalar coefficients for a fourth-power error budget. -/

namespace Erdos4.FGKMT

noncomputable def normalizerCoefficient (r : ℕ) (κ : ℝ) : ℝ := 5 + 2 * (r : ℝ) / κ ^ r

noncomputable def degreeCoefficient (r : ℕ) (κ D : ℝ) : ℝ :=
  1 + 3 * D ^ 2 + 2 * (r : ℝ) * D / κ ^ (r + 1)

noncomputable def lossCoefficient (r A : ℕ) (κ D : ℝ) : ℝ :=
  2 * (normalizerCoefficient r κ * (A : ℝ) * D / κ ^ r) / κ ^ A +
    (A : ℝ) ^ 2 / κ ^ r + (A : ℝ) * (2 * degreeCoefficient r κ D / κ ^ A) +
    4 * (A : ℝ) ^ 2 / κ ^ (2 * r)

noncomputable def propagationCoefficient (r A : ℕ) (κ D : ℝ) : ℝ :=
  1 + 2 * Real.exp ((A : ℝ) * D) * lossCoefficient r A κ D

theorem normalizerCoefficient_nonneg (r : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 ≤ normalizerCoefficient r κ := by unfold normalizerCoefficient; positivity

theorem degreeCoefficient_ge_one (r : ℕ) {κ D : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D) :
    1 ≤ degreeCoefficient r κ D := by
  have hh : 0 ≤ 3 * D ^ 2 + 2 * (r : ℝ) * D / κ ^ (r + 1) := by positivity
  unfold degreeCoefficient
  linarith

theorem lossCoefficient_nonneg (r A : ℕ) {κ D : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D) :
    0 ≤ lossCoefficient r A κ D := by
  have hn := normalizerCoefficient_nonneg r hκ
  have hd : 0 ≤ degreeCoefficient r κ D := (by norm_num : (0 : ℝ) ≤ 1).trans
    (degreeCoefficient_ge_one r hκ hD)
  unfold lossCoefficient
  positivity

theorem propagationCoefficient_ge_one (r A : ℕ) {κ D : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D) :
    1 ≤ propagationCoefficient r A κ D := by
  have hh := lossCoefficient_nonneg r A hκ hD
  have hm : 0 ≤ 2 * Real.exp ((A : ℝ) * D) * lossCoefficient r A κ D := by positivity
  unfold propagationCoefficient
  linarith

theorem normalizationError_fourth (r : ℕ) {κ δ ε q : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2)
    (hεq : ε ≤ q ^ 4) (hδq : δ ≤ q ^ 4) :
    normalizationError r κ δ ε q ≤ normalizerCoefficient r κ * q := by
  have hq : q ≤ 1 := by linarith
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hq4 : q ^ 4 ≤ 1 := pow_le_one₀ hq0.le hq
  have hε1 : ε ≤ 1 := hεq.trans hq4
  have hnum : 3 * ε + (1 + ε) * (r : ℝ) * δ / κ ^ r ≤
      (3 + 2 * (r : ℝ) / κ ^ r) * q ^ 4 := by
    have ha : 3 * ε ≤ 3 * q ^ 4 := mul_le_mul_of_nonneg_left hεq (by norm_num)
    have hb : (1 + ε) * (r : ℝ) * δ ≤ 2 * (r : ℝ) * q ^ 4 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (by linarith : 1 + ε ≤ 2) (Nat.cast_nonneg r))
        hδq hδ (by positivity)
    have hc := div_le_div_of_nonneg_right hb (pow_pos hκ r).le
    exact (add_le_add ha hc).trans_eq (by ring)
  have hcoef : 0 ≤ 3 + 2 * (r : ℝ) / κ ^ r := by positivity
  calc
    _ ≤ 2 * q + ((3 + 2 * (r : ℝ) / κ ^ r) * q ^ 4) / q ^ 2 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right hnum (sq_nonneg q))
    _ = 2 * q + (3 + 2 * (r : ℝ) / κ ^ r) * q ^ 2 := by field_simp
    _ ≤ 2 * q + (3 + 2 * (r : ℝ) / κ ^ r) * q :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hq2 hcoef)
    _ = _ := by unfold normalizerCoefficient; ring

theorem degreeVariance_fourth (r : ℕ) {κ δ ε q D : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hεq : ε ≤ q ^ 4) (hδq : δ ≤ q ^ 4) :
    Real.sqrt (degreeVariance r κ δ ε D) ≤ degreeCoefficient r κ D * q := by
  have hq : q ≤ 1 := by linarith
  have hq2 : q ^ 2 ≤ q := by nlinarith
  have hq4 : q ^ 4 ≤ 1 := pow_le_one₀ hq0.le hq
  have hε1 : ε ≤ 1 := hεq.trans hq4
  have hC1 := degreeCoefficient_ge_one r hκ hD
  have hC0 : 0 ≤ degreeCoefficient r κ D := by linarith
  have hvar : degreeVariance r κ δ ε D ≤
      (3 * D ^ 2 + 2 * (r : ℝ) * D / κ ^ (r + 1)) * q ^ 4 := by
    have ha := mul_le_mul_of_nonneg_left hεq (by positivity : 0 ≤ 3 * D ^ 2)
    have hb : (1 + ε) * δ ≤ 2 * q ^ 4 :=
      mul_le_mul (by linarith) hδq hδ (by norm_num)
    have hc := mul_le_mul_of_nonneg_right hb
      (by positivity : 0 ≤ (r : ℝ) * D / κ ^ (r + 1))
    have hc' : (1 + ε) * (r : ℝ) * δ * D / κ ^ (r + 1) ≤
        2 * (r : ℝ) * D * q ^ 4 / κ ^ (r + 1) := by
      calc
        _ = (1 + ε) * δ * ((r : ℝ) * D / κ ^ (r + 1)) := by ring
        _ ≤ 2 * q ^ 4 * ((r : ℝ) * D / κ ^ (r + 1)) := hc
        _ = _ := by ring
    unfold degreeVariance
    exact (add_le_add ha hc').trans_eq (by ring)
  have hsqrt := Real.sq_sqrt (degreeVariance_nonneg r hκ hδ hε hD)
  have hCsq : 3 * D ^ 2 + 2 * (r : ℝ) * D / κ ^ (r + 1) ≤ degreeCoefficient r κ D ^ 2 := by
    unfold degreeCoefficient at *
    nlinarith
  have hbound := hvar.trans (mul_le_mul_of_nonneg_right hCsq (pow_nonneg hq0.le 4))
  have hs : Real.sqrt (degreeVariance r κ δ ε D) ≤ degreeCoefficient r κ D * q ^ 2 := by
    have hn := Real.sqrt_nonneg (degreeVariance r κ δ ε D)
    have hcq : 0 ≤ degreeCoefficient r κ D * q ^ 2 := mul_nonneg hC0 (sq_nonneg q)
    nlinarith
  exact hs.trans (mul_le_mul_of_nonneg_left hq2 hC0)

end Erdos4.FGKMT
