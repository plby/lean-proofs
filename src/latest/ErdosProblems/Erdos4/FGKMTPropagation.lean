import ErdosProblems.Erdos4.FGKMTCoefficients

/-! A fourth-power input error propagates to a linear output error. -/

namespace Erdos4.FGKMT

theorem roundLoss_fourth (r A : ℕ) {κ δ ε q D : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hεq : ε ≤ q ^ 4) (hδq : δ ≤ q ^ 4) :
    roundLoss r A κ δ ε q D ≤ lossCoefficient r A κ D * q := by
  have hq : q ≤ 1 := by linarith
  have hq4q : q ^ 4 ≤ q := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq0.le hq (by decide : 1 ≤ 4)
  have hδq' : δ ≤ q := hδq.trans hq4q
  have hδ1 : δ ≤ 1 := hδq'.trans hq
  have hδ2 : δ ^ 2 ≤ q := by nlinarith
  have hN := normalizationError_fourth r hκ hδ hε hq0 hq1 hεq hδq
  have hV := degreeVariance_fourth r hκ hδ hε hD hq0 hq1 hεq hδq
  have hn : 2 * (normalizationError r κ δ ε q * (A : ℝ) * D / κ ^ r) / κ ^ A ≤
      (2 * (normalizerCoefficient r κ * (A : ℝ) * D / κ ^ r) / κ ^ A) * q := by
    calc
      _ ≤ 2 * ((normalizerCoefficient r κ * q) * (A : ℝ) * D / κ ^ r) / κ ^ A := by
        apply div_le_div_of_nonneg_right _ (pow_pos hκ A).le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply div_le_div_of_nonneg_right _ (pow_pos hκ r).le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg A)) hD
      _ = _ := by ring
  have ho : (A : ℝ) ^ 2 * δ / κ ^ r ≤ ((A : ℝ) ^ 2 / κ ^ r) * q := by
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hδq' (sq_nonneg _)) (pow_pos hκ r).le).trans_eq (by ring)
  have hv : (A : ℝ) * (2 * Real.sqrt (degreeVariance r κ δ ε D) / κ ^ A) ≤
      ((A : ℝ) * (2 * degreeCoefficient r κ D / κ ^ A)) * q := by
    calc
      _ ≤ (A : ℝ) * (2 * (degreeCoefficient r κ D * q) / κ ^ A) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hV (by norm_num))
            (pow_pos hκ A).le) (Nat.cast_nonneg A)
      _ = _ := by ring
  have hs : 4 * (A : ℝ) ^ 2 * δ ^ 2 / κ ^ (2 * r) ≤
      (4 * (A : ℝ) ^ 2 / κ ^ (2 * r)) * q := by
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hδ2 (by positivity)) (pow_pos hκ _).le).trans_eq (by ring)
  exact (add_le_add (add_le_add (add_le_add hn ho) hv) hs).trans_eq
    (by unfold lossCoefficient; ring)

theorem roundNextError_fourth (r A : ℕ) {κ δ ε q D : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hD : 0 ≤ D)
    (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (hεq : ε ≤ q ^ 4) (hδq : δ ≤ q ^ 4) :
    roundNextError r A κ δ ε q D ≤ propagationCoefficient r A κ D * q := by
  have hq : q ≤ 1 := by linarith
  have hq4q : q ^ 4 ≤ q := by
    simpa only [pow_one] using pow_le_pow_of_le_one hq0.le hq (by decide : 1 ≤ 4)
  have hεq' := hεq.trans hq4q
  have hε1 : ε ≤ 1 := hεq'.trans hq
  have hloss := roundLoss_fourth r A hκ hδ hε hD hq0 hq1 hεq hδq
  have hloss0 := roundLoss_nonneg r A hκ hδ hε hq0.le hD
  have hfactor : (1 + ε) * Real.exp ((A : ℝ) * D) ≤ 2 * Real.exp ((A : ℝ) * D) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  have hmul := mul_le_mul hfactor hloss hloss0 (by positivity)
  exact (add_le_add hεq' hmul).trans_eq (by unfold propagationCoefficient; ring)

end Erdos4.FGKMT
