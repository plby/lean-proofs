import ErdosProblems.Erdos587.HooleyRobustModelExtraction

/-! # Fixed rank-uniform constants for full-width extraction -/

namespace Erdos587.CFP

def deltaExtractionScale (d : ℕ) : ℕ := 32 * 4 ^ d * 4 ^ (d + 1)

def deltaExtractionFactor (d : ℕ) : ℕ := 9 * d * deltaExtractionScale d

lemma delta_extraction_ceil_eq (d : ℕ) :
    ⌈32 * ((4 ^ d : ℕ) : ℝ) / (1 / ((4 ^ (d + 1) : ℕ) : ℝ))⌉₊ =
      deltaExtractionScale d := by
  have heq : 32 * ((4 ^ d : ℕ) : ℝ) / (1 / ((4 ^ (d + 1) : ℕ) : ℝ)) =
      (deltaExtractionScale d : ℝ) := by
    simp only [one_div, div_inv_eq_mul, deltaExtractionScale, Nat.cast_mul, Nat.cast_ofNat]
  rw [heq, Nat.ceil_natCast]

lemma deltaExtractionScale_pos (d : ℕ) : 0 < deltaExtractionScale d := by
  dsimp only [deltaExtractionScale]
  positivity

lemma deltaExtractionScale_mono : Monotone deltaExtractionScale := by
  intro d e hde
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_right (by omega) hde))
    (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hde 1))

lemma deltaExtractionFactor_mono : Monotone deltaExtractionFactor := by
  intro d e hde
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 9 hde) (deltaExtractionScale_mono hde)

lemma deltaExtractionFactor_pos {d : ℕ} (hd : 0 < d) : 0 < deltaExtractionFactor d := by
  exact Nat.mul_pos (Nat.mul_pos (by omega) hd) (deltaExtractionScale_pos d)

lemma delta_geometric_threshold_of_card {d d₀ m : ℕ} (hd : d ≤ d₀)
    (hm : deltaExtractionScale d₀ ≤ m) :
    16 * ((4 ^ d : ℕ) : ℝ) ≤ (1 / ((4 ^ (d + 1) : ℕ) : ℝ)) * m := by
  have hpos : (0 : ℝ) < ((4 ^ (d + 1) : ℕ) : ℝ) := by positivity
  have hscale : deltaExtractionScale d ≤ m := (deltaExtractionScale_mono hd).trans hm
  have hbound : (16 * 4 ^ d * 4 ^ (d + 1) : ℕ) ≤ m := by
    dsimp only [deltaExtractionScale] at hscale
    nlinarith
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hpos]
  exact_mod_cast hbound

theorem delta_uniform_full_width_bounds (Q : Erdos587.GeneralizedAP) {d d₀ m : ℕ}
    (hd : d ≤ d₀)
    (hside : ∀ i, m ≤ deltaExtractionFactor d * Q.length i)
    (hcard : m ^ (Q.rank + 1) ≤ 2 * deltaExtractionFactor d ^ Q.rank * Q.carrier.card)
    (hheight : (Q.upperEndpoint : ℝ) ≤
      (((3 : ℝ) / 2) * deltaExtractionScale d + 1) * Q.coefficientSpan) :
    (∀ i, m ≤ deltaExtractionFactor d₀ * Q.length i) ∧
      m ^ (Q.rank + 1) ≤ 2 * deltaExtractionFactor d₀ ^ Q.rank * Q.carrier.card ∧
      (Q.upperEndpoint : ℝ) ≤ ((2 * deltaExtractionScale d₀ + 1 : ℕ) : ℝ) * Q.coefficientSpan := by
  have hF := deltaExtractionFactor_mono hd
  refine ⟨fun i => (hside i).trans (Nat.mul_le_mul_right _ hF),
    hcard.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hF _))), ?_⟩
  apply hheight.trans
  apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast Q.coefficientSpan_nonneg)
  have hK : (deltaExtractionScale d : ℝ) ≤ deltaExtractionScale d₀ := by
    exact_mod_cast deltaExtractionScale_mono hd
  have hKpos : (0 : ℝ) ≤ deltaExtractionScale d₀ := by positivity
  push_cast
  linarith

end Erdos587.CFP
