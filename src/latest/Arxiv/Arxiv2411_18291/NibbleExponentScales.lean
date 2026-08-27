import Arxiv.Arxiv2411_18291.CriticalExponentLowerBound
import Mathlib.Tactic.Positivity

/-! # Count, edge, and face scales in the critical-window exponent -/

namespace Arxiv2411_18291

theorem count_criticalExponent_ge {a g D c B T : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hg : 0 < g) (hD : 0 < D) (hc : 1 ≤ c)
    (hB : 0 < B) (hBc : B ≤ c * D) (hhalf : B ≤ a ^ 3 * D * g / 2)
    (hT0 : 0 ≤ T) (hT : T ≤ g) :
    a ^ 6 * g / (16 * c ^ 2) ≤ criticalExponent (a ^ 3 * D * g) B (T * B ^ 2) := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hV : T * B ^ 2 ≤ g * (c * D) ^ 2 :=
    (mul_le_mul_of_nonneg_right hT (sq_nonneg B)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB.le hBc 2) hg.le)
  have hW : a ^ 3 * D * g * B ≤ g * (c * D) ^ 2 := by
    calc
      _ ≤ a ^ 3 * D * g * (c * D) := mul_le_mul_of_nonneg_left hBc (by positivity)
      _ = a ^ 3 * (D * g * (c * D)) := by ring
      _ ≤ c * (D * g * (c * D)) :=
        mul_le_mul_of_nonneg_right ((pow_le_one₀ ha ha1).trans hc) (by positivity)
      _ = _ := by ring
  have hbudget : T * B ^ 2 + (a ^ 3 * D * g) * B ≤ 2 * g * (c * D) ^ 2 := by
    nlinarith only [hV, hW]
  calc
    _ = (a ^ 3 * D * g) ^ 2 / (8 * (2 * g * (c * D) ^ 2)) := by
      field_simp [hg.ne', hD.ne', hc0.ne']
      ring
    _ ≤ _ := criticalExponent_lower_bound hB (mul_nonneg hT0 (sq_nonneg B)) hhalf hbudget

theorem edge_criticalExponent_ge {a g D k B T : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hg : 0 < g) (hD : 0 < D) (hk : 1 ≤ k)
    (hB : 0 < B) (hhalf : B ≤ a ^ 2 * D / 2) (hT0 : 0 ≤ T) (hT : T ≤ g) :
    a ^ 4 * D / (88 * k ^ 2 * B) ≤
      criticalExponent (a ^ 2 * D) B (T * (B * (10 * k ^ 2 * D / g))) := by
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hk2 : 1 ≤ k ^ 2 := by nlinarith only [hk]
  have hV : T * (B * (10 * k ^ 2 * D / g)) ≤ 10 * k ^ 2 * D * B := by
    calc
      _ ≤ g * (B * (10 * k ^ 2 * D / g)) := mul_le_mul_of_nonneg_right hT (by positivity)
      _ = _ := by field_simp
  have hW : (a ^ 2 * D) * B ≤ k ^ 2 * D * B := by
    have h := mul_le_mul_of_nonneg_right ((pow_le_one₀ ha ha1 : a ^ 2 ≤ 1).trans hk2)
      (mul_nonneg hD.le hB.le)
    nlinarith only [h]
  have hbudget : T * (B * (10 * k ^ 2 * D / g)) + (a ^ 2 * D) * B ≤ 11 * k ^ 2 * D * B := by
    nlinarith only [hV, hW]
  calc
    _ = (a ^ 2 * D) ^ 2 / (8 * (11 * k ^ 2 * D * B)) := by
      field_simp [hk0.ne', hD.ne', hB.ne']
      ring
    _ ≤ _ := criticalExponent_lower_bound hB (by positivity) hhalf hbudget

theorem face_criticalExponent_ge {a g n B cv cb T : ℝ}
    (ha1 : a ≤ 1) (hg : 0 < g) (hn : 0 < n) (hcv : 0 ≤ cv)
    (hB : 0 < B) (hBc : B ≤ cb) (hhalf : B ≤ a * n / 2)
    (hT0 : 0 ≤ T) (hT : T ≤ g) :
    a ^ 2 * n / (8 * (cv + cb)) ≤ criticalExponent (a * n) B (T * (cv * n / g)) := by
  have hcb : 0 < cb := hB.trans_le hBc
  have hc : 0 < cv + cb := add_pos_of_nonneg_of_pos hcv hcb
  have hV : T * (cv * n / g) ≤ cv * n := by
    calc
      _ ≤ g * (cv * n / g) := mul_le_mul_of_nonneg_right hT (by positivity)
      _ = _ := by field_simp
  have hW : (a * n) * B ≤ cb * n := by
    calc
      _ = a * (n * B) := by ring
      _ ≤ 1 * (n * B) := mul_le_mul_of_nonneg_right ha1 (by positivity)
      _ ≤ n * cb := by simpa only [one_mul] using mul_le_mul_of_nonneg_left hBc hn.le
      _ = _ := by ring
  have hbudget : T * (cv * n / g) + (a * n) * B ≤ (cv + cb) * n := by
    nlinarith only [hV, hW]
  calc
    _ = (a * n) ^ 2 / (8 * ((cv + cb) * n)) := by
      field_simp [hc.ne', hn.ne']
    _ ≤ _ := criticalExponent_lower_bound hB (by positivity) hhalf hbudget

end Arxiv2411_18291
