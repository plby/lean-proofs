import Arxiv.Arxiv2411_18291.RatioPerturbation

/-! # Numerical drift inequalities in the two clique-count critical intervals -/

namespace Arxiv2411_18291

theorem clique_count_upper_drift_nonpos {K H H₀ E v w L δ : ℝ}
    (hE : 0 < E) (hgap : E * L ≤ v - w) (hH : H₀ + v - w ≤ H)
    (hstep : -(K ^ 2 * H₀ / E) ≤ δ) :
    -(K ^ 2 * H / E) + K ^ 2 * L - δ ≤ 0 := by
  have hcount : H₀ + E * L ≤ H := by linarith only [hgap, hH]
  have hratio : K ^ 2 * H₀ / E + K ^ 2 * L ≤ K ^ 2 * H / E := by
    calc
      _ = (K ^ 2 / E) * (H₀ + E * L) := by field_simp
      _ ≤ (K ^ 2 / E) * H :=
        mul_le_mul_of_nonneg_left hcount (div_nonneg (sq_nonneg K) hE.le)
      _ = _ := by ring
  linarith only [hratio, hstep]

theorem clique_count_lower_drift_nonneg {K H H₀ E v w u δ : ℝ}
    (hE : 0 < E) (hH₀ : 0 < H₀) (hhalf : H₀ / 2 ≤ H) (hH : H ≤ H₀ - v + w)
    (hvariance : 2 * E ^ 2 * u ^ 2 ≤ K ^ 2 * (v - w) * H₀)
    (hstep : δ ≤ -(K ^ 2 * H₀ / E)) :
    0 ≤ -(K ^ 2 * H / E) - E * u ^ 2 / H - δ := by
  have hpos : 0 < H := by linarith only [hH₀, hhalf]
  have hvar : E * u ^ 2 / H ≤ 2 * E * u ^ 2 / H₀ := by
    apply (div_le_div_iff₀ hpos hH₀).mpr
    have h := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hE.le (sq_nonneg u))
    nlinarith only [h]
  have hgap : 2 * E * u ^ 2 / H₀ ≤ K ^ 2 * (v - w) / E := by
    apply (div_le_div_iff₀ hH₀ hE).mpr
    nlinarith only [hvariance]
  have hcount : K ^ 2 * H / E ≤ K ^ 2 * H₀ / E - K ^ 2 * (v - w) / E := by
    calc
      _ ≤ K ^ 2 * (H₀ - v + w) / E :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH (sq_nonneg K)) hE.le
      _ = _ := by ring
  have hvar' := hvar.trans hgap
  linarith only [hcount, hvar', hstep]

end Arxiv2411_18291
