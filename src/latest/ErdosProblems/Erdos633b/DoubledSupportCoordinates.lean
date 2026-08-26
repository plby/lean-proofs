import ErdosProblems.Erdos633b.DoubledLayout

/-! Reverse barycentric certificates for all four triangular pieces. -/

namespace Erdos633b.DoubledPartition.Layout

theorem abd_coords_nonneg (L : Layout) (p q : ℝ)
    (hp : closed L.u L.v L.r L.μ L.height (p + L.u * q) (L.v * q) .abd) :
    0 ≤ p ∧ 0 ≤ q ∧ p + q ≤ 1 := by
  obtain ⟨⟨_, ht, _⟩, ha, hb⟩ := hp
  have hp' : 0 ≤ L.v * p := by dsimp only [ad] at ha; nlinarith only [ha]
  have hs' : 0 ≤ L.v * (1 - p - q) := by dsimp only [bd] at hb; nlinarith only [hb]
  have hs := nonneg_of_mul_nonneg_right hs' L.v_pos
  exact ⟨nonneg_of_mul_nonneg_right hp' L.v_pos,
    nonneg_of_mul_nonneg_right ht L.v_pos, by linarith only [hs]⟩

theorem bdg_coords_nonneg (L : Layout) (p q : ℝ)
    (hp : closed L.u L.v L.r L.μ L.height
      (1 - (1 - L.u) * p - L.r * q) (L.v * p + L.r * q) .bdg) :
    0 ≤ p ∧ 0 ≤ q ∧ p + q ≤ 1 := by
  obtain ⟨⟨_, _, hsum⟩, hb, hg⟩ := hp
  have hK : 0 < 1 - L.u - L.v := by linarith [L.uv_lt_one]
  have hA : 0 < L.r * (1 - L.u - L.v) := mul_pos L.r_pos hK
  have hp' : 0 ≤ (1 - L.u - L.v) * p := by nlinarith only [hsum]
  have hq' : 0 ≤ (L.r * (1 - L.u - L.v)) * q := by
    dsimp only [bd] at hb
    nlinarith only [hb]
  have hs' : 0 ≤ (L.r * (1 - L.u - L.v)) * (1 - p - q) := by
    dsimp only [dg] at hg
    nlinarith only [hg]
  have hs := nonneg_of_mul_nonneg_right hs' hA
  exact ⟨nonneg_of_mul_nonneg_right hp' hK,
    nonneg_of_mul_nonneg_right hq' hA, by linarith only [hs]⟩

theorem dg_aef_coords (L : Layout) (p q : ℝ) :
    dg L.u L.v L.r (L.ε * L.u * p) (L.ε * L.v * p + L.μ * q) =
      L.ε * delta L.u L.v L.r * (p + q) - delta L.u L.v L.r := by
  have h := L.cut
  dsimp only [delta] at h
  dsimp only [dg, delta]
  linear_combination q * h

theorem aef_coords_nonneg (L : Layout) (p q : ℝ)
    (hp : closed L.u L.v L.r L.μ L.height
      (L.ε * L.u * p) (L.ε * L.v * p + L.μ * q) .aef) :
    0 ≤ p ∧ 0 ≤ q ∧ p + q ≤ 1 := by
  obtain ⟨⟨hs, _, _⟩, ha, hg, _⟩ := hp
  have hp' := nonneg_of_mul_nonneg_right hs (mul_pos L.ε_pos L.u_pos)
  have hq' : 0 ≤ (L.u * L.μ) * q := by
    dsimp only [ad] at ha
    nlinarith only [ha]
  rw [L.dg_aef_coords] at hg
  have hsum' : 0 ≤ (L.ε * delta L.u L.v L.r) * (1 - p - q) := by
    dsimp only [height] at hg
    nlinarith only [hg]
  have hsum := nonneg_of_mul_nonneg_right hsum' (mul_pos L.ε_pos L.delta_pos)
  exact ⟨hp', nonneg_of_mul_nonneg_right hq' (mul_pos L.u_pos L.μ_pos),
    by linarith only [hsum]⟩

theorem cfg_coords_nonneg (L : Layout) (p q : ℝ)
    (hp : closed L.u L.v L.r L.μ L.height
      ((1 - L.r) * q) (1 - (1 - L.μ) * p - (1 - L.r) * q) .cfg) :
    0 ≤ p ∧ 0 ≤ q ∧ p + q ≤ 1 := by
  obtain ⟨⟨hs, _, hsum⟩, hf, _, _⟩ := hp
  have hr : 0 < 1 - L.r := sub_pos.mpr L.r_lt_one
  have hμ : 0 < 1 - L.μ := sub_pos.mpr L.μ_lt_one
  have hp' : 0 ≤ (1 - L.μ) * p := by nlinarith only [hsum]
  have hsum' : 0 ≤ ((1 - L.r) * (1 - L.μ)) * (1 - p - q) := by
    dsimp only [fg] at hf
    nlinarith only [hf]
  have hsum0 := nonneg_of_mul_nonneg_right hsum' (mul_pos hr hμ)
  exact ⟨nonneg_of_mul_nonneg_right hp' hμ, nonneg_of_mul_nonneg_right hs hr,
    by linarith only [hsum0]⟩

end Erdos633b.DoubledPartition.Layout
