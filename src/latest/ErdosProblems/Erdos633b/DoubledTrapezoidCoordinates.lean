import ErdosProblems.Erdos633b.DoubledLayout

/-! Exact inverse-coordinate inequalities for the placed trapezoid. -/

namespace Erdos633b.DoubledPartition.Layout

theorem ad_trapezoid_coords (L : Layout) (p q : ℝ) :
    ad L.u L.v (L.ε * L.u * p + (1 - L.r) * q)
      (L.μ + (L.ε * L.v - L.μ) * p + (L.r - L.μ) * q) =
      L.u * L.μ * (p - 1) + (L.u * L.μ - delta L.u L.v L.r) * q := by
  dsimp only [ad, delta]
  ring

theorem dg_trapezoid_coords (L : Layout) (p q : ℝ) :
    dg L.u L.v L.r (L.ε * L.u * p + (1 - L.r) * q)
      (L.μ + (L.ε * L.v - L.μ) * p + (L.r - L.μ) * q) = L.height * (1 - q) := by
  have h := L.cut
  dsimp only [delta] at h
  dsimp only [dg, height, delta]
  linear_combination (1 - p - q) * h

theorem fg_trapezoid_coords (L : Layout) (p q : ℝ) :
    fg L.r L.μ (L.ε * L.u * p + (1 - L.r) * q)
      (L.μ + (L.ε * L.v - L.μ) * p + (L.r - L.μ) * q) =
      (L.μ * L.u * (1 - L.ε)) * p := by
  have h := L.cut
  dsimp only [delta] at h
  dsimp only [fg]
  linear_combination -p * h

theorem trapezoid_coords_nonneg (L : Layout) (x y p q : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hscale : delta L.u L.v L.r * (x + y) = L.u * L.μ * x)
    (hp : constraints L.u L.v L.r L.μ L.height
      (L.ε * L.u * p + (1 - L.r) * q)
      (L.μ + (L.ε * L.v - L.μ) * p + (L.r - L.μ) * q) .trapezoid) :
    0 ≤ p ∧ 0 ≤ q ∧ q ≤ 1 ∧ (x + y) * p + y * q ≤ x + y := by
  obtain ⟨ha, hlo, hhi, hf⟩ := hp
  rw [L.ad_trapezoid_coords] at ha
  rw [L.dg_trapezoid_coords] at hlo hhi
  rw [L.fg_trapezoid_coords] at hf
  have hp' := nonneg_of_mul_nonneg_right hf
    (mul_pos (mul_pos L.μ_pos L.u_pos) (sub_pos.mpr L.ε_lt_one))
  have hq0 : 0 ≤ (-L.height) * q := by nlinarith only [hlo]
  have hq1 : 0 ≤ (-L.height) * (1 - q) := by nlinarith only [hhi]
  have hq' := nonneg_of_mul_nonneg_right hq0 (neg_pos.mpr L.height_neg)
  have hq1' := nonneg_of_mul_nonneg_right hq1 (neg_pos.mpr L.height_neg)
  have hid : (x + y) * (L.u * L.μ * (p - 1) + (L.u * L.μ - delta L.u L.v L.r) * q) =
      (L.u * L.μ) * ((x + y) * p + y * q - (x + y)) := by
    linear_combination -q * hscale
  have hs := mul_nonpos_of_nonneg_of_nonpos (add_pos hx hy).le ha
  rw [hid] at hs
  have hs' := nonpos_of_mul_nonpos_right hs (mul_pos L.u_pos L.μ_pos)
  exact ⟨hp', hq', by linarith only [hq1'], by linarith only [hs']⟩

end Erdos633b.DoubledPartition.Layout
