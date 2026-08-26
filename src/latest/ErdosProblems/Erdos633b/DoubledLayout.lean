import ErdosProblems.Erdos633b.DoubledPartition
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! Positive layout parameters and exact affine-form values at the seven vertices. -/

namespace Erdos633b.DoubledPartition

structure Layout where
  u : ℝ
  v : ℝ
  r : ℝ
  ε : ℝ
  μ : ℝ
  u_pos : 0 < u
  v_pos : 0 < v
  r_pos : 0 < r
  r_lt_one : r < 1
  uv_lt_one : u + v < 1
  delta_pos : 0 < delta u v r
  ε_pos : 0 < ε
  ε_lt_one : ε < 1
  μ_pos : 0 < μ
  μ_lt_one : μ < 1
  cut : (u + r - 1) * μ = ε * delta u v r

namespace Layout

noncomputable def height (L : Layout) : ℝ := (L.ε - 1) * delta L.u L.v L.r

theorem height_neg (L : Layout) : L.height < 0 :=
  mul_neg_of_neg_of_pos (sub_neg.mpr L.ε_lt_one) L.delta_pos

theorem v_lt_r (L : Layout) : L.v < L.r := by
  have h := L.delta_pos
  dsimp only [delta] at h
  nlinarith [mul_pos L.r_pos (show 0 < 1 - L.u - L.v by linarith [L.uv_lt_one])]

theorem u_lt_one (L : Layout) : L.u < 1 := by linarith [L.uv_lt_one, L.v_pos]

theorem dg_A (L : Layout) : dg L.u L.v L.r 0 0 = -delta L.u L.v L.r := by
  dsimp only [dg, delta]
  ring

theorem dg_B (L : Layout) : dg L.u L.v L.r 1 0 = L.r * (1 - L.u - L.v) := by
  dsimp only [dg]
  ring

theorem dg_C (L : Layout) : dg L.u L.v L.r 0 1 = -(1 - L.r) * (1 - L.u - L.v) := by
  dsimp only [dg]
  ring

theorem dg_D (L : Layout) : dg L.u L.v L.r L.u L.v = 0 := by simp [dg]

theorem dg_G (L : Layout) : dg L.u L.v L.r (1 - L.r) L.r = 0 := by
  dsimp only [dg]
  ring

theorem dg_E (L : Layout) : dg L.u L.v L.r (L.ε * L.u) (L.ε * L.v) = L.height := by
  dsimp only [dg, height, delta]
  ring

theorem dg_F (L : Layout) : dg L.u L.v L.r 0 L.μ = L.height := by
  have h := L.cut
  dsimp only [delta] at h
  dsimp only [dg, height, delta]
  linear_combination h

theorem fg_D (L : Layout) : fg L.r L.μ L.u L.v = (1 - L.ε) * delta L.u L.v L.r := by
  have h := L.cut
  dsimp only [delta] at h
  dsimp only [fg, delta]
  linear_combination -h

theorem fg_E (L : Layout) : fg L.r L.μ (L.ε * L.u) (L.ε * L.v) =
    L.μ * L.u * (1 - L.ε) := by
  have h := L.cut
  dsimp only [delta] at h
  dsimp only [fg]
  linear_combination -h

theorem ad_G (L : Layout) : ad L.u L.v (1 - L.r) L.r = -delta L.u L.v L.r := by
  dsimp only [ad, delta]
  ring

theorem bd_G (L : Layout) : bd L.u L.v (1 - L.r) L.r = L.r * (1 - L.u - L.v) := by
  dsimp only [bd]
  ring

theorem outer_D (L : Layout) : outer L.u L.v := ⟨L.u_pos.le, L.v_pos.le, L.uv_lt_one.le⟩

theorem outer_G (L : Layout) : outer (1 - L.r) L.r :=
  ⟨sub_nonneg.mpr L.r_lt_one.le, L.r_pos.le, by linarith⟩

theorem outer_E (L : Layout) : outer (L.ε * L.u) (L.ε * L.v) := by
  refine ⟨mul_nonneg L.ε_pos.le L.u_pos.le, mul_nonneg L.ε_pos.le L.v_pos.le, ?_⟩
  nlinarith [mul_nonneg L.ε_pos.le (show 0 ≤ 1 - L.u - L.v by linarith [L.uv_lt_one]),
    L.ε_lt_one]

theorem outer_F (L : Layout) : outer 0 L.μ := ⟨le_rfl, L.μ_pos.le, by linarith [L.μ_lt_one]⟩

end Layout
end Erdos633b.DoubledPartition
