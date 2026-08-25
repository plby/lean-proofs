import ErdosProblems.Erdos964.PrimeCountingReal

/-!
# Uniform prime counting in a fixed multiplicative window

The reference logarithm is the lower scale, which allows subtraction of
the two affine endpoints without a new logarithm at each endpoint.
-/

namespace Erdos964

open Filter
open scoped Topology

theorem abs_div_log_sub_div_log_le (B Y u : ℝ) (hB : 1 ≤ B) (hY : 1 < Y)
    (hYu : Y ≤ u) (huB : u ≤ B * Y) :
    |u / Real.log u - u / Real.log Y| ≤
      (u / Real.log Y) * (Real.log B / Real.log Y) := by
  have hY0 : 0 < Y := by linarith
  have hu0 : 0 < u := hY0.trans_le hYu
  have hB0 : 0 < B := by linarith
  have hLY : 0 < Real.log Y := Real.log_pos hY
  have hLYu : Real.log Y ≤ Real.log u := Real.log_le_log hY0 hYu
  have hLu : 0 < Real.log u := hLY.trans_le hLYu
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hgap : Real.log u - Real.log Y ≤ Real.log B := by
    have h := Real.log_le_log hu0 huB
    rw [Real.log_mul hB0.ne' hY0.ne'] at h
    linarith
  have hquot : u / Real.log u ≤ u / Real.log Y :=
    div_le_div_of_nonneg_left hu0.le hLY hLYu
  rw [abs_of_nonpos (sub_nonpos.mpr hquot)]
  calc
    _ = (u / Real.log Y) * ((Real.log u - Real.log Y) / Real.log u) := by
      field_simp
      ring
    _ ≤ (u / Real.log Y) * (Real.log B / Real.log u) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hgap hLu.le) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hlogB hLY hLYu) (by positivity)

theorem exists_primeCounting_multiplicative_window_error (B : ℝ) (hB : 1 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Y₀ : ℝ, 2 ≤ Y₀ ∧ ∀ Y u : ℝ, Y₀ ≤ Y → Y ≤ u → u ≤ B * Y →
      |(Nat.primeCounting ⌊u⌋₊ : ℝ) - u / Real.log Y| ≤ ε * (u / Real.log Y) := by
  obtain ⟨X, hX, hPNT⟩ := exists_primeCounting_real_relative_error (ε / 2) (by positivity)
  have htail : Tendsto (fun Y : ℝ => Real.log B / Real.log Y) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop _
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp ((tendsto_order.mp htail).2 (ε / 2) (by positivity))
  refine ⟨max X Y₁, hX.trans (le_max_left _ _), ?_⟩
  intro Y u hY hYu huB
  have hXY : X ≤ Y := (le_max_left X Y₁).trans hY
  have hYtwo : 2 ≤ Y := hX.trans hXY
  have hLY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hu0 : 0 < u := lt_of_lt_of_le (by linarith : 0 < Y) hYu
  have hlog := Real.log_le_log (by linarith : 0 < Y) hYu
  have hquot : u / Real.log u ≤ u / Real.log Y :=
    div_le_div_of_nonneg_left hu0.le hLY hlog
  have hsmall := hY₁ Y ((le_max_right X Y₁).trans hY)
  calc
    _ ≤ |(Nat.primeCounting ⌊u⌋₊ : ℝ) - u / Real.log u| +
        |u / Real.log u - u / Real.log Y| := abs_sub_le _ _ _
    _ ≤ (ε / 2) * (u / Real.log u) +
        (u / Real.log Y) * (Real.log B / Real.log Y) :=
      add_le_add (hPNT u (hXY.trans hYu))
        (abs_div_log_sub_div_log_le B Y u hB (by linarith) hYu huB)
    _ ≤ (ε / 2) * (u / Real.log Y) + (u / Real.log Y) * (ε / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hquot (by positivity))
        (mul_le_mul_of_nonneg_left hsmall.le (by positivity))
    _ = _ := by ring

end Erdos964
