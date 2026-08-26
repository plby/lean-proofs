import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Uniform rate bounds from an exponential collision estimate -/

namespace Erdos1148.DukeArithmetic

open Filter
open scoped Topology

theorem collision_entropy_linear_lower {m m₀ C κ L σ t : ℝ}
    (hm₀ : 0 < m₀) (hm : m₀ ≤ m) (hmone : m ≤ 1) (hC : 0 < C)
    (hκ : 0 ≤ κ) (hL : 0 ≤ L) (ht : 0 ≤ t) (hq : 0 ≤ 1 - 2 * σ - κ * L) :
    m₀ * (1 - 2 * σ - κ * L) * t - (κ * L + |Real.log C| - Real.log m₀) ≤
      -m * Real.log ((Real.exp (κ * (t + 1) * L) *
        (C * Real.exp ((-1 + 2 * σ) * t))) / m) := by
  have hmpos : 0 < m := hm₀.trans_le hm
  have hm₀one : m₀ ≤ 1 := hm.trans hmone
  have hlogm : Real.log m₀ ≤ Real.log m := Real.log_le_log hm₀ hm
  have hlogm₀ : Real.log m₀ ≤ 0 := Real.log_nonpos hm₀.le hm₀one
  have hmlog : Real.log m₀ ≤ m * Real.log m := by
    calc
      Real.log m₀ ≤ m * Real.log m₀ := by nlinarith [mul_nonneg (sub_nonneg.mpr hmone) (neg_nonneg.mpr hlogm₀)]
      _ ≤ m * Real.log m := mul_le_mul_of_nonneg_left hlogm hmpos.le
  have hmlogC : m * Real.log C ≤ |Real.log C| := by
    calc
      _ ≤ m * |Real.log C| := mul_le_mul_of_nonneg_left (le_abs_self _) hmpos.le
      _ ≤ 1 * |Real.log C| := mul_le_mul_of_nonneg_right hmone (abs_nonneg _)
      _ = _ := one_mul _
  have hmain : m₀ * (1 - 2 * σ - κ * L) * t ≤ m * (1 - 2 * σ - κ * L) * t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hq) ht
  have hconstant : m * (κ * L) ≤ κ * L := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hmone (mul_nonneg hκ hL)
  rw [Real.log_div (mul_pos (Real.exp_pos _) (mul_pos hC (Real.exp_pos _))).ne' hmpos.ne',
    Real.log_mul (Real.exp_pos _).ne' (mul_pos hC (Real.exp_pos _)).ne',
    Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  nlinarith

theorem eventual_entropy_rate_lower_of_linear_bound {ι : Type*} {l : Filter ι}
    {N : ι → ℕ} (hN : Tendsto N l atTop) {u : ι → ℝ} {a b c : ℝ}
    (hlower : ∀ᶠ i in l, a * (N i : ℝ) - b ≤ u i) (hc : c < a) :
    ∀ᶠ i in l, c ≤ u i / ((N i : ℝ) + 1) := by
  have hNR : Tendsto (fun i => (N i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hN
  have hden : Tendsto (fun i => (N i : ℝ) + 1) l atTop :=
    tendsto_atTop_mono (fun i => by linarith) hNR
  have hlim : Tendsto (fun i => a - (a + b) / ((N i : ℝ) + 1)) l (𝓝 a) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hden)
  filter_upwards [hlower, hlim.eventually (lt_mem_nhds hc)] with i hi hci
  have hn : (0 : ℝ) < (N i : ℝ) + 1 := by positivity
  have heq : a - (a + b) / ((N i : ℝ) + 1) =
      (a * (N i : ℝ) - b) / ((N i : ℝ) + 1) := by field_simp; ring
  rw [heq] at hci
  exact hci.le.trans (div_le_div_of_nonneg_right hi hn.le)

end Erdos1148.DukeArithmetic
