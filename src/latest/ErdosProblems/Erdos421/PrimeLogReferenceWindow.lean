import ErdosProblems.Erdos421.PrimeReferenceWindow

/-! # The positive prime-window main term at a fixed inverse-logarithmic scale -/

namespace Erdos421

open Complex Filter Topology
open scoped SchwartzMap

theorem logarithmic_reference_scale_admissible {B : ℝ} (hB : 0 < B) :
    ∀ᶠ X : ℕ in atTop, 0 < (Real.log X) ^ (-B) ∧
      2 / (Real.log X) ^ (B + 1) ≤ (Real.log X) ^ (-B) ∧
      Real.exp ((Real.log X) ^ (-B)) ≤ 4 / 3 := by
  have hloglim : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrho := (tendsto_rpow_neg_atTop hB).comp hloglim
  have hexp := (Real.continuous_exp.tendsto (0 : ℝ)).comp hrho
  simp only [Real.exp_zero] at hexp
  filter_upwards [hloglim.eventually (eventually_ge_atTop 2),
    hexp.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 4 / 3))] with X hlog hexp
  have hL : 0 < Real.log X := by linarith
  have hp : 0 < (Real.log X) ^ (-B) := Real.rpow_pos_of_pos hL _
  refine ⟨hp, ?_, hexp.le⟩
  have hratio : 2 / Real.log X ≤ 1 := (div_le_one hL).mpr hlog
  calc
    _ = (2 / Real.log X) * (Real.log X) ^ (-B) := by
      rw [Real.rpow_add hL, Real.rpow_one, Real.rpow_neg hL.le]
      ring
    _ ≤ _ := mul_le_of_le_one_left hp.le hratio

theorem prime_log_reference_window_lower_bound {B : ℝ} (hB : 0 < B) :
    ∀ᶠ X : ℕ in atTop, 0 < (Real.log X) ^ (-B) ∧
      ∀ (hρ : 0 < (Real.log X) ^ (-B)) (y : ℝ), (X : ℝ) ≤ Real.exp y →
      Real.exp y ≤ 3 * X / 2 → oneSidedWindowHeight / (16 * Real.log X) ≤
        (schwartzDirichletWindow (primeBlockSupport X X) (fun _ ↦ 1) 1
          (normalizedSchwartzScale ((Real.log X) ^ (-B)) hρ oneSidedSchwartzWindow) y).re := by
  obtain ⟨X₀, _, hreference⟩ := prime_reference_window_lower_bound (by linarith : 0 ≤ B + 1)
  filter_upwards [logarithmic_reference_scale_admissible hB,
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop X₀),
    eventually_ge_atTop (2 : ℕ)] with X hscale hX hX2
  refine ⟨hscale.1, ?_⟩
  intro hρ y hlo hhi
  have hx2 : (2 : ℝ) ≤ X := by exact_mod_cast hX2
  have hXp : (0 : ℝ) < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hL₂ : 0 < Real.log (2 * X) := Real.log_pos (by linarith)
  have hlog : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hXp.ne']
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx2
    linarith
  have hb := hreference X hX ((Real.log X) ^ (-B)) y hρ hscale.2.1 hscale.2.2 hlo hhi
  apply le_trans _ hb
  apply div_le_div_of_nonneg_left oneSidedWindowHeight_pos.le (by positivity)
  linarith

end Erdos421
