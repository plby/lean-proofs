import ErdosProblems.Erdos4.TiltedCutoffParameters
import ErdosProblems.Erdos4.TiltedTargetParameters
import ErdosProblems.Erdos4.TiltedPartitionSize
import ErdosProblems.Erdos4.TiltedRoughCount

/-! The actual rough composite count determines a sufficiently small block size. -/

namespace Erdos4.Tilted

open Filter

noncomputable def compositeTargets (c : ℝ) (x : ℕ) : Finset ℕ :=
  roughComposites x (gapTarget c x) (smallCutoff x)

theorem smallCutoff_tendsto : Tendsto smallCutoff atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_smallCutoff_bounds,
    log_tendsto.eventually (eventually_ge_atTop (max 2 (n : ℝ)))] with x hw hL
  have hL1 : 1 ≤ Real.log (x : ℝ) := by linarith [(le_max_left (2 : ℝ) n).trans hL]
  have hLL : Real.log (x : ℝ) ≤ Real.log (x : ℝ) ^ (98 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (98 : ℕ))
  have hh := ((le_max_right (2 : ℝ) n).trans hL).trans (hLL.trans hw.2.2.1)
  exact_mod_cast hh

theorem eventually_composite_count_and_blockSize {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      ((compositeTargets c x).card : ℝ) ≤
        (2 * c + 1) * (x : ℝ) * outerScale x / Real.log (Real.log (x : ℝ)) ∧
      (blockSize x (compositeTargets c x) : ℝ) ≤
        (2 * c + 2) * outerScale x / Real.log (Real.log (x : ℝ)) := by
  filter_upwards [eventually_smallCutoff_bounds, eventually_gapTarget_bounds hc,
    eventually_outerScale_bounds, smallCutoff_tendsto.eventually eventually_roughIntegers_card_le,
    eventually_iterated_log_power_le 1 1 (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop 1] with x hw hY hb hrough hlogsmall hx
  let l := Real.log (Real.log (x : ℝ))
  let s := outerScale x
  let C := compositeTargets c x
  have hl : 0 < l := by have hh := hb.2.1; change 1 ≤ l at hh; linarith
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hlw : l ≤ Real.log (smallCutoff x : ℝ) := hw.2.2.2.2.2.1
  have hls : l ≤ s := by
    have hh : l ≤ Real.sqrt (Real.log (x : ℝ)) := by
      simpa only [one_mul, pow_one, Real.sqrt_eq_rpow] using hlogsmall
    exact hh.trans hb.2.2.2.2.1
  have hratio : 1 ≤ s / l := (le_div_iff₀ hl).mpr (by simpa only [one_mul] using hls)
  have hraw : (C.card : ℝ) ≤ 2 * (gapTarget c x : ℝ) / Real.log (smallCutoff x : ℝ) +
      (smallCutoff x : ℝ) ^ 4 := by
    exact (Nat.cast_le.mpr (Finset.card_le_card (roughComposites_subset_roughIntegers
      x (gapTarget c x) (smallCutoff x)))).trans (hrough (gapTarget c x))
  have hcount : (C.card : ℝ) ≤ (2 * c + 1) * (x : ℝ) * s / l := by
    calc
      _ ≤ 2 * (gapTarget c x : ℝ) / l + (x : ℝ) :=
        hraw.trans (add_le_add (div_le_div_of_nonneg_left (by positivity) hl hlw) hw.2.2.2.2.1)
      _ ≤ 2 * (c * (x : ℝ) * s) / l + (x : ℝ) :=
        add_le_add (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hY.2.2.2.2.2.2.1 (by norm_num)) hl.le) le_rfl
      _ ≤ 2 * (c * (x : ℝ) * s) / l + (x : ℝ) * (s / l) :=
        add_le_add le_rfl (by nlinarith [mul_le_mul_of_nonneg_left hratio hxpos.le])
      _ = _ := by ring
  refine ⟨hcount, ?_⟩
  calc
    _ ≤ (C.card : ℝ) / x + 1 := blockSize_cast_le x C
    _ ≤ ((2 * c + 1) * (x : ℝ) * s / l) / x + 1 :=
      add_le_add (div_le_div_of_nonneg_right hcount hxpos.le) le_rfl
    _ = (2 * c + 1) * (s / l) + 1 := by field_simp
    _ ≤ (2 * c + 2) * s / l := by rw [mul_div_assoc]; nlinarith

end Erdos4.Tilted
