import ErdosProblems.Erdos4.FGKMTOuterParameters

/-! The concrete initial-sieve density has the required full-scale logarithmic order. -/

namespace Erdos4.FGKMT

open Filter

theorem eventually_growing_random_cutoff_logs :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ growingRandomStart x ∧ growingRandomStart x ≤ growingRandomEnd x ∧
      50 * Real.log (Real.log (x : ℝ)) ≤ Real.log (growingRandomStart x : ℝ) ∧
      Real.log (growingRandomStart x : ℝ) ≤ 100 * Real.log (Real.log (x : ℝ)) ∧
      growingOuterScale x / 200 ≤ Real.log (growingRandomEnd x : ℝ) ∧
      Real.log (growingRandomEnd x : ℝ) ≤ growingOuterScale x / 100 := by
  filter_upwards [eventually_growing_outer_log_budget] with x hx
  let L := Real.log (x : ℝ)
  let l := Real.log L
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hx.1
  have hl : 1 ≤ l := hx.2.1
  have hdom : 1000 * l ≤ Real.sqrt L := hx.2.2.1
  have hscale : Real.sqrt L ≤ growingOuterScale x / 100 := hx.2.2.2.1
  have hexp : Real.exp (100 * l) = L ^ (100 : ℕ) := by
    have hh := Real.exp_log (pow_pos hLpos 100)
    rw [Real.log_pow] at hh
    exact hh
  have hKeq : ⌊Real.exp (100 * l)⌋₊ = growingRandomStart x := by rw [hexp]; rfl
  have hK := floor_exp_log_bounds (by linarith : 2 ≤ 100 * l)
  rw [hKeq] at hK
  have hZend := floor_exp_log_bounds (by linarith : 2 ≤ growingOuterScale x / 100)
  change 2 ≤ growingRandomEnd x ∧ (growingOuterScale x / 100) / 2 ≤
    Real.log (growingRandomEnd x : ℝ) ∧
    Real.log (growingRandomEnd x : ℝ) ≤ growingOuterScale x / 100 at hZend
  have hlogs : Real.log (growingRandomStart x : ℝ) ≤ Real.log (growingRandomEnd x : ℝ) := by
    linarith [hK.2.2, hZend.2.1]
  have hKpos : (0 : ℝ) < growingRandomStart x := by
    exact_mod_cast (show 0 < growingRandomStart x by omega)
  have hZpos : (0 : ℝ) < growingRandomEnd x := by
    exact_mod_cast (show 0 < growingRandomEnd x by omega)
  have horder := Real.exp_le_exp.mpr hlogs
  rw [Real.exp_log hKpos, Real.exp_log hZpos] at horder
  refine ⟨hK.1, by exact_mod_cast horder, ?_, hK.2.2, ?_, hZend.2.2⟩
  · change 50 * l ≤ Real.log (growingRandomStart x : ℝ)
    linarith [hK.2.1]
  · linarith [hZend.2.1]

theorem exists_growing_random_density_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      c * Real.log (Real.log (x : ℝ)) / growingOuterScale x ≤
        UnitFourier.unitDensity (growingRandomValue x) ∧
      UnitFourier.unitDensity (growingRandomValue x) ≤
        C * Real.log (Real.log (x : ℝ)) / growingOuterScale x := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hdensity⟩ := EulerDensityBounds.exists_window_density_bounds
  refine ⟨5000 * c₀, 20000 * C₀, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_growing_random_cutoff_logs, eventually_growing_outer_log_budget]
    with x hx hlog
  let l := Real.log (Real.log (x : ℝ))
  let s := growingOuterScale x
  have hl : 0 < l := lt_of_lt_of_le (by norm_num) hlog.2.1
  have hs : 0 < s := by
    have hroot : 0 < Real.sqrt (Real.log (x : ℝ)) :=
      Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) hlog.1)
    have hh := hlog.2.2.2.1
    change Real.sqrt (Real.log (x : ℝ)) ≤ s / 100 at hh
    linarith
  have hKlog : 0 < Real.log (growingRandomStart x : ℝ) := Real.log_pos (by exact_mod_cast hx.1)
  have hZlog : 0 < Real.log (growingRandomEnd x : ℝ) :=
    Real.log_pos (by exact_mod_cast (hx.1.trans hx.2.1))
  have hd := hdensity (growingRandomStart x) (growingRandomEnd x) hx.1 hx.2.1
  change c₀ * Real.log (growingRandomStart x : ℝ) / Real.log (growingRandomEnd x : ℝ) ≤
      UnitFourier.unitDensity (growingRandomValue x) ∧
    UnitFourier.unitDensity (growingRandomValue x) ≤
      C₀ * Real.log (growingRandomStart x : ℝ) / Real.log (growingRandomEnd x : ℝ) at hd
  constructor
  · calc
      _ = c₀ * (50 * l) / (s / 100) := by dsimp only [l, s]; ring
      _ ≤ c₀ * Real.log (growingRandomStart x : ℝ) / (s / 100) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx.2.2.1 hc₀.le) (by positivity)
      _ ≤ c₀ * Real.log (growingRandomStart x : ℝ) / Real.log (growingRandomEnd x : ℝ) :=
        div_le_div_of_nonneg_left (mul_pos hc₀ hKlog).le hZlog hx.2.2.2.2.2
      _ ≤ _ := hd.1
  · calc
      _ ≤ C₀ * Real.log (growingRandomStart x : ℝ) / Real.log (growingRandomEnd x : ℝ) := hd.2
      _ ≤ C₀ * (100 * l) / Real.log (growingRandomEnd x : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx.2.2.2.1 hC₀.le) hZlog.le
      _ ≤ C₀ * (100 * l) / (s / 200) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hx.2.2.2.2.1
      _ = _ := by dsimp only [l, s]; ring

theorem eventually_growing_random_density_lower :
    ∀ᶠ x : ℕ in atTop, 1 / Real.log (x : ℝ) ^ (2 : ℕ) ≤
      UnitFourier.unitDensity (growingRandomValue x) := by
  obtain ⟨c, C, hc, _, hdensity⟩ := exists_growing_random_density_bounds
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hdensity, eventually_growing_outer_log_budget,
    hlog.eventually (eventually_ge_atTop (1 / c))] with x hd hb hlarge
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let s := growingOuterScale x
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) hb.1
  have hl : 1 ≤ l := hb.2.1
  have hs : 0 < s := by
    have hroot := Real.sqrt_pos.mpr hL
    have hh := hb.2.2.2.1
    change Real.sqrt L ≤ s / 100 at hh
    linarith
  have hCL : 1 ≤ c * L := by
    change 1 / c ≤ L at hlarge
    have hh := (div_le_iff₀ hc).mp hlarge
    nlinarith
  calc
    _ ≤ c / L := by
      apply (div_le_div_iff₀ (pow_pos hL 2) hL).mpr
      nlinarith
    _ ≤ c / s := div_le_div_of_nonneg_left hc.le hs hb.2.2.2.2
    _ ≤ c * l / s := div_le_div_of_nonneg_right
      (by nlinarith : c ≤ c * l) hs.le
    _ ≤ _ := hd.1

end Erdos4.FGKMT
