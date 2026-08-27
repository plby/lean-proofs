import ErdosProblems.Erdos4.FGKMTOuterParameters

/-! Uniform comparison of the FGKMT scale with a logarithmically chosen natural endpoint. -/

namespace Erdos4.FGKMT

open Filter

noncomputable def realOuterScale (t : ℝ) : ℝ :=
  t * Real.log t * Real.log (Real.log (Real.log t)) / Real.log (Real.log t)

noncomputable def gapScale (X : ℝ) : ℝ := realOuterScale (Real.log X)

noncomputable def endpointParameter (D : ℕ) (X : ℝ) : ℕ :=
  ⌊Real.log X / (2 * (D : ℝ))⌋₊

theorem realOuterScale_compare {t u A : ℝ} (hA : 1 ≤ A) (ht : 1 ≤ t)
    (hlower : t / A ≤ u) (hupper : u ≤ t)
    (hLA : 2 * Real.log A ≤ Real.log t)
    (hL : 4 ≤ Real.log t) (hl : 4 ≤ Real.log (Real.log t))
    (hll : 4 ≤ Real.log (Real.log (Real.log t))) :
    realOuterScale t / (4 * A) ≤ realOuterScale u := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hupos : 0 < u := (div_pos htpos hApos).trans_le hlower
  have hLtpos : 0 < Real.log t := by linarith
  have hltpos : 0 < Real.log (Real.log t) := by linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hLu : Real.log t / 2 ≤ Real.log u := by
    have hh := Real.log_le_log (div_pos htpos hApos) hlower
    rw [Real.log_div htpos.ne' hApos.ne'] at hh
    linarith
  have hLupos : 0 < Real.log u := by linarith
  have hlu : Real.log (Real.log t) / 2 ≤ Real.log (Real.log u) := by
    have hh := Real.log_le_log (div_pos hLtpos (by norm_num)) hLu
    rw [Real.log_div hLtpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    linarith
  have hlupos : 0 < Real.log (Real.log u) := by linarith
  have hllu : Real.log (Real.log (Real.log t)) / 2 ≤
      Real.log (Real.log (Real.log u)) := by
    have hh := Real.log_le_log (div_pos hltpos (by norm_num)) hlu
    rw [Real.log_div hltpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    linarith
  have hlupper : Real.log (Real.log u) ≤ Real.log (Real.log t) :=
    Real.log_le_log hLupos (Real.log_le_log hupos hupper)
  have hllupos : 0 ≤ Real.log (Real.log (Real.log u)) := by linarith
  have hnum : (t / A) * (Real.log t / 2) *
      (Real.log (Real.log (Real.log t)) / 2) ≤
        u * Real.log u * Real.log (Real.log (Real.log u)) := by
    gcongr
  calc
    _ = ((t / A) * (Real.log t / 2) *
        (Real.log (Real.log (Real.log t)) / 2)) / Real.log (Real.log t) := by
      unfold realOuterScale
      ring
    _ ≤ (u * Real.log u * Real.log (Real.log (Real.log u))) / Real.log (Real.log t) :=
      div_le_div_of_nonneg_right hnum hltpos.le
    _ ≤ realOuterScale u :=
      div_le_div_of_nonneg_left (by positivity) hlupos hlupper

theorem eventually_floor_scale_compare {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ t : ℝ in atTop,
      realOuterScale t / (16 * (D : ℝ)) ≤
        (⌊t / (2 * (D : ℝ))⌋₊ : ℝ) * growingOuterScale ⌊t / (2 * (D : ℝ))⌋₊ := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by norm_num) hDR
  have hlog := Real.tendsto_log_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hlogloglog := Real.tendsto_log_atTop.comp hloglog
  filter_upwards [eventually_ge_atTop (4 * (D : ℝ)),
    hlog.eventually (eventually_ge_atTop (max 4 (2 * Real.log (4 * (D : ℝ))))),
    hloglog.eventually (eventually_ge_atTop 4),
    hlogloglog.eventually (eventually_ge_atTop 4)] with t ht hL hl hll
  change max 4 (2 * Real.log (4 * (D : ℝ))) ≤ Real.log t at hL
  change 4 ≤ Real.log (Real.log t) at hl
  change 4 ≤ Real.log (Real.log (Real.log t)) at hll
  let s := t / (2 * (D : ℝ))
  let n := ⌊s⌋₊
  have ht1 : 1 ≤ t := by linarith
  have hs2 : 2 ≤ s := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hn1 : 1 ≤ n := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using (show (1 : ℝ) ≤ s by linarith)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hfloor := Nat.lt_floor_add_one s
  have hlow : t / (4 * (D : ℝ)) ≤ (n : ℝ) := by
    have hh : s / 2 ≤ (n : ℝ) := by dsimp only [n] at hnR ⊢; linarith
    exact (show t / (4 * (D : ℝ)) = s / 2 by dsimp only [s]; ring).trans_le hh
  have hupp : (n : ℝ) ≤ t := by
    apply (Nat.floor_le (show 0 ≤ s by linarith)).trans
    exact div_le_self (by linarith : 0 ≤ t) (by linarith : 1 ≤ 2 * (D : ℝ))
  have hh := realOuterScale_compare (by linarith : 1 ≤ 4 * (D : ℝ)) ht1 hlow hupp
    ((le_max_right _ _).trans hL) ((le_max_left _ _).trans hL) hl hll
  change realOuterScale t / (16 * (D : ℝ)) ≤ (n : ℝ) * growingOuterScale n
  calc
    _ = realOuterScale t / (4 * (4 * (D : ℝ))) := by ring
    _ ≤ realOuterScale (n : ℝ) := hh
    _ = _ := by unfold realOuterScale growingOuterScale; ring

theorem endpointParameter_tendsto {D : ℕ} (hD : 1 ≤ D) :
    Tendsto (endpointParameter D) atTop atTop := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  apply tendsto_atTop.2
  intro N
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop ((2 * (D : ℝ)) * N))] with X hX
  apply Nat.le_floor
  apply (le_div_iff₀ (by positivity : 0 < 2 * (D : ℝ))).mpr
  linarith

theorem eventually_endpoint_scale_compare {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ X : ℝ in atTop,
      gapScale X / (16 * (D : ℝ)) ≤
        (endpointParameter D X : ℝ) * growingOuterScale (endpointParameter D X) :=
  Real.tendsto_log_atTop.eventually (eventually_floor_scale_compare hD)

end Erdos4.FGKMT
