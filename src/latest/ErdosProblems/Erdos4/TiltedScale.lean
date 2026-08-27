import ErdosProblems.Erdos4.TiltedParameters
import ErdosProblems.Erdos4.FGKMTAllEndpoints

/-! Uniform scale comparisons for every real prime frontier and every real gap endpoint. -/

namespace Erdos4.Tilted

open Filter FGKMT

noncomputable def coverScale (t : ℝ) : ℝ :=
  t * Real.log t / Real.log (Real.log (Real.log t))

noncomputable def primeGapScale (T : ℝ) : ℝ := coverScale (Real.log T)

theorem coverScale_nat (x : ℕ) : coverScale (x : ℝ) = 4 * (x : ℝ) * outerScale x := by
  unfold coverScale outerScale tiltScale
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem coverScale_compare {t u A : ℝ} (hA : 1 ≤ A) (ht : 1 ≤ t)
    (hlower : t / A ≤ u) (hupper : u ≤ t)
    (hLA : 2 * Real.log A ≤ Real.log t)
    (hL : 4 ≤ Real.log t) (hl : 4 ≤ Real.log (Real.log t))
    (hll : 4 ≤ Real.log (Real.log (Real.log t))) :
    coverScale t / (2 * A) ≤ coverScale u := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
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
  have hllu : Real.log (Real.log (Real.log t)) / 2 ≤ Real.log (Real.log (Real.log u)) := by
    have hh := Real.log_le_log (div_pos hltpos (by norm_num)) hlu
    rw [Real.log_div hltpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hh
    linarith
  have hllupos : 0 < Real.log (Real.log (Real.log u)) := by linarith
  have hllupper : Real.log (Real.log (Real.log u)) ≤ Real.log (Real.log (Real.log t)) :=
    Real.log_le_log hlupos (Real.log_le_log hLupos (Real.log_le_log hupos hupper))
  have hnum : (t / A) * (Real.log t / 2) ≤ u * Real.log u := by gcongr
  calc
    _ = ((t / A) * (Real.log t / 2)) / Real.log (Real.log (Real.log t)) := by unfold coverScale; ring
    _ ≤ (u * Real.log u) / Real.log (Real.log (Real.log t)) :=
      div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ coverScale u := div_le_div_of_nonneg_left (mul_pos hupos hLupos).le hllupos hllupper

noncomputable def scaledParameter (D : ℕ) (t : ℝ) : ℕ := ⌊t / (2 * (D : ℝ))⌋₊

theorem scaledParameter_tendsto {D : ℕ} (hD : 1 ≤ D) : Tendsto (scaledParameter D) atTop atTop := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop ((2 * (D : ℝ)) * N)] with t ht
  apply Nat.le_floor
  apply (le_div_iff₀ (by positivity : 0 < 2 * (D : ℝ))).mpr
  linarith

theorem eventually_scaledParameter_compare {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ t : ℝ in atTop, coverScale t / (32 * (D : ℝ)) ≤
      (scaledParameter D t : ℝ) * outerScale (scaledParameter D t) := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDR
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
  let n := scaledParameter D t
  have ht1 : 1 ≤ t := by linarith
  have hs2 : 2 ≤ s := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hn1 : 1 ≤ n := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using (show (1 : ℝ) ≤ s by linarith)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hfloor := Nat.lt_floor_add_one s
  have hlow : t / (4 * (D : ℝ)) ≤ (n : ℝ) := by
    have hh : s / 2 ≤ (n : ℝ) := by change s < (n : ℝ) + 1 at hfloor; linarith
    exact (show t / (4 * (D : ℝ)) = s / 2 by dsimp only [s]; ring).trans_le hh
  have hupp : (n : ℝ) ≤ t := by
    apply (Nat.floor_le (show 0 ≤ s by linarith)).trans
    exact div_le_self (by linarith : 0 ≤ t) (by linarith : 1 ≤ 2 * (D : ℝ))
  have hh := coverScale_compare (by linarith : 1 ≤ 4 * (D : ℝ)) ht1 hlow hupp
    ((le_max_right _ _).trans hL) ((le_max_left _ _).trans hL) hl hll
  rw [coverScale_nat n] at hh
  change coverScale t / (32 * (D : ℝ)) ≤ (n : ℝ) * outerScale n
  calc
    _ = (coverScale t / (2 * (4 * (D : ℝ)))) / 4 := by ring
    _ ≤ (4 * (n : ℝ) * outerScale n) / 4 := div_le_div_of_nonneg_right hh (by norm_num)
    _ = _ := by ring

theorem scaledParameter_frontier_le {D : ℕ} (hD : 1 ≤ D) {t : ℝ} (ht : 0 ≤ t) :
    D * scaledParameter D t ≤ ⌊t⌋₊ := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  apply Nat.le_floor
  rw [Nat.cast_mul]
  have hf : (scaledParameter D t : ℝ) ≤ t / (2 * (D : ℝ)) := Nat.floor_le (by positivity)
  calc
    _ ≤ (D : ℝ) * (t / (2 * (D : ℝ))) := mul_le_mul_of_nonneg_left hf hDpos.le
    _ = t / 2 := by field_simp
    _ ≤ _ := by linarith

theorem eventually_endpoint_tilted_compare {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ T : ℝ in atTop, primeGapScale T / (32 * (D : ℝ)) ≤
      (endpointParameter D T : ℝ) * outerScale (endpointParameter D T) :=
  Real.tendsto_log_atTop.eventually (eventually_scaledParameter_compare hD)

end Erdos4.Tilted
