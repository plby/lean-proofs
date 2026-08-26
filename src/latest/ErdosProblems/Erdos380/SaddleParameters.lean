import ErdosProblems.Erdos380.SaddleScale

/-! # Concrete parameters and decay of the normalized neighbor error -/

open Filter
open scoped Topology

namespace Erdos380

noncomputable def logarithmicCeiling (N : ℕ) : ℕ := ⌈Real.log (2 * N : ℕ)⌉₊
noncomputable def shortWidth (N : ℕ) : ℕ := logarithmicCeiling N ^ 20
noncomputable def mixingBase (N : ℕ) : ℕ := scaleBase N ^ 10
noncomputable def replacementScale (N : ℕ) : ℕ := scaleBase N ^ 910
noncomputable def cofactorScale (N : ℕ) : ℕ := scaleBase N ^ 920
noncomputable def squareScale (N : ℕ) : ℕ := scaleBase N ^ 3000
noncomputable def largePrimeScale (N : ℕ) : ℕ := scaleBase N ^ 6000
noncomputable def smallPrimeScale (N : ℕ) : ℕ := scaleBase N ^ 490
noncomputable def probabilityParameter (N : ℕ) : ℝ :=
  Real.log (N : ℝ) / (10000 * Real.log (scaleBase N : ℝ))

noncomputable def neighborErrorFactor (N : ℕ) : ℝ :=
  (1 + Real.log (shortWidth N : ℝ)) *
    (Real.log (N : ℝ) / Real.log (replacementScale N : ℝ)) / probabilityParameter N ^ 2

lemma logarithmicCeiling_bounds {N : ℕ} (hN : 1 ≤ N) (hL : 2 ≤ Real.log (N : ℝ)) :
    Real.log (N : ℝ) ≤ logarithmicCeiling N ∧
      (logarithmicCeiling N : ℝ) ≤ 2 * Real.log N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog2N : 0 ≤ Real.log (2 * N : ℕ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * N))
  have hlow : Real.log (N : ℝ) ≤ Real.log (2 * N : ℕ) :=
    Real.log_le_log hNpos (by exact_mod_cast (by omega : N ≤ 2 * N))
  have hceil := Nat.ceil_lt_add_one hlog2N
  change (logarithmicCeiling N : ℝ) < Real.log (2 * N : ℕ) + 1 at hceil
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hNpos.ne'] at hceil
  exact ⟨hlow.trans (Nat.le_ceil _), by linarith⟩

lemma shortWidth_log_bound {N : ℕ} (hN : 1 ≤ N) (hL : 2 ≤ Real.log (N : ℝ)) :
    0 < shortWidth N ∧ 1 + Real.log (shortWidth N : ℝ) ≤
      41 * (1 + Real.log (Real.log (N : ℝ))) := by
  obtain ⟨hlo, hhi⟩ := logarithmicCeiling_bounds hN hL
  have hB : (0 : ℝ) < logarithmicCeiling N := by linarith
  have hLpos : 0 < Real.log (N : ℝ) := by linarith
  have hll : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg (by linarith)
  have hlogB := Real.log_le_log hB hhi
  rw [Real.log_mul (by norm_num) hLpos.ne'] at hlogB
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  constructor
  · exact pow_pos (by exact_mod_cast hB) 20
  · rw [shortWidth, Nat.cast_pow, Real.log_pow]
    norm_num
    linarith

lemma neighborErrorFactor_eq {N : ℕ} (hL : 0 < Real.log (N : ℝ))
    (hS : 0 < Real.log (scaleBase N : ℝ)) :
    neighborErrorFactor N = (100000000 / 910 : ℝ) *
      (1 + Real.log (shortWidth N : ℝ)) * Real.log (scaleBase N : ℝ) / Real.log N := by
  unfold neighborErrorFactor replacementScale probabilityParameter
  rw [Nat.cast_pow, Real.log_pow]
  push_cast
  field_simp
  ring

theorem neighborErrorFactor_tendsto_zero : Tendsto neighborErrorFactor atTop (𝓝 0) := by
  have hmajor := scaleBase_error_coefficient_tendsto_zero.const_mul ((100000000 / 910 : ℝ) * 41)
  simp only [mul_zero] at hmajor
  have hbounds : ∀ᶠ N : ℕ in atTop, 0 ≤ neighborErrorFactor N ∧
      neighborErrorFactor N ≤ ((100000000 / 910 : ℝ) * 41) *
        ((1 + Real.log (Real.log (N : ℝ))) * Real.log (scaleBase N : ℝ) / Real.log N) := by
    filter_upwards [eventually_ge_atTop 1,
      log_nat_tendsto_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
      log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hL hS
    have hLpos : 0 < Real.log (N : ℝ) := by linarith
    obtain ⟨hWpos, hWlog⟩ := shortWidth_log_bound hN hL
    have hlogW : 0 ≤ Real.log (shortWidth N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr hWpos))
    rw [neighborErrorFactor_eq hLpos hS]
    constructor
    · positivity
    · calc
        _ ≤ (100000000 / 910 : ℝ) * (41 * (1 + Real.log (Real.log (N : ℝ)))) *
            Real.log (scaleBase N : ℝ) / Real.log N := by gcongr
        _ = _ := by ring
  exact squeeze_zero' (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2) hmajor

end Erdos380
