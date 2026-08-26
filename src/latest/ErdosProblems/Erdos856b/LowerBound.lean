import ErdosProblems.Erdos856b.Selections
import ErdosProblems.Erdos856b.PrimeBuckets

/-! # The unconditional weighted lower bound -/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

noncomputable def exponentRatio (k N : ℕ) : ℝ := log (f k N) / logScale N

theorem one_le_f {k N : ℕ} (hk : 3 ≤ k) (hN : 1 ≤ N) : 1 ≤ f k N := by
  have hfree : LcmFree k {1} := by
    apply (lcmFree_iff_unionFree_primeFactors (by simp)).mpr
    simpa using unionFree_singleton hk (∅ : Finset ℕ)
  have h := reciprocalWeight_le_f (by simpa using hN : ({1} : Finset ℕ) ⊆ Finset.Icc 1 N) hfree
  simpa [reciprocalWeight] using h

theorem eventually_C_le_f {k : ℕ} (hk : 3 ≤ k) {a z : ℝ}
    (ha : 0 < a) (hz : 0 < z) (haz : a * z < 1) :
    ∀ᶠ N : ℕ in atTop, C k (bucketCount a N) z ≤ f k N := by
  let δ := (1 - a * z) / (2 * a)
  have hδ : 0 < δ := div_pos (by linarith) (by positivity)
  have hsmall : a * (z + δ) < 1 := by
    dsimp [δ]
    have ha0 : a ≠ 0 := ha.ne'
    field_simp
    nlinarith
  filter_upwards [eventually_prime_buckets ha hz hδ hsmall] with N hN
  obtain ⟨ht, hX, hsize, P, hdis, hP, hw⟩ := hN
  exact C_le_f_of_prime_buckets hk ht hdis (fun i p hp => (hP i p hp).1) hX
    (fun i p hp => (hP i p hp).2) hsize hz.le hw

theorem tendsto_bucket_log_C_div {k : ℕ} (hk : 3 ≤ k) {a z : ℝ}
    (ha : 0 < a) (hz : 0 < z) :
    Tendsto (fun N => log (C k (bucketCount a N) z) / logScale N) atTop
      (𝓝 (a * logPressure k z)) := by
  have hC := (tendsto_log_C_div hk hz).comp (tendsto_bucketCount ha)
  have h := hC.mul (tendsto_bucketCount_div ha)
  rw [mul_comm (logPressure k z) a] at h
  apply h.congr'
  filter_upwards [(tendsto_bucketCount ha).eventually_gt_atTop 0] with N hN
  have hN0 : (bucketCount a N : ℝ) ≠ 0 := by positivity
  dsimp [Function.comp_def]
  field_simp

theorem weighted_lower_bound_param {k : ℕ} (hk : 3 ≤ k) {a z : ℝ}
    (ha : 0 < a) (hz : 0 < z) (haz : a * z < 1) {b : ℝ}
    (hb : b < a * logPressure k z) :
    ∀ᶠ N : ℕ in atTop, b < exponentRatio k N := by
  have hlimit := (tendsto_bucket_log_C_div hk ha hz).eventually (lt_mem_nhds hb)
  filter_upwards [hlimit, eventually_C_le_f hk ha hz haz,
    tendsto_logScale.eventually_gt_atTop 0] with N hN hCf hL
  apply hN.trans_le
  exact div_le_div_of_nonneg_right (log_le_log (C_pos hk hz) hCf) hL.le

/-- Theorem 3.5, stated directly as an eventual lower bound on the logarithmic ratio. -/
theorem weighted_lower_bound {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) {b : ℝ}
    (hb : b < logPressure k z / z) :
    ∀ᶠ N : ℕ in atTop, b < exponentRatio k N := by
  have hH : 0 ≤ logPressure k z := logPressure_nonneg hk hz
  by_cases hzero : logPressure k z = 0
  · have hb0 : b < 0 := by simpa [hzero] using hb
    apply weighted_lower_bound_param hk (a := 1 / (2 * z)) (by positivity) hz
    · have hz0 : z ≠ 0 := hz.ne'
      field_simp
      linarith
    · simpa [hzero] using hb0
  · have hHpos : 0 < logPressure k z := lt_of_le_of_ne hH (Ne.symm hzero)
    have hright : max 0 (b / logPressure k z) < 1 / z := by
      apply max_lt (by positivity)
      apply (div_lt_div_iff₀ hHpos hz).mpr
      have h := (lt_div_iff₀ hz).mp hb
      simpa using h
    obtain ⟨a, ha, haz⟩ := exists_between hright
    apply weighted_lower_bound_param hk
      ((le_max_left _ _).trans_lt ha) hz ((lt_div_iff₀ hz).mp haz)
    exact (div_lt_iff₀ hHpos).mp ((le_max_right _ _).trans_lt ha)

theorem lower_bound_gamma {k : ℕ} (hk : 3 ≤ k) {b : ℝ} (hb : b < gamma k) :
    ∀ᶠ N : ℕ in atTop, b < exponentRatio k N := by
  rw [gamma_eq_sup_logPressure_div hk] at hb
  have hne : ({v : ℝ | ∃ z : ℝ, 0 < z ∧ v = logPressure k z / z} : Set ℝ).Nonempty :=
    ⟨logPressure k 1 / 1, 1, by norm_num, rfl⟩
  obtain ⟨v, hv, hbv⟩ := exists_lt_of_lt_csSup hne hb
  obtain ⟨z, hz, rfl⟩ := hv
  exact weighted_lower_bound hk hz hbv

/-- The finite-block exponent gives the claimed lower bound for every positive error. -/
theorem eventually_lower_bound {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (log (N : ℝ)) ^ (gamma k - ε) ≤ f k N := by
  filter_upwards [lower_bound_gamma hk (by linarith : gamma k - ε < gamma k),
    tendsto_logScale.eventually_gt_atTop 0, eventually_gt_atTop (1 : ℕ)] with N hN hL hN1
  have hfpos : 0 < f k N := lt_of_lt_of_le zero_lt_one (one_le_f hk (by omega))
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN1)
  have hlog := (lt_div_iff₀ hL).mp hN
  rw [rpow_def_of_pos hlogN, ← exp_log hfpos]
  apply exp_le_exp.mpr
  exact le_of_lt (by simpa [logScale, mul_comm] using hlog)

end Erdos856b
