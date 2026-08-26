import ErdosProblems.Erdos856b.Pressure

/-! # Existence of the weighted cosunflower pressure -/

namespace Erdos856b

open Real Filter
open scoped BigOperators Topology

/-- Logarithm of the largest weighted uniform layer on `n` points. -/
noncomputable def uniformLog (k n : ℕ) (z : ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' (by simp) (fun r => log (M k n r) + r * log z)

theorem uniformLog_attained (k n : ℕ) (z : ℝ) :
    ∃ r : ℕ, r ≤ n ∧ uniformLog k n z = log (M k n r) + r * log z := by
  obtain ⟨r, hr, hmax⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.range (n + 1)).Nonempty by simp)
    (fun r => log (M k n r) + r * log z)
  exact ⟨r, by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr, hmax⟩

theorem le_uniformLog {k n r : ℕ} (hr : r ≤ n) (z : ℝ) :
    log (M k n r) + r * log z ≤ uniformLog k n z := by
  unfold uniformLog
  exact Finset.le_sup' (s := Finset.range (n + 1))
    (fun r => log (M k n r) + r * log z) (Finset.mem_range.mpr (by omega))

theorem uniformLog_nonneg {k : ℕ} (hk : 3 ≤ k) (n : ℕ) (z : ℝ) :
    0 ≤ uniformLog k n z := by
  simpa [M_rank_zero hk] using le_uniformLog (k := k) (Nat.zero_le n) z

theorem uniformLog_le_mul_logPressure {k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    {z : ℝ} (hz : 0 < z) : uniformLog k n z ≤ n * logPressure k z := by
  obtain ⟨r, hr, heq⟩ := uniformLog_attained k n z
  rw [heq]
  have h := log_M_weight_div_le_logPressure hk hn hr hz
  simpa [mul_comm] using (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mp h

theorem uniformLog_superadditive {k : ℕ} (hk : 3 ≤ k) (z : ℝ) (n m : ℕ) :
    uniformLog k n z + uniformLog k m z ≤ uniformLog k (n + m) z := by
  obtain ⟨r, hr, hnr⟩ := uniformLog_attained k n z
  obtain ⟨s, hs, hms⟩ := uniformLog_attained k m z
  have hM1 : (0 : ℝ) < M k n r := by exact_mod_cast M_pos hk hr
  have hM2 : (0 : ℝ) < M k m s := by exact_mod_cast M_pos hk hs
  have hlog : log (M k n r) + log (M k m s) ≤ log (M k (n + m) (r + s)) := by
    rw [← log_mul hM1.ne' hM2.ne']
    apply log_le_log (mul_pos hM1 hM2)
    exact_mod_cast M_mul_le hk n m r s
  have hbound := le_uniformLog (k := k) (show r + s ≤ n + m by omega) z
  rw [hnr, hms]
  push_cast at hbound
  linarith

theorem tendsto_uniformLog_div {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => uniformLog k n z / n) atTop (𝓝 (logPressure k z)) := by
  have hsub : Subadditive (fun n => -uniformLog k n z) := by
    intro n m
    linarith [uniformLog_superadditive hk z n m]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨b, hb, hab⟩ := exists_lt_of_lt_csSup (show (logPressureScores k z).Nonempty from
      ⟨0, zero_mem_logPressureScores hk z⟩) ha
    obtain ⟨n, r, hn, hr, rfl⟩ := hb
    have hnval : a < uniformLog k n z / n := hab.trans_le
      (div_le_div_of_nonneg_right (le_uniformLog hr z) (by positivity))
    have hneg : -uniformLog k n z / n < -a := by
      rw [neg_div]
      linarith
    have hev := hsub.eventually_div_lt_of_div_lt hn.ne' hneg
    filter_upwards [hev] with m hm
    rw [neg_div] at hm
    linarith
  · intro b hb
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
      (by simpa [mul_comm] using uniformLog_le_mul_logPressure hk hn hz) |>.trans_lt hb

noncomputable def partitionWeight {α : Type*} (F : Finset (Finset α)) (z : ℝ) : ℝ :=
  ∑ s ∈ F, z ^ s.card

noncomputable def allUnionFreeFamilies (k n : ℕ) : Finset (Finset (Finset (Fin n))) := by
  classical
  exact insert ∅ (Finset.univ.filter (UnionFree k))

/-- `C_k(n; z)` from Section 2. The empty family is explicitly included. -/
noncomputable def C (k n : ℕ) (z : ℝ) : ℝ :=
  (allUnionFreeFamilies k n).sup' (by
    classical
    simp [allUnionFreeFamilies])
    (fun F => partitionWeight F z)

theorem partitionWeight_uniform {α : Type*} {F : Finset (Finset α)} {r : ℕ}
    (hU : Uniform r F) (z : ℝ) : partitionWeight F z = F.card * z ^ r := by
  unfold partitionWeight
  simp_rw [Finset.sum_congr rfl (fun s hs => congrArg (z ^ ·) (hU s hs)), Finset.sum_const]
  simp

theorem partitionWeight_le_C {k n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : UnionFree k F) (z : ℝ) : partitionWeight F z ≤ C k n z := by
  classical
  unfold C
  exact Finset.le_sup' (s := allUnionFreeFamilies k n) (fun G => partitionWeight G z)
    (b := F) (by simp [allUnionFreeFamilies, hF])

theorem exp_uniformLog_le_C {k n : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    exp (uniformLog k n z) ≤ C k n z := by
  obtain ⟨r, hr, hmax⟩ := uniformLog_attained k n z
  obtain ⟨F, hU, hF, hcard⟩ := M_attained (by omega : 0 < k) n r
  have hM : (0 : ℝ) < M k n r := by exact_mod_cast M_pos hk hr
  rw [hmax, ← log_pow, ← log_mul hM.ne' (pow_pos hz _).ne',
    exp_log (mul_pos hM (pow_pos hz _))]
  have h := partitionWeight_le_C hF z
  simpa [partitionWeight_uniform hU, hcard] using h

theorem UnionFree.mono {k : ℕ} {α : Type*} [DecidableEq α]
    {F G : Finset (Finset α)} (hF : UnionFree k F) (hGF : G ⊆ F) : UnionFree k G :=
  fun a ha hmem => hF a ha (fun i => hGF (hmem i))

theorem partitionWeight_le_layers {k n : ℕ} {F : Finset (Finset (Fin n))}
    (hF : UnionFree k F) {z : ℝ} (hz : 0 ≤ z) :
    partitionWeight F z ≤ ∑ r ∈ Finset.range (n + 1), (M k n r : ℝ) * z ^ r := by
  classical
  unfold partitionWeight
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := Finset.range (n + 1)) (g := Finset.card) (by
      intro s _
      simpa using Nat.lt_succ_of_le (Finset.card_le_univ s))]
  apply Finset.sum_le_sum
  intro r _
  let G := F.filter (fun s => s.card = r)
  have hU : Uniform r G := by intro s hs; exact (Finset.mem_filter.mp hs).2
  have hfree : UnionFree k G := hF.mono (Finset.filter_subset (fun s => s.card = r) F)
  have hcard := card_le_M hU hfree
  change partitionWeight G z ≤ _
  rw [partitionWeight_uniform hU]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (pow_nonneg hz _)

theorem C_le_exp_uniformLog {k n : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    C k n z ≤ (n + 1) * exp (uniformLog k n z) := by
  classical
  unfold C
  apply Finset.sup'_le
  intro F hF
  have hfree : UnionFree k F := by
    simp only [allUnionFreeFamilies, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and] at hF
    rcases hF with rfl | hF
    · exact unionFree_empty (by omega)
    · exact hF
  apply (partitionWeight_le_layers hfree hz.le).trans
  calc
    ∑ r ∈ Finset.range (n + 1), (M k n r : ℝ) * z ^ r ≤
        ∑ _r ∈ Finset.range (n + 1), exp (uniformLog k n z) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrn : r ≤ n := by simpa using hr
      have hM : (0 : ℝ) < M k n r := by exact_mod_cast M_pos hk hrn
      rw [← exp_log (mul_pos hM (pow_pos hz _)), log_mul hM.ne' (pow_pos hz _).ne', log_pow]
      exact exp_le_exp.mpr (le_uniformLog hrn z)
    _ = (n + 1) * exp (uniformLog k n z) := by simp

theorem C_pos {k n : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) : 0 < C k n z :=
  (exp_pos _).trans_le (exp_uniformLog_le_C hk hz)

theorem log_C_bounds {k n : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    uniformLog k n z ≤ log (C k n z) ∧
      log (C k n z) ≤ log (n + 1) + uniformLog k n z := by
  constructor
  · have h := log_le_log (exp_pos _) (exp_uniformLog_le_C (n := n) hk hz)
    simpa using h
  · have h := log_le_log (C_pos (n := n) hk hz) (C_le_exp_uniformLog (n := n) hk hz)
    simpa [log_mul (by positivity : (n : ℝ) + 1 ≠ 0) (exp_ne_zero _)] using h

theorem tendsto_log_nat_add_one_div :
    Tendsto (fun n : ℕ => log (n + 1) / n) atTop (𝓝 0) := by
  have harg : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) _ tendsto_natCast_atTop_atTop
    intro n
    linarith
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    harg
  simpa [Function.comp_def] using h

theorem tendsto_log_C_div {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => log (C k n z) / n) atTop (𝓝 (logPressure k z)) := by
  have hU := tendsto_uniformLog_div hk hz
  have hupper := tendsto_log_nat_add_one_div.add hU
  simp only [zero_add] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hU hupper
  · filter_upwards with n
    exact div_le_div_of_nonneg_right (log_C_bounds hk hz).1 (by positivity)
  · filter_upwards with n
    simpa [add_div] using div_le_div_of_nonneg_right (log_C_bounds hk hz).2
      (by positivity : (0 : ℝ) ≤ n)

/-- The pressure limit in Proposition 2.2, with its uniform representation. -/
theorem tendsto_C_root {k : ℕ} (hk : 3 ≤ k) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => C k n z ^ (1 / (n : ℝ))) atTop
      (𝓝 (exp (logPressure k z))) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp (tendsto_log_C_div hk hz)
  convert h using 1
  ext n
  rw [rpow_def_of_pos (C_pos hk hz)]
  congr 1
  ring

end Erdos856b
