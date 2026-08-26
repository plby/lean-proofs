import ErdosProblems.Erdos421.GeometricDensity

/-! # Extending a zero density limit from geometric endpoints -/

namespace Erdos421

open Filter Topology

theorem geometric_prefix_ratio_tendsto_of_limit {f : ℕ → ℕ} (hf : Monotone f)
    {b : ℕ} (hb : 1 < b)
    (hlimit : Tendsto (fun u : ℕ ↦ (f (b ^ u) : ℝ) / (b ^ u : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (f n : ℝ) / n) atTop (𝓝 0) := by
  have hbp : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hshift : Tendsto (fun n : ℕ ↦ Nat.log b n + 1) atTop atTop := by
    apply tendsto_atTop_atTop.mpr
    intro m
    obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp (nat_log_tendsto hb) m
    exact ⟨N, fun n hn ↦ (hN n hn).trans (Nat.le_add_right _ _)⟩
  have hmajor : Tendsto (fun n : ℕ ↦ (b : ℝ) *
      ((f (b ^ (Nat.log b n + 1)) : ℝ) / (b ^ (Nat.log b n + 1) : ℕ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using (hlimit.comp hshift).const_mul (b : ℝ)
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) _ hmajor
  filter_upwards [eventually_gt_atTop 0] with n hn
  let u := Nat.log b n
  have hnupper : n ≤ b ^ (u + 1) := (Nat.lt_pow_succ_log_self hb n).le
  have hnlower : b ^ u ≤ n := Nat.pow_log_le_self b hn.ne'
  have hden : (0 : ℝ) < (b ^ u : ℕ) := by exact_mod_cast (pow_pos (by omega : 0 < b) u)
  calc
    _ ≤ (f (b ^ (u + 1)) : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast hf hnupper
    _ ≤ (f (b ^ (u + 1)) : ℝ) / (b ^ u : ℕ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden (by exact_mod_cast hnlower)
    _ = _ := by
      dsimp only [u]
      push_cast
      rw [pow_succ]
      field_simp
      ring

theorem hasDensity_zero_of_geometric_limit (S : Set ℕ) {b : ℕ} (hb : 1 < b)
    (hlimit : Tendsto (fun u : ℕ ↦ (prefixCount S (b ^ u) : ℝ) / (b ^ u : ℕ)) atTop (𝓝 0)) :
    S.HasDensity 0 := by
  simp only [Set.HasDensity, partialDensity_eq_prefixCount]
  exact geometric_prefix_ratio_tendsto_of_limit (prefixCount_mono S) hb hlimit

end Erdos421
