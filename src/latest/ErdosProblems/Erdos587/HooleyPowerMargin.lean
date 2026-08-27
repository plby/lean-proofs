import ErdosProblems.Erdos587.HooleyDenominatorBlocks

/-! # Absorbing the short-progression cost under fixed power separation -/

namespace Erdos587

noncomputable def deltaProgressionCutoff (r N : ℕ) : ℕ :=
  16 + ⌈(N : ℝ) ^ (r : ℝ)⁻¹⌉₊

lemma deltaProgressionCutoff_ge_sixteen (r N : ℕ) : 16 ≤ deltaProgressionCutoff r N := by
  simp only [deltaProgressionCutoff]
  omega

lemma deltaProgressionCutoff_power {r : ℕ} (hr : 0 < r) (N : ℕ) :
    N ≤ deltaProgressionCutoff r N ^ r := by
  have hroot : (N : ℝ) ^ (r : ℝ)⁻¹ ≤ (deltaProgressionCutoff r N : ℝ) := by
    have h := Nat.le_ceil ((N : ℝ) ^ (r : ℝ)⁻¹)
    simp only [deltaProgressionCutoff, Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hroot r
  rw [Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) hr.ne'] at hpow
  exact_mod_cast hpow

lemma deltaProgressionCutoff_le {r N : ℕ} (hr : 0 < r) (hN : 1 ≤ N) :
    (deltaProgressionCutoff r N : ℝ) ≤ 18 * (N : ℝ) ^ (r : ℝ)⁻¹ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hroot : 1 ≤ (N : ℝ) ^ (r : ℝ)⁻¹ :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) (r : ℝ)⁻¹)
  simp only [deltaProgressionCutoff, Nat.cast_add, Nat.cast_ofNat]
  linarith

lemma delta_dyadic_scale_rpow_bound {r N D : ℕ} (hr : 0 < r) (hN : 1 ≤ N)
    (hD : 2 ^ D ≤ N) :
    (D : ℝ) + 3 ≤ ((r : ℝ) / Real.log 2 + 3) * (N : ℝ) ^ (r : ℝ)⁻¹ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : (D : ℝ) * Real.log 2 ≤ Real.log N :=
    (Real.pow_le_iff_le_log (by norm_num : (0 : ℝ) < 2) hN0).mp (by exact_mod_cast hD)
  have hlog := Real.log_le_rpow_div hN0.le (inv_pos.mpr hrR)
  rw [div_inv_eq_mul] at hlog
  have hroot : 1 ≤ (N : ℝ) ^ (r : ℝ)⁻¹ :=
    Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hD' : (D : ℝ) ≤ (r : ℝ) / Real.log 2 * (N : ℝ) ^ (r : ℝ)⁻¹ := by
    calc
      _ ≤ ((N : ℝ) ^ (r : ℝ)⁻¹ * r) / Real.log 2 :=
        (le_div_iff₀ hlog2).mpr (hlogD.trans hlog)
      _ = _ := by ring
  nlinarith

theorem exists_delta_power_margin_bound (r : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N q D : ℕ, 1 ≤ N → 2 ^ D ≤ N →
      (q : ℝ) * (N : ℝ) ^ (3 / (r : ℝ)) ≤ N →
      (q : ℝ) * (N : ℝ) ^ (r : ℝ)⁻¹ *
        (2 * deltaProgressionCutoff r N + D + 1) * (D + 3) ≤ C * N := by
  let A := (r : ℝ) / Real.log 2 + 3
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨(36 + A) * A, by positivity, ?_⟩
  intro N q D hN hD hsep
  let R := (N : ℝ) ^ (r : ℝ)⁻¹
  have hR : 0 ≤ R := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hY := deltaProgressionCutoff_le hr hN
  have hD' := delta_dyadic_scale_rpow_bound hr hN hD
  change (D : ℝ) + 3 ≤ A * R at hD'
  have hfirst : (2 : ℝ) * deltaProgressionCutoff r N + D + 1 ≤ (36 + A) * R := by
    change (deltaProgressionCutoff r N : ℝ) ≤ 18 * R at hY
    nlinarith
  have hpower : R ^ 3 = (N : ℝ) ^ (3 / (r : ℝ)) := by
    dsimp only [R]
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg N)]
    congr 1
    norm_num
    ring
  calc
    _ ≤ ((q : ℝ) * R * ((36 + A) * R)) * (A * R) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hfirst (by positivity)) hD'
        (by positivity) (by positivity)
    _ = ((36 + A) * A) * ((q : ℝ) * R ^ 3) := by ring
    _ ≤ ((36 + A) * A) * N := by
      rw [hpower]
      exact mul_le_mul_of_nonneg_left hsep (by positivity)

end Erdos587
