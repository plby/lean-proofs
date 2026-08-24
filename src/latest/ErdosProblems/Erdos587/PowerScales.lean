import ErdosProblems.Erdos587.NearbyScale

/-!
# A polynomial envelope for the critical nearby-mean parameters

The auxiliary scale is the fortieth root of the terminal size. The deliberately
loose exponents below leave room for every fixed logarithmic cutoff loss.
-/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma constant_mul_pow_le_pow {x c : ℝ} {a b : ℕ}
    (hx : 1 ≤ x) (hc : c ≤ x) (hab : a + 1 ≤ b) :
    c * x ^ a ≤ x ^ b := by
  calc
    c * x ^ a ≤ x * x ^ a := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = x ^ (a + 1) := by rw [pow_succ]; ring
    _ ≤ x ^ b := pow_le_pow_right₀ hx hab

lemma floor_fourth_power_bounds {x : ℝ} (hx : 2 ≤ x) :
    x ^ 3 ≤ (⌊x ^ 4⌋₊ : ℝ) ∧ (⌊x ^ 4⌋₊ : ℝ) ≤ x ^ 4 := by
  have hx1 : 1 ≤ x := by linarith
  have h1 : 1 ≤ x ^ 3 := one_le_pow₀ hx1
  have h2 : 2 * x ^ 3 ≤ x ^ 4 := constant_mul_pow_le_pow hx1 hx (by omega)
  have hf := Nat.lt_floor_add_one (x ^ 4)
  exact ⟨by linarith, Nat.floor_le (by positivity)⟩

lemma nearby_power_scale_conditions (u v M : ℕ) {x : ℝ} (hx : 256 ≤ x)
    (hu0 : x ^ 2 ≤ (u : ℝ)) (hu1 : (u : ℝ) ≤ x ^ 22)
    (hv0 : x ^ 28 ≤ (v : ℝ)) (hv1 : (v : ℝ) ≤ x ^ 30)
    (hM : (M : ℝ) * x ^ 19 ≤ v) :
    let Y := ⌊x ^ 4⌋₊
    1 ≤ Y ∧ 81 ≤ x ^ 20 ∧ (u : ℝ) * (x ^ 20) ^ 3 ≤ (v : ℝ) ^ 3 ∧
      4 * (Y : ℝ) * x ^ 20 ≤ v ∧ 64 * (M : ℝ) * x ^ 20 ≤ u * v ∧
      64 * ((u + v) * M + 1) ≤ Y ^ (4 ^ 2) := by
  let Y := ⌊x ^ 4⌋₊
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨hYlo, hYhi⟩ := floor_fourth_power_bounds (show 2 ≤ x by linarith)
  have hY1 : 1 ≤ Y := by
    have hh := (one_le_pow₀ hx1 : 1 ≤ x ^ 3).trans hYlo
    exact_mod_cast hh
  have h81 : 81 ≤ x ^ 20 := by
    exact (show (81 : ℝ) ≤ x by linarith).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hx1 (show 1 ≤ 20 by omega))
  have hpower : (u : ℝ) * (x ^ 20) ^ 3 ≤ (v : ℝ) ^ 3 := by
    calc
      _ ≤ x ^ 22 * (x ^ 20) ^ 3 := mul_le_mul_of_nonneg_right hu1 (by positivity)
      _ = x ^ 82 := by ring
      _ ≤ x ^ 84 := pow_le_pow_right₀ hx1 (by omega)
      _ = (x ^ 28) ^ 3 := by ring
      _ ≤ (v : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hv0 _
  have hYv : 4 * (Y : ℝ) * x ^ 20 ≤ v := by
    calc
      _ ≤ 4 * x ^ 4 * x ^ 20 := by gcongr
      _ = 4 * x ^ 24 := by ring
      _ ≤ x ^ 28 := constant_mul_pow_le_pow hx1 (by linarith) (by omega)
      _ ≤ v := hv0
  have hglobal : 64 * (M : ℝ) * x ^ 20 ≤ u * v := by
    calc
      _ = 64 * ((M : ℝ) * x ^ 19) * x := by ring
      _ ≤ 64 * (v : ℝ) * x := by gcongr
      _ = (64 * x) * v := by ring
      _ ≤ (x ^ 2) * v := by
        gcongr
        simpa only [pow_one] using
          constant_mul_pow_le_pow (a := 1) (b := 2) hx1 (show 64 ≤ x by linarith) (by omega)
      _ ≤ u * v := mul_le_mul_of_nonneg_right hu0 (by positivity)
  have hMupper : (M : ℝ) ≤ x ^ 11 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hx0 19)).mp
    calc
      _ ≤ (v : ℝ) := hM
      _ ≤ x ^ 30 := hv1
      _ = x ^ 11 * x ^ 19 := by ring
  have hu30 : (u : ℝ) ≤ x ^ 30 := hu1.trans (pow_le_pow_right₀ hx1 (by omega))
  have hsizeR : (64 : ℝ) * (((u : ℝ) + v) * M + 1) ≤ (Y : ℝ) ^ 16 := by
    calc
      _ ≤ 64 * ((2 * x ^ 30) * x ^ 11 + 1) := by gcongr; linarith
      _ = 64 * (2 * x ^ 41 + 1) := by ring
      _ ≤ 192 * x ^ 41 := by nlinarith [one_le_pow₀ hx1 (n := 41)]
      _ ≤ x ^ 48 := constant_mul_pow_le_pow hx1 (by linarith) (by omega)
      _ = (x ^ 3) ^ 16 := by ring
      _ ≤ (Y : ℝ) ^ 16 := pow_le_pow_left₀ (by positivity) hYlo _
  have hsize : 64 * ((u + v) * M + 1) ≤ Y ^ (4 ^ 2) := by
    norm_num at hsizeR ⊢
    exact_mod_cast hsizeR
  exact ⟨hY1, h81, hpower, hYv, hglobal, hsize⟩

lemma nearby_power_scale_log_bounds (u M : ℕ) {x : ℝ} (hx : 256 ≤ x)
    (hu : (u : ℝ) ≤ x ^ 22) (hM0 : 0 < M) (hM : (M : ℝ) ≤ x ^ 11) :
    1 + Real.log u ≤ 22 * (1 + Real.log x) ∧
      Real.log ((35 * M * (⌊x ^ 20⌋₊ + 1) : ℕ) : ℝ) ≤ 32 * (1 + Real.log x) := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hx20 : 1 ≤ x ^ 20 := one_le_pow₀ hx1
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨_, _, hK, _, _⟩ := rounded_physical_width_bounds hx20
  push_cast at hK
  have huLog : Real.log u ≤ 22 * Real.log x := by
    by_cases hu0 : u = 0
    · simp only [hu0, Nat.cast_zero, Real.log_zero]
      positivity
    · have hupos : (0 : ℝ) < u := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hu0)
      have hh := Real.log_le_log hupos hu
      simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hZpos : (0 : ℝ) < ((35 * M * (⌊x ^ 20⌋₊ + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by positivity : 0 < 35 * M * (⌊x ^ 20⌋₊ + 1))
  have hZ : (((35 * M * (⌊x ^ 20⌋₊ + 1) : ℕ) : ℝ)) ≤ x ^ 32 := by
    push_cast
    calc
      _ ≤ 35 * x ^ 11 * (2 * x ^ 20) := by gcongr
      _ = 70 * x ^ 31 := by ring
      _ ≤ x ^ 32 := constant_mul_pow_le_pow hx1 (by linarith) (by omega)
  have hlog := Real.log_le_log hZpos hZ
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  exact ⟨by linarith, by linarith⟩

theorem exists_nearby_mean_bound_of_power_scales (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a u v M : ℕ),
      0 < u → 0 < v → 0 < M → a.Coprime u → u.Coprime v → u ∣ a * v + 1 →
      ∀ x : ℝ, 256 ≤ x → x ^ 2 ≤ (u : ℝ) → (u : ℝ) ≤ x ^ 22 →
        x ^ 28 ≤ (v : ℝ) → (v : ℝ) ≤ x ^ 30 → (M : ℝ) * x ^ 19 ≤ v →
        (u : ℝ) * v ≤ M * x ^ 40 →
        (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f u m v (a : ℤ) (x ^ 20)‖) ≤
          C * M * x ^ 10 * (1 + Real.log x) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_nearby_mean_bound_of_global_scales 2 f
  refine ⟨22 * C * 32 ^ O, by positivity, O + 1, by omega, ?_⟩
  intro a u v M hu hv hM ha huv hav x hx hu0 hu1 hv0 hv1 hcut hcutlo
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨hY, h81, hpower, hYv, hglobal, hsize⟩ :=
    nearby_power_scale_conditions u v M hx hu0 hu1 hv0 hv1 hcut
  have hcutlo' : (u : ℝ) * v / (x ^ 20) ^ 2 ≤ M := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [← pow_mul] using hcutlo
  have hbound := hmean a u v M ⌊x ^ 4⌋₊ hu hv hM hY ha huv hav
    (x ^ 20) h81 hpower hcutlo' hYv hglobal hsize
  have hsqrt : Real.sqrt (x ^ 20) = x ^ 10 := by
    rw [show x ^ 20 = (x ^ 10) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsqrt] at hbound
  have hMupper : (M : ℝ) ≤ x ^ 11 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hx0 19)).mp
    calc
      _ ≤ (v : ℝ) := hcut
      _ ≤ x ^ 30 := hv1
      _ = x ^ 11 * x ^ 19 := by ring
  obtain ⟨hlogu, hlogZ⟩ := nearby_power_scale_log_bounds u M hx hu1 hM hMupper
  have hlogZ0 : 0 ≤ Real.log ((35 * M * (⌊x ^ 20⌋₊ + 1) : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.succ_le_of_lt
      (by positivity : 0 < 35 * M * (⌊x ^ 20⌋₊ + 1)))
  have hlogu0 : 0 ≤ 1 + Real.log u := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ u by exact_mod_cast hu)
    linarith
  calc
    _ ≤ C * M * x ^ 10 * (1 + Real.log u) *
        Real.log ((35 * M * (⌊x ^ 20⌋₊ + 1) : ℕ) : ℝ) ^ O := hbound
    _ ≤ C * M * x ^ 10 * (22 * (1 + Real.log x)) *
        (32 * (1 + Real.log x)) ^ O := by gcongr
    _ = (22 * C * 32 ^ O) * M * x ^ 10 * (1 + Real.log x) ^ (O + 1) := by
      rw [mul_pow, pow_succ]
      ring

end Erdos587
