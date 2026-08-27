import ErdosProblems.Erdos587.HooleyNearbyMean
import ErdosProblems.Erdos587.PowerScales

/-! # A polynomial envelope for the log-log nearby mean -/

open scoped BigOperators SchwartzMap

namespace Erdos587

lemma delta_floor_fortieth_power_bounds {x : ℝ} (hx : 2 ≤ x) :
    x ^ 39 ≤ (⌊x ^ 40⌋₊ : ℝ) ∧ (⌊x ^ 40⌋₊ : ℝ) ≤ x ^ 40 := by
  have hx1 : 1 ≤ x := by linarith
  have h1 : 1 ≤ x ^ 39 := one_le_pow₀ hx1
  have h2 : 2 * x ^ 39 ≤ x ^ 40 := constant_mul_pow_le_pow hx1 hx (by omega)
  have hf := Nat.lt_floor_add_one (x ^ 40)
  exact ⟨by linarith, Nat.floor_le (by positivity)⟩

lemma delta_nearby_power_scale_conditions (u v M : ℕ) {x : ℝ} (hx : 256 ≤ x)
    (hu0 : x ^ 2 ≤ (u : ℝ)) (hu1 : (u : ℝ) ≤ x ^ 22)
    (hv0 : x ^ 28 ≤ (v : ℝ)) (hv1 : (v : ℝ) ≤ x ^ 30)
    (hM : (M : ℝ) * x ^ 19 ≤ v) :
    let X := ⌊x ^ 40⌋₊
    2 ≤ X ∧ u ≤ X ∧ 4 * x ^ 20 * (X : ℝ) ^ (1 / 40 : ℝ) ≤ v ∧
      4 * (M : ℝ) * x ^ 20 ≤ u * v ∧ (4 * x ^ 20 + 16 * u) * M ≤ X := by
  let X := ⌊x ^ 40⌋₊
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  obtain ⟨hXlo, hXhi⟩ := delta_floor_fortieth_power_bounds (show 2 ≤ x by linarith)
  have hx39 : x ≤ x ^ 39 := by
    simpa only [pow_one] using pow_le_pow_right₀ hx1 (show 1 ≤ 39 by omega)
  have hX2 : 2 ≤ X := by
    have ht : (2 : ℝ) ≤ X := (show (2 : ℝ) ≤ x by linarith).trans (hx39.trans hXlo)
    exact_mod_cast ht
  have huX : u ≤ X := by
    have ht := (hu1.trans (pow_le_pow_right₀ hx1 (show 22 ≤ 39 by omega))).trans hXlo
    exact_mod_cast ht
  have hroot : (X : ℝ) ^ (1 / 40 : ℝ) ≤ x := by
    calc
      _ ≤ (x ^ 40) ^ (1 / 40 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg X) hXhi (by norm_num)
      _ = x := by
        simpa only [Nat.cast_ofNat, one_div] using
          Real.pow_rpow_inv_natCast hx0.le (show (40 : ℕ) ≠ 0 by omega)
  have hsep : 4 * x ^ 20 * (X : ℝ) ^ (1 / 40 : ℝ) ≤ v := by
    calc
      _ ≤ 4 * x ^ 20 * x := by gcongr
      _ = 4 * x ^ 21 := by ring
      _ ≤ x ^ 28 := constant_mul_pow_le_pow hx1 (by linarith) (by omega)
      _ ≤ v := hv0
  have hglobal : 4 * (M : ℝ) * x ^ 20 ≤ u * v := by
    calc
      _ = 4 * ((M : ℝ) * x ^ 19) * x := by ring
      _ ≤ 4 * (v : ℝ) * x := by gcongr
      _ = (4 * x) * v := by ring
      _ ≤ (x ^ 2) * v := by
        gcongr
        simpa only [pow_one] using
          constant_mul_pow_le_pow (a := 1) (b := 2) hx1 (show 4 ≤ x by linarith) (by omega)
      _ ≤ u * v := mul_le_mul_of_nonneg_right hu0 (by positivity)
  have hMupper : (M : ℝ) ≤ x ^ 11 := by
    apply (mul_le_mul_iff_left₀ (pow_pos hx0 19)).mp
    calc
      _ ≤ (v : ℝ) := hM
      _ ≤ x ^ 30 := hv1
      _ = x ^ 11 * x ^ 19 := by ring
  have hsize : (4 * x ^ 20 + 16 * u) * M ≤ (X : ℝ) := by
    calc
      _ ≤ (20 * x ^ 22) * x ^ 11 := by
        gcongr
        have ht : x ^ 20 ≤ x ^ 22 := pow_le_pow_right₀ hx1 (by omega)
        linarith
      _ = 20 * x ^ 33 := by ring
      _ ≤ x ^ 39 := constant_mul_pow_le_pow hx1 (by linarith) (by omega)
      _ ≤ X := hXlo
  exact ⟨hX2, huX, hsep, hglobal, hsize⟩

theorem exists_delta_nearby_mean_of_power_scales (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u v M : ℕ, 0 < u → 0 < v → a.Coprime u →
      u.Coprime v → u ∣ a * v + 1 →
      ∀ x : ℝ, 256 ≤ x → x ^ 2 ≤ (u : ℝ) → (u : ℝ) ≤ x ^ 22 →
      x ^ 28 ≤ (v : ℝ) → (v : ℝ) ≤ x ^ 30 → (M : ℝ) * x ^ 19 ≤ v →
      (u : ℝ) * v ≤ M * x ^ 40 →
      (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f u m v (a : ℤ) (x ^ 20)‖) ≤
        C * M * x ^ 10 * (max 1 (Real.log (Real.log (x ^ 40)))) ^ (9 / 2 : ℝ) := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_nearby_mean f (κ := 1 / 40) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro a u v M hu hv ha huv hav x hx hu0 hu1 hv0 hv1 hcut hcutlo
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  let X := ⌊x ^ 40⌋₊
  let M₀ := ⌊(u : ℝ) * v / (x ^ 20) ^ 2⌋₊
  obtain ⟨hX, huX, hsep, hglobal, hsize⟩ :=
    delta_nearby_power_scale_conditions u v M hx hu0 hu1 hv0 hv1 hcut
  have hM₀M : M₀ ≤ M := by
    apply Nat.floor_le_of_le
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [← pow_mul] using hcutlo
  have hbound := hmean a u v M M₀ X hu hv ha huv hav hM₀M hX huX (x ^ 20)
    (one_le_pow₀ hx1) (Nat.floor_le (by positivity)) (Nat.lt_floor_add_one _)
    hsep hglobal hsize
  have hsqrt : Real.sqrt (x ^ 20) = x ^ 10 := by
    rw [show x ^ 20 = (x ^ 10) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsqrt] at hbound
  have hlog : max 1 (Real.log (Real.log (X : ℝ))) ≤
      max 1 (Real.log (Real.log (x ^ 40))) := by
    apply max_le_max le_rfl
    apply Real.log_le_log (Real.log_pos (by exact_mod_cast (show 1 < X by omega)))
    exact Real.log_le_log (by exact_mod_cast (show 0 < X by omega))
      (Nat.floor_le (by positivity))
  apply hbound.trans
  gcongr

end Erdos587
