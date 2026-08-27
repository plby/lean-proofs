import ErdosProblems.Erdos4.TiltedCompositeParameters

/-! The inverse survival weights and maximal gcd tilt are smaller than any fixed power of x. -/

namespace Erdos4.Tilted

open Filter

theorem block_exponent_budget {L l t A C K v H δ : ℝ}
    (hL : 0 < L) (hl : 0 < l) (ht : 0 < t) (hA : 0 ≤ A) (_hC : 0 ≤ C) (_hδ : 0 ≤ δ)
    (_hK0 : 0 ≤ K) (hK : K ≤ A * L / (t * l))
    (hv0 : 0 ≤ v) (hv : v ≤ 2 * L) (hH0 : 0 ≤ H) (hH : H ≤ C * l)
    (hlarge_l : 8 * A ≤ δ * l) (hlarge_t : 16 * A * C ≤ δ * t)
    (hsmall_l : 8 * C * l ≤ δ * L) :
    (t / L) * K * v + (4 * K + 2) * H ≤ δ * L := by
  have hmain : (t / L) * K * v + (4 * K + 2) * H ≤
      2 * A * L / l + 4 * A * C * L / t + 2 * C * l := by
    calc
      _ ≤ (t / L) * (A * L / (t * l)) * (2 * L) +
          (4 * (A * L / (t * l)) + 2) * (C * l) := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hK (div_nonneg ht.le hL.le)) hv hv0 (by positivity)
        · exact mul_le_mul (by linarith) hH hH0 (by positivity)
      _ = _ := by field_simp; ring
  have hfirst : 2 * A * L / l ≤ δ * L / 4 := by
    apply (div_le_iff₀ hl).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlarge_l hL.le]
  have hsecond : 4 * A * C * L / t ≤ δ * L / 4 := by
    apply (div_le_iff₀ ht).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlarge_t hL.le]
  have hthird : 2 * C * l ≤ δ * L / 4 := by linarith
  nlinarith [mul_nonneg _hδ hL.le]

theorem eventually_block_exponent_budget {A C δ : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hδ : 0 < δ) :
    ∀ᶠ x : ℕ in atTop, ∀ Y K : ℕ, ∀ H : ℝ,
      1 ≤ Y → Y ≤ x ^ 2 →
      (K : ℝ) ≤ A * outerScale x / Real.log (Real.log (x : ℝ)) →
      0 ≤ H → H ≤ C * Real.log (Real.log (x : ℝ)) →
      tiltExponent x * K * Real.log Y + (4 * (K : ℝ) + 2) * H ≤ δ * Real.log (x : ℝ) := by
  filter_upwards [eventually_outerScale_bounds,
    log_two_tendsto.eventually (eventually_ge_atTop (8 * A / δ)),
    tiltScale_tendsto.eventually (eventually_ge_atTop (16 * A * C / δ)),
    eventually_iterated_log_power_le 1 (8 * C / δ) (by norm_num : (0 : ℝ) < 1)]
    with x hb hl ht hsmall
  intro Y K H hY hYX hK hH0 hH
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let t := tiltScale x
  have hLpos : 0 < L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have hlpos : 0 < l := by have hh := hb.2.1; change 1 ≤ l at hh; linarith
  have htpos : 0 < t := by have hh := hb.2.2.1; change 1 ≤ t at hh; linarith
  have hK' : (K : ℝ) ≤ A * L / (t * l) := by
    apply hK.trans_eq
    dsimp [outerScale, L, l, t]
    ring
  have hv : Real.log (Y : ℝ) ≤ 2 * L := by
    have hh := Real.log_le_log (by exact_mod_cast hY : (0 : ℝ) < Y)
      (by exact_mod_cast hYX : (Y : ℝ) ≤ (x : ℝ) ^ 2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlarge_l : 8 * A ≤ δ * l := by
    have hh := (div_le_iff₀ hδ).mp hl
    change 8 * A ≤ l * δ at hh
    nlinarith
  have hlarge_t : 16 * A * C ≤ δ * t := by
    have hh := (div_le_iff₀ hδ).mp ht
    change 16 * A * C ≤ t * δ at hh
    nlinarith
  have hsmall_l : 8 * C * l ≤ δ * L := by
    have hh : (8 * C / δ) * l ≤ L := by simpa only [pow_one, Real.rpow_one] using hsmall
    have hm := mul_le_mul_of_nonneg_right hh hδ.le
    have heq : (8 * C / δ) * l * δ = 8 * C * l := by field_simp
    rw [heq] at hm
    nlinarith
  exact block_exponent_budget hLpos hlpos htpos hA.le hC.le hδ.le (Nat.cast_nonneg K) hK'
    (Real.log_natCast_nonneg Y) hv hH0 hH hlarge_l hlarge_t hsmall_l

theorem eventually_blockSize_le_log {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, (blockSize x (compositeTargets c x) : ℝ) ≤ Real.log (x : ℝ) := by
  filter_upwards [eventually_composite_count_and_blockSize hc, eventually_outerScale_bounds,
    tiltScale_tendsto.eventually (eventually_ge_atTop (2 * c + 2))] with x hK hb ht
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let t := tiltScale x
  have hLpos : 0 < L := by have hh := hb.1; change 16 ≤ L at hh; linarith
  have hl1 : 1 ≤ l := hb.2.1
  have hlpos : 0 < l := by linarith
  have htpos : 0 < t := by have hh := hb.2.2.1; change 1 ≤ t at hh; linarith
  have hA : 2 * c + 2 ≤ t * l := by
    have hm := mul_le_mul_of_nonneg_left hl1 htpos.le
    change 2 * c + 2 ≤ t at ht
    nlinarith
  apply hK.2.trans
  change (2 * c + 2) * (L / t) / l ≤ L
  rw [← mul_div_assoc, div_div]
  apply (div_le_iff₀ (mul_pos htpos hlpos)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hA hLpos.le]

end Erdos4.Tilted
