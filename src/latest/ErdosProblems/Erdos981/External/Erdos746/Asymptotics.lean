import Mathlib

open Filter
open scoped Topology

namespace Erdos746

/-! Elementary asymptotic estimates used in the proof of Erdős Problem 746. -/

/-- The natural-number sequence `log n` tends to infinity. -/
lemma tendsto_log_nat_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The natural-number sequence `log (log n)` tends to infinity. -/
lemma tendsto_log_log_nat_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_nat_atTop

/-- `log n / n → 0`. -/
lemma tendsto_log_div_nat :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
  simpa [Function.comp_def] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop

/-- `log (log n) / log n → 0`. -/
lemma tendsto_loglog_div_log_nat :
    Tendsto (fun n : ℕ ↦
      Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (nhds 0) := by
  simpa [Function.comp_def] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_log_nat_atTop

/-- Every fixed real power of `log n` is negligible compared with every
positive real power of `n`. -/
lemma tendsto_log_rpow_div_rpow_nat (b : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦
      Real.log (n : ℝ) ^ b / (n : ℝ) ^ a) atTop (nhds 0) := by
  simpa [Function.comp_def] using
    (isLittleO_log_rpow_rpow_atTop b ha).tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop

/-- A convenient natural-power specialization of logarithmic domination. -/
lemma tendsto_log_pow_div_rpow_nat (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦
      Real.log (n : ℝ) ^ k / (n : ℝ) ^ a) atTop (nhds 0) := by
  simpa only [Real.rpow_natCast] using
    tendsto_log_rpow_div_rpow_nat (k : ℝ) ha

/-- An eventual inequality form of logarithmic domination. -/
lemma eventually_log_rpow_le_mul_rpow (b : ℝ) {a η : ℝ}
    (ha : 0 < a) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ b ≤ η * (n : ℝ) ^ a := by
  have h := (tendsto_log_rpow_div_rpow_nat b ha).eventually
    (gt_mem_nhds hη)
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hpow : 0 < (n : ℝ) ^ a :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hnpos) a
  rw [div_lt_iff₀ hpow] at hn
  exact hn.le

/-- The quotient `n / log n` tends to infinity. -/
lemma tendsto_nat_div_log_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ)) atTop atTop := by
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (Nat.cast_pos.mpr (by omega))
  have hinv := (tendsto_nhdsWithin_iff.mpr ⟨tendsto_log_div_nat, hpos⟩).inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  change (Real.log (n : ℝ) / (n : ℝ))⁻¹ =
    (n : ℝ) / Real.log (n : ℝ)
  exact inv_div _ _

/-! ### Rounding the two edge thresholds -/

/-- Subtracting two natural ceilings loses less than one compared with
subtracting the underlying nonnegative reals. -/
lemma ceil_sub_ceil_lower {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    x - y - 1 ≤ ((Nat.ceil x - Nat.ceil y : ℕ) : ℝ) := by
  have hceil : Nat.ceil y ≤ Nat.ceil x := Nat.ceil_le_ceil hxy
  rw [Nat.cast_sub hceil]
  have hx : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have hy' : (Nat.ceil y : ℝ) < y + 1 := Nat.ceil_lt_add_one hy
  linarith

/-- The exact rounding loss for the main and base edge thresholds. -/
lemma threshold_ceil_gap_lower {ε ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρε : ρ ≤ ε)
    {n : ℕ} (hn : 1 ≤ n) :
    ρ / 2 * (n : ℝ) * Real.log (n : ℝ) - 1 ≤
      ((Nat.ceil ((1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ)) -
        Nat.ceil ((1 / 2 + ρ / 2) * (n : ℝ) * Real.log (n : ℝ)) : ℕ) : ℝ) := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have hcoeff : 1 / 2 + ρ / 2 ≤ 1 / 2 + ε := by linarith
  have hy : 0 ≤ (1 / 2 + ρ / 2) * (n : ℝ) * Real.log (n : ℝ) := by
    positivity
  have hxy : (1 / 2 + ρ / 2) * (n : ℝ) * Real.log (n : ℝ) ≤
      (1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ) := by
    gcongr
  refine le_trans ?_ (ceil_sub_ceil_lower hy hxy)
  have hhalf : ρ / 2 ≤ ε - ρ / 2 := by linarith
  nlinarith

/-- The rounded gap eventually contains the sprinkling budget
`(ρ/3) n log n`. -/
lemma eventually_threshold_ceil_gap {ε ρ : ℝ} (hρ0 : 0 < ρ) (hρε : ρ ≤ ε) :
    ∀ᶠ n : ℕ in atTop,
      ρ / 3 * (n : ℝ) * Real.log (n : ℝ) ≤
        ((Nat.ceil ((1 / 2 + ε) * (n : ℝ) * Real.log (n : ℝ)) -
          Nat.ceil ((1 / 2 + ρ / 2) * (n : ℝ) * Real.log (n : ℝ)) : ℕ) : ℝ) := by
  have hprod : Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ tendsto_log_nat_atTop
  have hlarge := (hprod.const_mul_atTop (by positivity : 0 < ρ / 6)).eventually
    (eventually_ge_atTop 1)
  filter_upwards [hlarge, eventually_ge_atTop 1] with n hlarge hn
  have hround := threshold_ceil_gap_lower hρ0.le hρε hn
  nlinarith

/-! ### The geometric-series error -/

/-- The ratio used to sum the Range-I union bound. -/
noncomputable def baseRatio (A δ : ℝ) (n : ℕ) : ℝ :=
  A * Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (δ / 2)

/-- The summed Range-I error `a / (1-a)`. -/
noncomputable def geometricError (A δ : ℝ) (n : ℕ) : ℝ :=
  baseRatio A δ n / (1 - baseRatio A δ n)

lemma tendsto_baseRatio_zero (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (baseRatio A δ) atTop (nhds 0) := by
  have hA : Tendsto (fun _ : ℕ ↦ A) atTop (nhds A) := tendsto_const_nhds
  change Tendsto (fun n : ℕ ↦
    A * Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (δ / 2)) atTop (nhds 0)
  convert hA.mul (tendsto_log_pow_div_rpow_nat 2 (half_pos hδ)) using 1 <;>
    simp [mul_div_assoc]

lemma eventually_baseRatio_lt_one (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, baseRatio A δ n < 1 :=
  (tendsto_baseRatio_zero A hδ).eventually (Iio_mem_nhds zero_lt_one)

lemma tendsto_geometricError_zero (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (geometricError A δ) atTop (nhds 0) := by
  have h := tendsto_baseRatio_zero A hδ
  change Tendsto (fun n : ℕ ↦
    baseRatio A δ n / (1 - baseRatio A δ n)) atTop (nhds 0)
  have hden : Tendsto (fun n : ℕ ↦ 1 - baseRatio A δ n) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub h
  convert h.div hden (by norm_num : (1 : ℝ) - 0 ≠ 0) using 1
  · ext n
    rfl
  · norm_num

/-! ### Exponential errors -/

/-- After absorbing the leading factor `n`, an exponent of the form
`-b n / log n` still tends to minus infinity. -/
lemma tendsto_log_sub_mul_nat_div_log_atBot {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦
      Real.log (n : ℝ) - b * (n : ℝ) / Real.log (n : ℝ)) atTop atBot := by
  have hsmall := (tendsto_log_pow_div_rpow_nat 2 (a := 1) one_pos).eventually
    (gt_mem_nhds (half_pos hb))
  have hdom : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) - b * (n : ℝ) / Real.log (n : ℝ) ≤
        -(b / 2 * ((n : ℝ) / Real.log (n : ℝ))) := by
    filter_upwards [hsmall, eventually_ge_atTop 2] with n hsmall hn
    have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    rw [Real.rpow_one, div_lt_iff₀ (by positivity : (0 : ℝ) < n)] at hsmall
    have hlin : Real.log (n : ℝ) <
        b / 2 * (n : ℝ) / Real.log (n : ℝ) := by
      rw [lt_div_iff₀ hlog]
      nlinarith
    have hlin' : Real.log (n : ℝ) <
        b / 2 * ((n : ℝ) / Real.log (n : ℝ)) := by
      simpa [div_eq_mul_inv, mul_assoc] using hlin
    calc
      Real.log (n : ℝ) - b * (n : ℝ) / Real.log (n : ℝ) =
          Real.log (n : ℝ) - b * ((n : ℝ) / Real.log (n : ℝ)) := by ring
      _ ≤ -(b / 2 * ((n : ℝ) / Real.log (n : ℝ))) := by linarith
  have hneg : Tendsto (fun n : ℕ ↦
      -(b / 2 * ((n : ℝ) / Real.log (n : ℝ)))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      (tendsto_nat_div_log_atTop.const_mul_atTop (half_pos hb))
  exact tendsto_atBot_mono' atTop hdom hneg

/-- `n exp(-b n/log n) → 0`. -/
lemma tendsto_nat_mul_exp_neg_nat_div_log {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦
      (n : ℝ) * Real.exp (-b * (n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds 0) := by
  have h := Real.tendsto_exp_atBot.comp (tendsto_log_sub_mul_nat_div_log_atBot hb)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change Real.exp (Real.log (n : ℝ) -
      b * (n : ℝ) / Real.log (n : ℝ)) =
    (n : ℝ) * Real.exp (-b * (n : ℝ) / Real.log (n : ℝ))
  symm
  calc
    (n : ℝ) * Real.exp (-b * (n : ℝ) / Real.log (n : ℝ)) =
        Real.exp (Real.log (n : ℝ)) *
          Real.exp (-b * (n : ℝ) / Real.log (n : ℝ)) := by
            rw [Real.exp_log (Nat.cast_pos.mpr hn)]
    _ = Real.exp (Real.log (n : ℝ) -
          b * (n : ℝ) / Real.log (n : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            ring

/-- The exponent obtained after absorbing `n` into `n exp (-b n)` tends to
minus infinity. -/
lemma tendsto_log_sub_mul_nat_atBot {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) - b * (n : ℝ)) atTop atBot := by
  have hsmall := tendsto_log_div_nat.eventually (gt_mem_nhds (half_pos hb))
  have hdom : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) - b * (n : ℝ) ≤ -(b / 2 * (n : ℝ)) := by
    filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with n hsmall hn
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hn)] at hsmall
    nlinarith
  have hneg : Tendsto (fun n : ℕ ↦ -(b / 2 * (n : ℝ))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos hb))
  exact tendsto_atBot_mono' atTop hdom hneg

/-- `n exp(-b n) → 0`. -/
lemma tendsto_nat_mul_exp_neg_mul_nat {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.exp (-b * (n : ℝ)))
      atTop (nhds 0) := by
  have h := Real.tendsto_exp_atBot.comp (tendsto_log_sub_mul_nat_atBot hb)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change Real.exp (Real.log (n : ℝ) - b * (n : ℝ)) =
    (n : ℝ) * Real.exp (-b * (n : ℝ))
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (Nat.cast_pos.mpr hn)]
  congr 2
  ring

/-- The product `n log n` tends to infinity. -/
lemma tendsto_nat_mul_log_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ tendsto_log_nat_atTop

/-- A positive multiple of `n log n` dominates `log n + B n`. -/
lemma tendsto_log_add_linear_sub_mul_nat_log_atBot (B : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) + B * (n : ℝ) -
      c * (n : ℝ) * Real.log (n : ℝ)) atTop atBot := by
  have hnlarge := tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (4 / c))
  have hloglarge := tendsto_log_nat_atTop.eventually
    (eventually_ge_atTop (4 * |B| / c))
  have hdom : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) + B * (n : ℝ) -
          c * (n : ℝ) * Real.log (n : ℝ) ≤
        -(c / 2 * ((n : ℝ) * Real.log (n : ℝ))) := by
    filter_upwards [hnlarge, hloglarge, eventually_ge_atTop 2]
      with n hnlarge hloglarge hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlog0 : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hB : B ≤ |B| := le_abs_self B
    have hc4 : 0 < c / 4 := by positivity
    have hfirst : Real.log (n : ℝ) ≤
        c / 4 * ((n : ℝ) * Real.log (n : ℝ)) := by
      have : 1 ≤ c / 4 * (n : ℝ) := by
        calc
          1 = c / 4 * (4 / c) := by field_simp
          _ ≤ c / 4 * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hnlarge hc4.le
      nlinarith
    have hsecond : B * (n : ℝ) ≤
        c / 4 * ((n : ℝ) * Real.log (n : ℝ)) := by
      have habs : |B| ≤ c / 4 * Real.log (n : ℝ) := by
        calc
          |B| = c / 4 * (4 * |B| / c) := by field_simp
          _ ≤ c / 4 * Real.log (n : ℝ) :=
            mul_le_mul_of_nonneg_left hloglarge hc4.le
      nlinarith
    nlinarith
  have hneg : Tendsto (fun n : ℕ ↦
      -(c / 2 * ((n : ℝ) * Real.log (n : ℝ)))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      (tendsto_nat_mul_log_atTop.const_mul_atTop (half_pos hc))
  exact tendsto_atBot_mono' atTop hdom hneg

/-- `n exp(B n - c n log n) → 0` for every fixed `B` and every `c > 0`. -/
lemma tendsto_nat_mul_exp_linear_sub_mul_nat_log (B : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) *
      Real.exp (B * (n : ℝ) - c * (n : ℝ) * Real.log (n : ℝ)))
      atTop (nhds 0) := by
  have h := Real.tendsto_exp_atBot.comp
    (tendsto_log_add_linear_sub_mul_nat_log_atBot B hc)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change Real.exp (Real.log (n : ℝ) + B * (n : ℝ) -
      c * (n : ℝ) * Real.log (n : ℝ)) =
    (n : ℝ) * Real.exp
      (B * (n : ℝ) - c * (n : ℝ) * Real.log (n : ℝ))
  rw [show Real.log (n : ℝ) + B * (n : ℝ) -
      c * (n : ℝ) * Real.log (n : ℝ) =
      Real.log (n : ℝ) +
        (B * (n : ℝ) - c * (n : ℝ) * Real.log (n : ℝ)) by ring,
    Real.exp_add, Real.exp_log (Nat.cast_pos.mpr hn)]

/-- `exp(-b n log n) → 0`. -/
lemma tendsto_exp_neg_mul_nat_log {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦
      Real.exp (-b * (n : ℝ) * Real.log (n : ℝ))) atTop (nhds 0) := by
  have h := Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <|
    tendsto_nat_mul_log_atTop.const_mul_atTop hb
  apply h.congr'
  filter_upwards [] with n
  change Real.exp (-(b * ((n : ℝ) * Real.log (n : ℝ)))) =
    Real.exp (-b * (n : ℝ) * Real.log (n : ℝ))
  congr 1
  ring

/-- The precise exponential form used for the sprinkling error tends to
zero for every positive coefficient. -/
lemma tendsto_exp_nat_sub_one_sub_mul_nat_log {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ Real.exp ((n : ℝ) - 1 -
      b * (n : ℝ) * Real.log (n : ℝ))) atTop (nhds 0) := by
  have hlog := tendsto_log_nat_atTop.eventually (eventually_ge_atTop (2 / b))
  have hdom : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) - 1 - b * (n : ℝ) * Real.log (n : ℝ) ≤
        -(b / 2 * ((n : ℝ) * Real.log (n : ℝ))) := by
    filter_upwards [hlog, eventually_ge_atTop 2] with n hlog hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hlog0 : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hb2 : 0 < b / 2 := by positivity
    have hone : 1 ≤ b / 2 * Real.log (n : ℝ) := by
      calc
        1 = b / 2 * (2 / b) := by field_simp
        _ ≤ b / 2 * Real.log (n : ℝ) :=
          mul_le_mul_of_nonneg_left hlog hb2.le
    nlinarith
  have hneg : Tendsto (fun n : ℕ ↦
      -(b / 2 * ((n : ℝ) * Real.log (n : ℝ)))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      (tendsto_nat_mul_log_atTop.const_mul_atTop (half_pos hb))
  exact Real.tendsto_exp_atBot.comp (tendsto_atBot_mono' atTop hdom hneg)

end Erdos746
