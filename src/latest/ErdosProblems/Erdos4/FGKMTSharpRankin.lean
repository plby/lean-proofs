import ErdosProblems.Erdos4.SmoothRankin
import UnitFractions.ForMathlib.BasicEstimates

/-! A Rankin Euler bound with an absolute leading logarithmic coefficient. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter Classical

theorem prime_summatory_nat_eq (f : ℕ → ℝ) (n : ℕ) :
    prime_summatory f 1 (n : ℝ) = ∑ p ∈ n.primesLE, f p := by
  have hset : (Finset.Icc 1 n).filter Nat.Prime = n.primesLE := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hpn⟩, hp⟩
      exact ⟨hpn, hp⟩
    · rintro ⟨hpn, hp⟩
      exact ⟨⟨hp.one_le, hpn⟩, hp⟩
  simp only [prime_summatory, Nat.floor_natCast, hset]

theorem eventually_prime_harmonic_bounds :
    ∀ᶠ z : ℕ in atTop,
      (∑ p ∈ z.primesLE, (p : ℝ)⁻¹) ≤ 2 * Real.log (Real.log (z : ℝ)) ∧
      (∑ p ∈ z.primesLE, Real.log (p : ℝ) / p) ≤ 2 * Real.log (z : ℝ) := by
  obtain ⟨C₁, hC₁, h₁⟩ := log_reciprocal.exists_pos
  obtain ⟨C₂, hC₂, h₂⟩ := prime_reciprocal.exists_pos
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually h₁.bound,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h₂.bound,
    hlog.eventually (eventually_ge_atTop (max 1 C₁)),
    hloglog.eventually (eventually_ge_atTop (C₂ + |meissel_mertens|))]
    with z h₁ h₂ hL hl
  change max 1 C₁ ≤ Real.log (z : ℝ) at hL
  change C₂ + |meissel_mertens| ≤ Real.log (Real.log (z : ℝ)) at hl
  have hL1 : 1 ≤ Real.log (z : ℝ) := (le_max_left _ _).trans hL
  have hLC : C₁ ≤ Real.log (z : ℝ) := (le_max_right _ _).trans hL
  have hLpos : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (by norm_num) hL1
  simp only [Real.norm_eq_abs, abs_one, mul_one, prime_summatory_nat_eq] at h₁ h₂
  have hinv : |(Real.log (z : ℝ))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr hLpos.le)]
    exact (inv_le_one₀ hLpos).mpr hL1
  have hrec := h₂.trans (mul_le_mul_of_nonneg_left hinv hC₂.le)
  have hrec' := (le_abs_self _).trans hrec
  have hlog' := (le_abs_self _).trans h₁
  constructor
  · have hm := le_abs_self meissel_mertens
    linarith
  · linarith

theorem rpow_le_log_chord {t z δ : ℝ} (ht : 1 ≤ t) (htz : t ≤ z) (hz : 1 < z) :
    t ^ δ ≤ 1 + ((z ^ δ - 1) / Real.log z) * Real.log t := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hzpos : 0 < z := zero_lt_one.trans hz
  have hlogz : 0 < Real.log z := Real.log_pos hz
  let a := Real.log t / Real.log z
  have ha0 : 0 ≤ a := div_nonneg (Real.log_nonneg ht) hlogz.le
  have ha1 : a ≤ 1 := (div_le_one hlogz).mpr (Real.log_le_log htpos htz)
  have hh := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (δ * Real.log z)) (sub_nonneg.mpr ha1) ha0
    (show (1 - a) + a = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hh
  have harg : a * (δ * Real.log z) = Real.log t * δ := by
    dsimp only [a]
    field_simp
  rw [harg, ← Real.rpow_def_of_pos htpos] at hh
  have heq : Real.exp (δ * Real.log z) = z ^ δ := by
    rw [Real.rpow_def_of_pos hzpos]
    congr 1
    ring
  rw [heq] at hh
  exact hh.trans_eq (by dsimp only [a]; ring)

theorem primeRankinSum_le_chord {z : ℕ} (hz : 2 ≤ z) (δ : ℝ) :
    SmoothRankin.primeRankinSum δ z ≤
      (∑ p ∈ z.primesLE, (p : ℝ)⁻¹) +
        (((z : ℝ) ^ δ - 1) / Real.log (z : ℝ)) *
          (∑ p ∈ z.primesLE, Real.log (p : ℝ) / p) := by
  let a := ((z : ℝ) ^ δ - 1) / Real.log (z : ℝ)
  have hzR : (1 : ℝ) < z := by exact_mod_cast hz
  calc
    _ ≤ ∑ p ∈ z.primesLE, ((p : ℝ)⁻¹ + a * (Real.log (p : ℝ) / p)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hprime := (Nat.mem_primesLE.mp hp).2
      have hpz : (p : ℝ) ≤ z := by exact_mod_cast (Nat.mem_primesLE.mp hp).1
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_le
      have hh := mul_le_mul_of_nonneg_right (rpow_le_log_chord hp1 hpz hzR (δ := δ))
        (inv_nonneg.mpr (Nat.cast_nonneg p))
      rw [SmoothRankin.rankinWeight_eq_rpow_mul_inv hprime.pos]
      exact hh.trans_eq (by dsimp only [a]; ring)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem rankinEulerConstant_le_four : Erdos469.rankinEulerConstant ≤ 4 := by
  let t := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have ht0 : 0 ≤ t := Real.rpow_nonneg (by norm_num) _
  have htsq : t ^ 2 = 1 / 2 := by
    dsimp only [t]
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have ht : t ≤ 3 / 4 := by nlinarith
  have hden : 0 < 1 - t := by linarith
  change (1 - t)⁻¹ ≤ 4
  have hh : 1 / (1 - t) ≤ 4 := (div_le_iff₀ hden).mpr (by linarith)
  simpa only [one_div] using hh

theorem eventually_sharp_rankin_euler :
    ∀ᶠ z : ℕ in atTop, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      Erdos469.smoothRankinEulerProduct δ z ≤
        Real.exp (8 * Real.log (Real.log (z : ℝ)) + 8 * (z : ℝ) ^ δ) := by
  filter_upwards [eventually_prime_harmonic_bounds, eventually_ge_atTop 2]
    with z hsum hz
  intro δ hδ hδhalf
  have hzpos : (0 : ℝ) < z := by exact_mod_cast (show 0 < z by omega)
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast hz)
  have hpow : 1 ≤ (z : ℝ) ^ δ := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ z by omega)) hδ.le
  have hcoef : 0 ≤ ((z : ℝ) ^ δ - 1) / Real.log (z : ℝ) := by positivity
  have hprime : SmoothRankin.primeRankinSum δ z ≤
      2 * Real.log (Real.log (z : ℝ)) + 2 * (z : ℝ) ^ δ := by
    calc
      _ ≤ (∑ p ∈ z.primesLE, (p : ℝ)⁻¹) +
          (((z : ℝ) ^ δ - 1) / Real.log (z : ℝ)) *
            (∑ p ∈ z.primesLE, Real.log (p : ℝ) / p) := primeRankinSum_le_chord hz δ
      _ ≤ 2 * Real.log (Real.log (z : ℝ)) +
          (((z : ℝ) ^ δ - 1) / Real.log (z : ℝ)) * (2 * Real.log (z : ℝ)) := by
        exact add_le_add hsum.1 (mul_le_mul_of_nonneg_left hsum.2 hcoef)
      _ = 2 * Real.log (Real.log (z : ℝ)) + 2 * ((z : ℝ) ^ δ - 1) := by field_simp
      _ ≤ _ := by linarith
  have hnonneg : 0 ≤ SmoothRankin.primeRankinSum δ z :=
    Finset.sum_nonneg (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
  apply (SmoothRankin.smoothRankinEulerProduct_le_exp_primeRankinSum hδ.le hδhalf).trans
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ 4 * SmoothRankin.primeRankinSum δ z :=
      mul_le_mul_of_nonneg_right rankinEulerConstant_le_four hnonneg
    _ ≤ 4 * (2 * Real.log (Real.log (z : ℝ)) + 2 * (z : ℝ) ^ δ) :=
      mul_le_mul_of_nonneg_left hprime (by norm_num)
    _ = _ := by ring

end Erdos4.FGKMT
