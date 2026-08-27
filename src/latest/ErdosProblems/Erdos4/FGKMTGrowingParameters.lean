import ErdosProblems.Erdos4.FGKMTSieveProfileParameters
import ErdosProblems.Erdos4.FGKMTLogarithmicAbsorption
import Mathlib.Data.Nat.Log

/-! A logarithmically growing dimension at every sufficiently large endpoint. -/

namespace Erdos4.FGKMT

open Filter

noncomputable def growingIndex (x : ℕ) : ℕ :=
  Nat.log 2 ⌊Real.log (x : ℝ) ^ (1 / 100 : ℝ)⌋₊

noncomputable def growingPrecutoff (x : ℕ) : ℕ := 16 * sieveDimension (growingIndex x) ^ 4

theorem logarithmicScale_tendsto :
    Tendsto (fun x : ℕ => Real.log (x : ℝ) ^ (1 / 100 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem growingIndex_tendsto : Tendsto growingIndex atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [logarithmicScale_tendsto.eventually (eventually_ge_atTop ((2 ^ N : ℕ) : ℝ))]
    with x hx
  have hfloor : 2 ^ N ≤ ⌊Real.log (x : ℝ) ^ (1 / 100 : ℝ)⌋₊ := Nat.le_floor hx
  have hnonzero : ⌊Real.log (x : ℝ) ^ (1 / 100 : ℝ)⌋₊ ≠ 0 :=
    (lt_of_lt_of_le (by positivity : 0 < 2 ^ N) hfloor).ne'
  exact (Nat.le_log_iff_pow_le (by norm_num : 1 < (2 : ℕ)) hnonzero).mpr hfloor

theorem growingDimension_tendsto :
    Tendsto (fun x => sieveDimension (growingIndex x)) atTop atTop := by
  apply tendsto_atTop_mono _ growingIndex_tendsto
  intro x
  unfold sieveDimension
  exact (Nat.lt_two_pow_self (n := growingIndex x)).le

theorem eventually_growingDimension_bounds :
    ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) ^ (1 / 100 : ℝ) / 4 ≤ (sieveDimension (growingIndex x) : ℝ) ∧
      (sieveDimension (growingIndex x) : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 100 : ℝ) := by
  filter_upwards [logarithmicScale_tendsto.eventually (eventually_ge_atTop 2)] with x hx
  let t := Real.log (x : ℝ) ^ (1 / 100 : ℝ)
  change 2 ≤ t at hx
  have hfloor : 2 ≤ ⌊t⌋₊ := Nat.le_floor hx
  have hpos : (0 : ℝ) ≤ t := by linarith
  have hlo : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one t
    have hh' : (2 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast hfloor
    linarith
  have hpow := Nat.pow_log_le_self 2 (by omega : ⌊t⌋₊ ≠ 0)
  have hpow' := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) ⌊t⌋₊
  rw [pow_succ] at hpow'
  have hklo : (⌊t⌋₊ : ℝ) < 2 * (sieveDimension (growingIndex x) : ℝ) := by
    change (⌊t⌋₊ : ℝ) < 2 * ((2 ^ Nat.log 2 ⌊t⌋₊ : ℕ) : ℝ)
    exact_mod_cast (by simpa only [mul_comm] using hpow')
  have hkhi : (sieveDimension (growingIndex x) : ℝ) ≤ t := by
    apply (show (sieveDimension (growingIndex x) : ℝ) ≤ ⌊t⌋₊ by exact_mod_cast hpow).trans
    exact Nat.floor_le hpos
  exact ⟨by linarith, hkhi⟩

theorem eventually_growingPrecutoff_bounds :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ growingPrecutoff x ∧
      4 * (sieveDimension (growingIndex x) + 1) ^ 2 ≤ growingPrecutoff x - 1 ∧
      (growingPrecutoff x : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 4 : ℝ) := by
  have hscale : Tendsto (fun x : ℕ => Real.log (x : ℝ) ^ (21 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 21 / 100)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_growingDimension_bounds,
    growingDimension_tendsto.eventually (eventually_ge_atTop 2),
    hscale.eventually (eventually_ge_atTop 16)] with x hk hk2 hlarge
  let k := sieveDimension (growingIndex x)
  have hk' : 2 ≤ k := hk2
  have hkpow : 4 ≤ k ^ 2 := by nlinarith
  have hfour : k ^ 4 = (k ^ 2) ^ 2 := by ring
  have hD2 : 2 ≤ growingPrecutoff x := by
    change 2 ≤ 16 * k ^ 4
    rw [hfour]
    nlinarith
  have hcollision : 4 * (k + 1) ^ 2 ≤ growingPrecutoff x - 1 := by
    have hh : 4 * (k + 1) ^ 2 + 1 ≤ 16 * k ^ 4 := by
      rw [hfour]
      nlinarith
    change 4 * (k + 1) ^ 2 ≤ 16 * k ^ 4 - 1
    omega
  refine ⟨hD2, hcollision, ?_⟩
  have hL0 := Real.log_natCast_nonneg x
  have hLpos : 0 < Real.log (x : ℝ) := by
    by_contra hh
    have heq : Real.log (x : ℝ) = 0 := le_antisymm (le_of_not_gt hh) hL0
    simp [heq, Real.zero_rpow (by norm_num : (21 / 100 : ℝ) ≠ 0)] at hlarge
    norm_num at hlarge
  have hk4 : (k : ℝ) ^ 4 ≤ Real.log (x : ℝ) ^ (1 / 25 : ℝ) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hk.2 4).trans_eq
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]
    norm_num
  change ((16 * k ^ 4 : ℕ) : ℝ) ≤ _
  push_cast
  calc
    _ ≤ 16 * Real.log (x : ℝ) ^ (1 / 25 : ℝ) := mul_le_mul_of_nonneg_left hk4 (by norm_num)
    _ ≤ Real.log (x : ℝ) ^ (21 / 100 : ℝ) * Real.log (x : ℝ) ^ (1 / 25 : ℝ) :=
      mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hL0 _)
    _ = _ := by rw [← Real.rpow_add hLpos]; norm_num

end Erdos4.FGKMT
