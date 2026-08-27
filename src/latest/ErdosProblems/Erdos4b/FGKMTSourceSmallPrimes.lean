/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTIntervalDensity

/-! # The literal source small-prime interval and its eventual ranges -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def sourceSmallPrimeLower (x : ℕ) : ℝ := Real.log (x : ℝ) ^ 20

def sourceSmallPrimeUpper (a : ℝ) (x : ℕ) : ℝ :=
  Real.exp (Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
    (a * Real.log (Real.log (x : ℝ))))

def sourceSmallPrimes (a : ℝ) (x : ℕ) : Finset ℕ :=
  commonPinnedPrimeSet ⌊sourceSmallPrimeLower x⌋₊ ⌊sourceSmallPrimeUpper a x⌋₊

theorem log_sourceSmallPrimeLower (x : ℕ) :
    Real.log (sourceSmallPrimeLower x) = 20 * Real.log (Real.log (x : ℝ)) := by
  simp only [sourceSmallPrimeLower, Real.log_pow, Nat.cast_ofNat]

theorem log_sourceSmallPrimeUpper (a : ℝ) (x : ℕ) :
    Real.log (sourceSmallPrimeUpper a x) =
      Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) /
        (a * Real.log (Real.log (x : ℝ))) := Real.log_exp _

theorem mem_sourceSmallPrimes {a : ℝ} {x p : ℕ} :
    p ∈ sourceSmallPrimes a x ↔
      sourceSmallPrimeLower x < (p : ℝ) ∧ (p : ℝ) ≤ sourceSmallPrimeUpper a x ∧ p.Prime := by
  have hv : 0 ≤ sourceSmallPrimeLower x := pow_nonneg (Real.log_natCast_nonneg x) 20
  have hz : 0 ≤ sourceSmallPrimeUpper a x := (Real.exp_pos _).le
  rw [sourceSmallPrimes, mem_commonPinnedPrimeSet, Nat.floor_lt hv, Nat.le_floor_iff hz]

theorem sourceSmallPrimes_prime (a : ℝ) (x p : ℕ) (hp : p ∈ sourceSmallPrimes a x) :
    p.Prime := (mem_sourceSmallPrimes.mp hp).2.2

theorem sourceSmallPrimes_rough (a : ℝ) (x p : ℕ) (hp : p ∈ sourceSmallPrimes a x) :
    Real.log (x : ℝ) ^ 20 < (p : ℝ) := (mem_sourceSmallPrimes.mp hp).1

theorem eventually_sourceSmallPrime_ranges {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ sourceSmallPrimeLower x ∧
      sourceSmallPrimeLower x ≤ sourceSmallPrimeUpper a x ∧
      sourceSmallPrimeUpper a x < (x : ℝ) / 2 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hlogloglog := Real.tendsto_log_atTop.comp hloglog
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto hlog).def
      (by positivity : (0 : ℝ) < 1 / (20 * a))
  have htiny := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).comp_tendsto
    hloglog).def (by positivity : (0 : ℝ) < a / 2)
  filter_upwards [hsmall, htiny,
    hlog.eventually (eventually_ge_atTop (max 2 (2 * Real.log 2 + 1))),
    hloglog.eventually (eventually_ge_atTop (1 : ℝ)),
    hlogloglog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hs ht hL hl htt hx
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let t := Real.log l
  change max 2 (2 * Real.log 2 + 1) ≤ L at hL
  change 1 ≤ l at hl
  change 1 ≤ t at htt
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLbig : 2 * Real.log 2 + 1 ≤ L := (le_max_right _ _).trans hL
  have hLpos : 0 < L := by linarith
  have hlpos : 0 < l := by linarith
  have htpos : 0 < t := by linarith
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  change ‖l ^ (2 : ℝ)‖ ≤ (1 / (20 * a)) * ‖L ^ (1 : ℝ)‖ at hs
  change ‖t‖ ≤ (a / 2) * ‖l ^ (1 : ℝ)‖ at ht
  have hs' : l ^ 2 ≤ L / (20 * a) := by
    simpa only [Function.comp_apply, Real.rpow_two, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg l), abs_of_nonneg hLpos.le, one_div, div_eq_mul_inv,
      mul_comm, one_mul] using hs
  have hbudget : 20 * a * l ^ 2 ≤ L := by
    have h := (le_div_iff₀ (by positivity : 0 < 20 * a)).mp hs'
    nlinarith
  have ht' : t ≤ (a / 2) * l := by
    simpa only [Function.comp_apply, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg htpos.le, abs_of_nonneg hlpos.le] using ht
  have hlow : 20 * l ≤ L * t / (a * l) := by
    apply (le_div_iff₀ (mul_pos ha hlpos)).mpr
    have hLt : L ≤ L * t := le_mul_of_one_le_right hLpos.le htt
    nlinarith
  have hupp : L * t / (a * l) ≤ L / 2 := by
    apply (div_le_iff₀ (mul_pos ha hlpos)).mpr
    have h := mul_le_mul_of_nonneg_left ht' hLpos.le
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · change 2 ≤ L ^ 20
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL2 20
    norm_num at h
    linarith
  · apply (Real.log_le_iff_le_exp (pow_pos hLpos 20)).mp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hlow
  · calc
      sourceSmallPrimeUpper a x = Real.exp (L * t / (a * l)) := rfl
      _ ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr hupp
      _ < Real.exp (L - Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = (x : ℝ) / 2 := by
        rw [Real.exp_sub, Real.exp_log hxpos, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem eventually_sourceSmallPrimes_le {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop, ∀ p ∈ sourceSmallPrimes a x, p ≤ x := by
  filter_upwards [eventually_sourceSmallPrime_ranges ha] with x hx
  intro p hp
  have h := (mem_sourceSmallPrimes.mp hp).2.1.trans_lt hx.2.2
  have hpR : (p : ℝ) ≤ x := by nlinarith [show (0 : ℝ) ≤ x from Nat.cast_nonneg x]
  exact_mod_cast hpR

end

end Erdos4b.FGKMT
