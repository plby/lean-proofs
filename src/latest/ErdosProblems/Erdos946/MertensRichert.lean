/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SieveWindow
import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

/-! # The prime average of the Richert weight -/

open scoped BigOperators Asymptotics
open Filter

namespace Erdos946.MertensRichert

open Erdos851

noncomputable section

def primeRichertMass (z Y : ℕ) : ℝ :=
  ∑ p ∈ sievePrimes z Y, (1 - Real.log (p : ℝ) / Real.log (Y : ℝ)) / p

theorem sum_sievePrimes_eq_sub (f : ℕ → ℝ) {z Y : ℕ} (hzY : z ≤ Y) :
    (∑ p ∈ sievePrimes z Y, f p) =
      (∑ p ∈ sievePrimes 0 Y, f p) - ∑ p ∈ sievePrimes 0 z, f p := by
  have hsets : sievePrimes z Y = sievePrimes 0 Y \ sievePrimes 0 z := by
    ext p
    simp only [mem_sievePrimes, Finset.mem_sdiff]
    constructor
    · rintro ⟨hzp, hpY, hp⟩
      exact ⟨⟨hp.pos, hpY, hp⟩, fun h ↦ (not_le_of_gt hzp) h.2.1⟩
    · rintro ⟨⟨hp0, hpY, hp⟩, hnot⟩
      refine ⟨?_, hpY, hp⟩
      by_contra hzp
      exact hnot ⟨hp0, Nat.le_of_not_gt hzp, hp⟩
  have hsub : sievePrimes 0 z ⊆ sievePrimes 0 Y := by
    intro p hp
    have h := mem_sievePrimes.mp hp
    exact mem_sievePrimes.mpr ⟨h.1, h.2.1.trans hzY, h.2.2⟩
  rw [hsets, Finset.sum_sdiff_eq_sub hsub]

theorem primeRichertMass_eq_mertens {z Y : ℕ} (hzY : z ≤ Y) :
    primeRichertMass z Y =
      (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log (z : ℝ))) -
        (Real.log (Y : ℝ) - Real.log (z : ℝ)) / Real.log (Y : ℝ) +
      (Mertens.E₂p (Y : ℝ) - Mertens.E₂p (z : ℝ)) -
        (Mertens.E₁p (Y : ℝ) - Mertens.E₁p (z : ℝ)) / Real.log (Y : ℝ) := by
  have hfirst (n : ℕ) :
      (∑ p ∈ sievePrimes 0 n, (1 : ℝ) / p) =
        Real.log (Real.log (n : ℝ)) + Mertens.M + Mertens.E₂p (n : ℝ) := by
    simpa [sievePrimes] using Mertens.sum_prime_div_eq (n : ℝ)
  have hsecond (n : ℕ) :
      (∑ p ∈ sievePrimes 0 n, Real.log (p : ℝ) / p) =
        Real.log (n : ℝ) + Mertens.E₁p (n : ℝ) := by
    simpa [sievePrimes] using Mertens.sum_log_prime_div_eq (n : ℝ)
  have hsplit : primeRichertMass z Y =
      (∑ p ∈ sievePrimes z Y, (1 : ℝ) / p) -
        (∑ p ∈ sievePrimes z Y, Real.log (p : ℝ) / p) / Real.log (Y : ℝ) := by
    unfold primeRichertMass
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit, sum_sievePrimes_eq_sub _ hzY, sum_sievePrimes_eq_sub _ hzY,
    hfirst, hfirst, hsecond, hsecond]
  ring

theorem tendsto_mertens_second_error :
    Tendsto Mertens.E₂p atTop (nhds 0) :=
  (Asymptotics.isLittleO_one_iff ℝ).mp Mertens.E₂p.bound'

theorem tendsto_mertens_first_error_div_log :
    Tendsto (fun x : ℝ ↦ Mertens.E₁p x / Real.log x) atTop (nhds 0) := by
  have hone : (fun _ : ℝ ↦ (1 : ℝ)) =o[atTop] Real.log := by
    rw [Asymptotics.isLittleO_one_left_iff]
    simpa only [Real.norm_eq_abs, Function.comp_def] using
      (tendsto_abs_atTop_atTop.comp Real.tendsto_log_atTop)
  exact (Mertens.sum_log_prime_div_eq_log'.trans_isLittleO hone).tendsto_div_nhds_zero

theorem primeRichertMass_pow_eq {N R : ℕ} (hN : 2 ≤ N) (hR : 1 ≤ R) :
    primeRichertMass N (N ^ R) =
      (Real.log (R : ℝ) - 1 + 1 / R) +
        (Mertens.E₂p (N ^ R : ℕ) - Mertens.E₂p (N : ℝ)) -
        (Mertens.E₁p (N ^ R : ℕ) / Real.log (N ^ R : ℕ) -
          (Mertens.E₁p (N : ℝ) / Real.log (N : ℝ)) / R) := by
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hRR : (R : ℝ) ≠ 0 := by exact_mod_cast (show R ≠ 0 by omega)
  have hlogpow : Real.log (N ^ R : ℕ) = (R : ℝ) * Real.log (N : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  have hloglog : Real.log (Real.log (N ^ R : ℕ)) =
      Real.log (R : ℝ) + Real.log (Real.log (N : ℝ)) := by
    rw [hlogpow, Real.log_mul hRR hlogN]
  rw [primeRichertMass_eq_mertens (le_self_pow (by omega : 1 ≤ N) (by omega)),
    hloglog, hlogpow]
  field_simp [hRR, hlogN]
  <;> ring

/-- The weighted prime mass between `N` and a fixed positive natural power
of `N` has the exact limit required by the Richert average. -/
theorem tendsto_primeRichertMass_pow {R : ℕ} (hR : 1 ≤ R) :
    Tendsto (fun N : ℕ ↦ primeRichertMass N (N ^ R)) atTop
      (nhds (Real.log (R : ℝ) - 1 + 1 / R)) := by
  have hnat : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun N : ℕ ↦ ((N ^ R : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_pow, Function.comp_def] using
      (tendsto_pow_atTop (show R ≠ 0 by omega)).comp hnat
  have he2 := (tendsto_mertens_second_error.comp hpow).sub
    (tendsto_mertens_second_error.comp hnat)
  have he1 := (tendsto_mertens_first_error_div_log.comp hpow).sub
    ((tendsto_mertens_first_error_div_log.comp hnat).div_const (R : ℝ))
  have hc : Tendsto (fun _ : ℕ ↦ Real.log (R : ℝ) - 1 + 1 / R) atTop
      (nhds (Real.log (R : ℝ) - 1 + 1 / R)) := tendsto_const_nhds
  have h := (hc.add he2).sub he1
  simp only [Function.comp_def, sub_zero, zero_div, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (primeRichertMass_pow_eq hN hR).symm

theorem eventually_primeRichertMass_thousand_lt :
    ∀ᶠ N : ℕ in atTop, primeRichertMass N (N ^ 1000) < 601 / 100 := by
  apply (tendsto_primeRichertMass_pow (R := 1000) (by norm_num)).eventually_lt_const
  have h := SieveWindow.log_thousand_lt_seven
  norm_num
  linarith

end

end Erdos946.MertensRichert

#print axioms Erdos946.MertensRichert.tendsto_primeRichertMass_pow
