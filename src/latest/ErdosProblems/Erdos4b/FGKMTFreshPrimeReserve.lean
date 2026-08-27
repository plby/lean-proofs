/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeCountBounds

/-! # A full-ray reserve of fresh primes above the initial sieve cutoff -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem exists_fresh_prime_reserve (K : ℝ) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ᶠ x : ℕ in atTop,
      K * x / Real.log (x : ℝ) ≤ (commonPinnedPrimeSet ((M * x) / 2) (M * x)).card ∧
      (∀ p ∈ commonPinnedPrimeSet ((M * x) / 2) (M * x), x < p) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (max (2 : ℝ) (16 * K))
  have hM2R : (2 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hM2 : 2 ≤ M := by exact_mod_cast hM2R.le
  have hMK : 16 * K ≤ (M : ℝ) := ((le_max_right _ _).trans_lt hM).le
  have hMpos : 0 < M := by omega
  have hMposR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have htop : Tendsto (fun x : ℕ => M * x) atTop atTop :=
    tendsto_atTop_mono (fun x => Nat.le_mul_of_pos_left x hMpos) tendsto_id
  refine ⟨M, hM2, ?_⟩
  filter_upwards [htop.eventually eventually_commonPinnedPrimeSet_half_card_lower,
    eventually_ge_atTop M, eventually_ge_atTop (2 : ℕ)] with x hcount hxM hx
  have hx1 : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hxpos : (0 : ℝ) < x := by linarith
  have hL : 0 < Real.log (x : ℝ) := Real.log_pos hx1
  have hprod1 : (1 : ℝ) < (M * x : ℕ) := by
    exact_mod_cast (show 1 < M * x by nlinarith)
  have hprodLog : 0 < Real.log (M * x : ℕ) := Real.log_pos hprod1
  have hprodLog' : 0 < Real.log ((M : ℝ) * x) := by
    simpa only [Nat.cast_mul] using hprodLog
  have hlog : Real.log (M * x : ℕ) ≤ 2 * Real.log (x : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hMposR.ne' hxpos.ne']
    have hh := Real.log_le_log hMposR (show (M : ℝ) ≤ x by exact_mod_cast hxM)
    linarith
  have hhalf : x ≤ M * x / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
    nlinarith
  refine ⟨?_, ?_⟩
  · calc
      K * x / Real.log (x : ℝ) ≤ ((M : ℝ) * x) / (16 * Real.log (x : ℝ)) := by
        apply (div_le_div_iff₀ hL (by positivity : 0 < 16 * Real.log (x : ℝ))).mpr
        nlinarith [mul_le_mul_of_nonneg_right hMK (mul_nonneg hxpos.le hL.le)]
      _ ≤ ((M * x : ℕ) : ℝ) / (8 * Real.log (M * x : ℕ)) := by
        rw [Nat.cast_mul]
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (by norm_num : (0 : ℝ) < 8) hprodLog')
        have hh : Real.log ((M : ℝ) * x) ≤ 2 * Real.log (x : ℝ) := by
          simpa only [Nat.cast_mul] using hlog
        linarith
      _ ≤ _ := hcount
  · intro p hp
    exact hhalf.trans_lt (mem_commonPinnedPrimeSet.mp hp).1

end

end Erdos4b.FGKMT
