/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.Parameters

/-!
# Large-input logarithmic absorption

This file packages the elementary asymptotic estimate needed to absorb a
fixed polynomial in the dyadic logarithm into an arbitrary positive power
of the input cardinality.
-/

namespace Erdos186.CFP

open Filter Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Above two, the successor of the dyadic logarithm is bounded by four
times the real logarithm. -/
theorem natLog_two_add_one_le_four_mul_log {m : ℕ} (hm : 2 ≤ m) :
    ((Nat.log 2 m + 1 : ℕ) : ℝ) ≤ 4 * Real.log (m : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  have hpowNat : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hm0
  have hpowReal : ((2 ^ Nat.log 2 m : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hpowNat
  have hlogPow := Real.log_le_log
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 m)
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpowReal)
  have hlogMul :
      (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log (m : ℝ) := by
    simpa only [Real.log_pow] using hlogPow
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogMono : Real.log 2 ≤ Real.log (m : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hm)
  push_cast
  nlinarith

/-- Every fixed natural polynomial in `Nat.log 2 m + 1` is eventually
bounded by every prescribed positive real power of `m`. -/
theorem exists_cutoff_logPolynomial_le_rpow
    (eta : ℝ) (heta : 0 < eta) (K p : ℕ) :
    ∃ cutoff : ℕ, 2 ≤ cutoff ∧
      ∀ {m : ℕ}, cutoff ≤ m →
        ((K * (Nat.log 2 m + 1) ^ p : ℕ) : ℝ) ≤
          Real.rpow (m : ℝ) eta := by
  let C : ℝ := (K : ℝ) * 4 ^ p
  have hsmall :
      (fun n : ℕ ↦ C * Real.log (n : ℝ) ^ (p : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ eta) :=
    (log_rpow_isLittleO_nat_rpow (p : ℝ) heta).const_mul_left C
  have hev : ∀ᶠ n : ℕ in atTop,
      C * Real.log (n : ℝ) ^ (p : ℝ) ≤ (n : ℝ) ^ eta := by
    filter_upwards [hsmall.eventuallyLE,
      (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
      tendsto_natCast_atTop_atTop.eventually_gt_atTop (0 : ℝ)]
        with n hn hlog hnpos
    have hC : 0 ≤ C := by simp [C]
    have hleft : 0 ≤ C * Real.log (n : ℝ) ^ (p : ℝ) :=
      mul_nonneg hC (Real.rpow_nonneg hlog.le _)
    have hright : 0 ≤ (n : ℝ) ^ eta := Real.rpow_nonneg hnpos.le _
    simpa only [Real.norm_of_nonneg hleft,
      Real.norm_of_nonneg hright] using hn
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 hev
  refine ⟨max 2 cutoff, le_max_left _ _, ?_⟩
  intro m hm
  have hm2 : 2 ≤ m := (le_max_left 2 cutoff).trans hm
  have hmc : cutoff ≤ m := (le_max_right 2 cutoff).trans hm
  have hlog := natLog_two_add_one_le_four_mul_log hm2
  have hlogNonneg : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hpow : ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ p ≤
      (4 * Real.log (m : ℝ)) ^ p := by
    exact pow_le_pow_left₀ (by positivity) hlog p
  have hK : (0 : ℝ) ≤ (K : ℝ) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hpow hK
  calc
    ((K * (Nat.log 2 m + 1) ^ p : ℕ) : ℝ) =
        (K : ℝ) * ((Nat.log 2 m + 1 : ℕ) : ℝ) ^ p := by
          norm_num
    _ ≤ (K : ℝ) * (4 * Real.log (m : ℝ)) ^ p := hbound
    _ = C * Real.log (m : ℝ) ^ (p : ℝ) := by
      simp only [C, mul_pow, Real.rpow_natCast]
      ring
    _ ≤ Real.rpow (m : ℝ) eta := hcutoff m hmc

end

end Erdos186.CFP

#print axioms Erdos186.CFP.exists_cutoff_logPolynomial_le_rpow
