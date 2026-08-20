/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SieveDensity
import UnitFractions.ForMathlib.BasicEstimates

/-!
# Erdős Problem 446: the small-prime Euler factor
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem smallPrimeEulerDensity_eq_partialEulerProduct_inv (N : ℕ) :
    smallPrimeEulerDensity N = (partial_euler_product N)⁻¹ := by
  rw [smallPrimeEulerDensity, partial_euler_product]
  simp only [Finset.prod_inv_distrib, inv_inv]
  apply Finset.prod_bij (fun p _ ↦ p.1)
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(primeIndex_prime p).one_le,
      (Finset.mem_Icc.mp (Finset.mem_filter.mp p.2).1).2⟩,
      primeIndex_prime p⟩
  · intro p hp q hq hpq
    exact Subtype.ext hpq
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    let pN : PrimeIndex N := ⟨p, by
      rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hp'.2.two_le, (Finset.mem_Icc.mp hp'.1).2⟩, hp'.2⟩⟩
    exact ⟨pN, Finset.mem_univ pN, rfl⟩
  · intro p hp
    simp [one_div]

/-- A positive constant for the weak Mertens upper bound.  This is kept
inside the Problem 446 development so that the proof does not depend on the
unrelated Problem 448 formalization. -/
noncomputable def cleanMertensConstant446 : ℝ :=
  Classical.choose weak_mertens_third_upper_all

lemma cleanMertensConstant446_pos : 0 < cleanMertensConstant446 :=
  (Classical.choose_spec weak_mertens_third_upper_all).1

/-- The weak Mertens estimate in the form needed for the small-prime sieve
density. -/
lemma partialEulerProduct_le_cleanMertens446 (N : ℕ) (hN : 2 ≤ N) :
    partial_euler_product N ≤ cleanMertensConstant446 * Real.log (N : ℝ) := by
  have h := (Classical.choose_spec weak_mertens_third_upper_all).2
    (N : ℝ) (by exact_mod_cast hN)
  have hprod : 0 ≤ partial_euler_product N :=
    zero_le_one.trans partial_euler_trivial_lower_bound
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  change partial_euler_product N ≤
    Classical.choose weak_mertens_third_upper_all * Real.log (N : ℝ)
  simpa [Real.norm_of_nonneg hprod, Real.norm_of_nonneg hlog] using h

/-- Weak Mertens lower bound in the exact form used by the construction. -/
theorem smallPrimeEulerDensity_lower (N : ℕ) (hN : 2 ≤ N) :
    1 / (cleanMertensConstant446 * Real.log (N : ℝ)) ≤
      smallPrimeEulerDensity N := by
  rw [smallPrimeEulerDensity_eq_partialEulerProduct_inv, one_div]
  have hprod := partialEulerProduct_le_cleanMertens446 N hN
  have hprodPos : 0 < partial_euler_product N :=
    zero_lt_one.trans_le partial_euler_trivial_lower_bound
  exact inv_anti₀ hprodPos hprod

end Erdos446
