/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.PrimeWindows

/-!
# Erdős Problem 446: the distinguished-prime candidate set

After all other selected primes and the two divisor subsets are fixed, the
close-divisor inequality restricts the distinguished prime `p` by
`|log(pu)-log v| ≤ log 2`.  Any two primes satisfying this condition differ
by at most a factor four, so the short-window estimate applies without any
rounding of real endpoints.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable def closePrimeCandidates (P : Finset ℕ) (u v : ℕ) : Finset ℕ :=
  P.filter fun p ↦
    |Real.log ((p * u : ℕ) : ℝ) - Real.log (v : ℝ)| ≤ Real.log 2

theorem mem_closePrimeCandidates {P : Finset ℕ} {u v p : ℕ} :
    p ∈ closePrimeCandidates P u v ↔
      p ∈ P ∧
        |Real.log ((p * u : ℕ) : ℝ) - Real.log (v : ℝ)| ≤ Real.log 2 := by
  simp [closePrimeCandidates]

theorem closePrimeCandidates_comparable
    {P : Finset ℕ} {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hPprime : ∀ p ∈ P, p.Prime) :
    ∀ p ∈ closePrimeCandidates P u v,
      ∀ q ∈ closePrimeCandidates P u v, p ≤ 4 * q := by
  intro p hp q hq
  have hpData := mem_closePrimeCandidates.mp hp
  have hqData := mem_closePrimeCandidates.mp hq
  have hpPrime := hPprime p hpData.1
  have hqPrime := hPprime q hqData.1
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hpAbs := (abs_le.mp hpData.2)
  have hqAbs := (abs_le.mp hqData.2)
  have hpu :
      Real.log ((p * u : ℕ) : ℝ) =
        Real.log (p : ℝ) + Real.log (u : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hpPos.ne' huR.ne']
  have hqu :
      Real.log ((q * u : ℕ) : ℝ) =
        Real.log (q : ℝ) + Real.log (u : ℝ) := by
    rw [Nat.cast_mul, Real.log_mul hqPos.ne' huR.ne']
  have hlog : Real.log (p : ℝ) ≤
      Real.log (q : ℝ) + 2 * Real.log 2 := by
    rw [hpu] at hpAbs
    rw [hqu] at hqAbs
    linarith
  have hpExp : (p : ℝ) ≤
      Real.exp (Real.log (q : ℝ) + 2 * Real.log 2) :=
    (Real.log_le_iff_le_exp hpPos).mp hlog
  have hexp :
      Real.exp (Real.log (q : ℝ) + 2 * Real.log 2) = 4 * (q : ℝ) := by
    rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
      Real.exp_add, Real.exp_add,
      Real.exp_log hqPos, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    ring
  rw [hexp] at hpExp
  exact_mod_cast hpExp

theorem closePrimeCandidates_mass_upper
    {N j : ℕ} (hN : 3 ≤ N) (hendpoint : N ≤ blockEndpoint j)
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ))
    {P : Finset ℕ} (hPblock : P ⊆ primeBlock j)
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    primeSetMass (closePrimeCandidates P u v) ≤
      7 / Real.log (blockEndpoint j : ℝ) := by
  apply comparable_primeSetMass_upper hN hendpoint hprime
  · exact (Finset.filter_subset _ _).trans hPblock
  · exact closePrimeCandidates_comparable hu hv
      (fun p hp ↦ (mem_primeBlock.mp (hPblock hp)).1)

end Erdos446
