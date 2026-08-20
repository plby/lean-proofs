/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.IsolatedDivisors

/-!
# Erdős Problem 446: logarithmic isolation implies dyadic ratio isolation

Ford's moment estimate uses isolation in the symmetric logarithmic window
`|log d - log e| ≤ log 2`, whereas the exact-multiplicity construction is
most conveniently stated using the cross-multiplied target-interval
inequalities.  This file supplies the elementary conversion between the two
forms.  It is the pointwise bridge from `sigmaIsolatedCount` to the prime
extension producing exactly `r` divisors in `(y,2y]`.
-/

namespace Erdos446

open Finset Real

/-- Two positive integers whose ratio lies strictly between `1/2` and `2`
are neighbours in the logarithmic window of radius `log 2`. -/
theorem abs_log_sub_log_le_log_two_of_lt_two_mul
    {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hed : e < 2 * d) (hde : d < 2 * e) :
    |Real.log (d : ℝ) - Real.log (e : ℝ)| ≤ Real.log 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have htwoR : (0 : ℝ) < 2 := by norm_num
  have hedR : (e : ℝ) < 2 * (d : ℝ) := by exact_mod_cast hed
  have hdeR : (d : ℝ) < 2 * (e : ℝ) := by exact_mod_cast hde
  have hlogE : Real.log (e : ℝ) < Real.log (2 * (d : ℝ)) :=
    Real.strictMonoOn_log heR (mul_pos htwoR hdR) hedR
  have hlogD : Real.log (d : ℝ) < Real.log (2 * (e : ℝ)) :=
    Real.strictMonoOn_log hdR (mul_pos htwoR heR) hdeR
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hdR.ne'] at hlogE
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) heR.ne'] at hlogD
  rw [abs_le]
  constructor <;> linarith

/-- A divisor isolated in Ford's logarithmic sense is the unique divisor
within a factor two of itself. -/
theorem eq_of_mem_divisors_of_lt_two_mul_of_sigmaIsolated_log_two
    {a d e : ℕ}
    (hdIso : d ∈ sigmaIsolatedDivisors a (Real.log 2))
    (heDiv : e ∈ a.divisors)
    (hed : e < 2 * d) (hde : d < 2 * e) : e = d := by
  have hdData := mem_sigmaIsolatedDivisors.mp hdIso
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hdData.1
  have hePos : 0 < e := Nat.pos_of_mem_divisors heDiv
  have heNeighbor : e ∈ sigmaNeighborDivisors a d (Real.log 2) :=
    mem_sigmaNeighborDivisors.mpr
      ⟨heDiv, abs_log_sub_log_le_log_two_of_lt_two_mul hdPos hePos hed hde⟩
  rw [hdData.2] at heNeighbor
  simpa using heNeighbor

/-- Cross-multiplied dyadic interval inequalities imply factor-two
closeness.  Hence a `log 2`-isolated divisor is ratio-isolated for every
positive dyadic base point `y`.

The conclusion is deliberately stated without referring to a later
construction-specific predicate, so the lemma can be imported without an
acyclicity issue. -/
theorem dyadic_ratio_eq_of_sigmaIsolated_log_two
    {a d y : ℕ} (hy : 0 < y)
    (hdIso : d ∈ sigmaIsolatedDivisors a (Real.log 2)) :
    ∀ e ∈ a.divisors,
      y * e < (2 * y) * d → y * d < (2 * y) * e → e = d := by
  intro e heDiv hyed hyde
  have hed : e < 2 * d := by
    apply (Nat.mul_lt_mul_left hy).mp
    simpa [mul_assoc, mul_left_comm, mul_comm] using hyed
  have hde : d < 2 * e := by
    apply (Nat.mul_lt_mul_left hy).mp
    simpa [mul_assoc, mul_left_comm, mul_comm] using hyde
  exact eq_of_mem_divisors_of_lt_two_mul_of_sigmaIsolated_log_two
    hdIso heDiv hed hde

end Erdos446
