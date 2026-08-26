/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierAffineEdges

/-!
# Logarithmic size of the concrete affine exceptional integer

The tuple varies with the pre-sieve cutoff. Its shift sum is bounded
explicitly, so the exceptional integer still has a fixed logarithmic
envelope once the cofactor, auxiliary prime, and primorial do.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem sum_preSievedShifts_le (K w : ℕ) :
    (∑ h ∈ preSievedShifts K w, h) ≤ primorial w * K ^ 2 := by
  have hle : ∀ h ∈ preSievedShifts K w, h ≤ primorial w * K := by
    intro h hh
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
    exact Nat.mul_le_mul_left _ (Finset.mem_range.mp hi).le
  calc
    _ ≤ ∑ h ∈ preSievedShifts K w, primorial w * K := Finset.sum_le_sum hle
    _ = K * (primorial w * K) := by
      simp only [Finset.sum_const, nsmul_eq_mul, card_preSievedShifts]
      norm_cast
    _ = _ := by ring

theorem crossAffineEnvelope_preSieved_le (K w : ℕ) {m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) :
    crossAffineEnvelope (preSievedShifts K w) m q ≤ m * q * primorial w * (K ^ 2 + 1) := by
  have hP := primorial_pos w
  have hmqP : 1 ≤ m * q * primorial w := Nat.succ_le_iff.mpr (Nat.mul_pos (Nat.mul_pos hm hq) hP)
  calc
    _ = m * q * (∑ h ∈ preSievedShifts K w, h) + 1 := rfl
    _ ≤ m * q * (primorial w * K ^ 2) + 1 := by
      gcongr
      exact sum_preSievedShifts_le K w
    _ ≤ m * q * (primorial w * K ^ 2) + m * q * primorial w :=
      Nat.add_le_add_left hmqP _
    _ = _ := by ring

theorem log_crossAffineEnvelope_preSieved_le (K w : ℕ) {m q : ℕ}
    (hm : 0 < m) (hq : 0 < q) :
    Real.log (crossAffineEnvelope (preSievedShifts K w) m q) ≤
      Real.log m + Real.log q + Real.log (primorial w) + Real.log ((K : ℝ) ^ 2 + 1) := by
  have hP : (0 : ℝ) < primorial w := by exact_mod_cast primorial_pos w
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hE : (0 : ℝ) < crossAffineEnvelope (preSievedShifts K w) m q := by
    exact_mod_cast (show 0 < crossAffineEnvelope (preSievedShifts K w) m q by
      unfold crossAffineEnvelope; omega)
  have h := Real.log_le_log hE
    (show (crossAffineEnvelope (preSievedShifts K w) m q : ℝ) ≤
      (m * q * primorial w * (K ^ 2 + 1) : ℕ) by
        exact_mod_cast crossAffineEnvelope_preSieved_le K w hm hq)
  push_cast at h
  rw [Real.log_mul (by positivity : (m : ℝ) * q * primorial w ≠ 0)
      (by positivity : (K : ℝ) ^ 2 + 1 ≠ 0),
    Real.log_mul (by positivity : (m : ℝ) * q ≠ 0) hP.ne',
    Real.log_mul hmR.ne' hqR.ne'] at h
  exact h

theorem log_crossExceptionalModulus_preSieved_le (K w : ℕ) {m q : ℕ}
    (hm : 0 < m) (hq : q.Prime) :
    Real.log (crossExceptionalModulus (preSievedShifts K w) m q) ≤
      (K : ℝ) ^ 2 *
        (Real.log m + Real.log q + Real.log (primorial w) + Real.log ((K : ℝ) ^ 2 + 1)) := by
  have hpos : (0 : ℝ) < crossExceptionalModulus (preSievedShifts K w) m q := by
    exact_mod_cast crossExceptionalModulus_pos (H := preSievedShifts K w) hm hq
  have hbase := Real.log_le_log hpos
    (show (crossExceptionalModulus (preSievedShifts K w) m q : ℝ) ≤
      (crossAffineEnvelope (preSievedShifts K w) m q ^
        Fintype.card (preSievedShifts K w × preSievedShifts K w) : ℕ) by
          exact_mod_cast crossExceptionalModulus_le_envelope_pow (preSievedShifts K w) m q)
  have hlog : Real.log (crossExceptionalModulus (preSievedShifts K w) m q) ≤
      (K : ℝ) ^ 2 * Real.log (crossAffineEnvelope (preSievedShifts K w) m q) := by
    simpa only [Nat.cast_pow, Real.log_pow, Fintype.card_prod, Fintype.card_coe,
      card_preSievedShifts, Nat.cast_mul, pow_two] using hbase
  exact hlog.trans (mul_le_mul_of_nonneg_left
    (log_crossAffineEnvelope_preSieved_le K w hm hq.pos) (sq_nonneg _))

theorem log_fullAffineExceptionalInteger_le (K w : ℕ) {m q : ℕ} {V : ℝ}
    (hm : 0 < m) (hq : q.Prime)
    (hmV : Real.log m ≤ V) (hqV : Real.log q ≤ V)
    (hPV : Real.log (primorial w) ≤ V) (hKV : Real.log ((K : ℝ) ^ 2 + 1) ≤ V) :
    Real.log (m * crossExceptionalModulus (preSievedShifts K w) m q : ℕ) ≤
      (1 + 4 * (K : ℝ) ^ 2) * V := by
  have hM : (0 : ℝ) < crossExceptionalModulus (preSievedShifts K w) m q := by
    exact_mod_cast crossExceptionalModulus_pos (H := preSievedShifts K w) hm hq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Nat.cast_mul, Real.log_mul hmR.ne' hM.ne']
  have hlog := log_crossExceptionalModulus_preSieved_le K w hm hq
  have hsum : Real.log m + Real.log q + Real.log (primorial w) +
      Real.log ((K : ℝ) ^ 2 + 1) ≤ 4 * V := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsum (sq_nonneg (K : ℝ))
  nlinarith

end

end Erdos4b
