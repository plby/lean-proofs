/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos387.RoughIntervalEstimate

/-!
# Erdős Problem 446: endpoint-free rough counts on polynomial intervals

The finite Brun bound has an explicit endpoint term.  On intervals whose
upper endpoint is only a fixed power of the roughness threshold, the
elementary least-prime-factor decomposition gives the required
`U / log z` bound without that term: its residual rough harmonic mass is
bounded by the uniform logarithmic-ratio envelope.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- A constant bounding the uniform rough harmonic envelope when
`T ≤ z^d`. -/
noncomputable def roughPolynomialEnvelopeConstant (K : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) +
    10 * ((K + BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) /
      Real.log 2 + 1) +
    2 * (Real.exp 16 +
      4 * BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant)

theorem roughLogRatioEnvelope_le_polynomial
    {K : ℝ} (hK : 0 < K) {z T d : ℕ} (hz : 2 ≤ z)
    (hT : T ≤ z ^ d) :
    Erdos387.RoughHarmonic.roughLogRatioEnvelope K z T ≤
      roughPolynomialEnvelopeConstant K d := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hz)
  have hlogZm1 : 0 ≤ Real.log (z - 1 : ℕ) :=
    Real.log_natCast_nonneg (z - 1)
  have hlogZm1Le : Real.log (z - 1 : ℕ) ≤ Real.log (z : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < z - 1 by omega)
    · exact_mod_cast (show z - 1 ≤ z by omega)
  have hmass : 0 ≤ BoundedGaps.Maynard.primeLogDivisorMass 1 := by
    unfold BoundedGaps.Maynard.primeLogDivisorMass
    positivity
  let A : ℝ := K + BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAdiv : A / Real.log (z : ℝ) ≤ A / Real.log 2 :=
    div_le_div_of_nonneg_left hA hlogTwo hlogTwoLe
  have hzm1div : Real.log (z - 1 : ℕ) / Real.log (z : ℝ) ≤ 1 := by
    rw [div_le_one hlogz]
    exact hlogZm1Le
  have hmiddle :
      (K + Real.log (z - 1 : ℕ) +
          BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) /
          Real.log (z : ℝ) ≤ A / Real.log 2 + 1 := by
    have hsplit :
        (K + Real.log (z - 1 : ℕ) +
            BoundedGaps.Maynard.primeLogDivisorMass 1 + Real.log 2) /
            Real.log (z : ℝ) =
          A / Real.log (z : ℝ) +
            Real.log (z - 1 : ℕ) / Real.log (z : ℝ) := by
      dsimp [A]
      ring
    rw [hsplit]
    linarith
  have hfirst : Real.log (T : ℝ) / Real.log (z : ℝ) ≤ (d : ℝ) := by
    by_cases hT0 : T = 0
    · subst T
      simp
    · have hTpos : (0 : ℝ) < T := by
        exact_mod_cast Nat.pos_of_ne_zero hT0
      have hpowpos : (0 : ℝ) < z ^ d := by positivity
      have hlogmono : Real.log (T : ℝ) ≤ Real.log ((z : ℝ) ^ d) :=
        Real.strictMonoOn_log.monotoneOn
          (by simpa only [Set.mem_Ioi] using hTpos)
          (by simpa only [Set.mem_Ioi] using hpowpos)
          (by exact_mod_cast hT)
      rw [Real.log_pow] at hlogmono
      apply (div_le_iff₀ hlogz).2
      simpa [mul_comm] using hlogmono
  unfold Erdos387.RoughHarmonic.roughLogRatioEnvelope
  unfold roughPolynomialEnvelopeConstant
  dsimp [A] at hmiddle
  linarith

/-- Uniform endpoint-free cardinal bound when the residual range is at most
a fixed power of the roughness threshold. -/
theorem exists_uniform_roughCount_le_polynomial :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ (z A U d : ℕ), N ≤ z → 2 ≤ z → 1 ≤ A → U / z ≤ z ^ d →
        ((Erdos387.RoughHarmonic.roughPositiveIoc z A U).card : ℝ) ≤
          C * (d + 1 : ℕ) * (U : ℝ) / Real.log z := by
  obtain ⟨C₀, hC₀, N, hprime⟩ :=
    Erdos387.RoughHarmonic.exists_uniform_primeCounting_le_div_log
  obtain ⟨K, hK, hrough⟩ :=
    Erdos387.RoughHarmonic.exists_uniform_roughReciprocalMass_le_envelope
  let B : ℝ := roughPolynomialEnvelopeConstant K 0 + 1
  let C : ℝ := C₀ * B
  have hB : 0 < B := by
    dsimp [B, roughPolynomialEnvelopeConstant]
    have hmass : 0 ≤ BoundedGaps.Maynard.primeLogDivisorMass 1 := by
      unfold BoundedGaps.Maynard.primeLogDivisorMass
      positivity
    have hcorr : 0 ≤
        BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant := by
      unfold BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant
      positivity
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, N, ?_⟩
  intro z A U d hzN hz hA hUz
  have hbase :=
    Erdos387.RoughHarmonic.card_roughPositiveIoc_le_roughMass_div_log
      (U := U) hC₀ hprime hzN hz hA
  have hrough' := hrough z (U / z) hz
  have hpoly := roughLogRatioEnvelope_le_polynomial hK hz hUz
  have henv :
      Erdos387.roughReciprocalMass z (U / z) ≤
        roughPolynomialEnvelopeConstant K d := hrough'.trans hpoly
  have hpolyLinear : roughPolynomialEnvelopeConstant K d ≤
      B * (d + 1 : ℕ) := by
    have hzero : roughPolynomialEnvelopeConstant K d =
        (d : ℝ) + roughPolynomialEnvelopeConstant K 0 := by
      unfold roughPolynomialEnvelopeConstant
      push_cast
      ring
    rw [hzero]
    dsimp [B]
    have hbaseNonneg : 0 ≤ roughPolynomialEnvelopeConstant K 0 := by
      dsimp [roughPolynomialEnvelopeConstant]
      have hmass : 0 ≤ BoundedGaps.Maynard.primeLogDivisorMass 1 := by
        unfold BoundedGaps.Maynard.primeLogDivisorMass
        positivity
      have hcorr : 0 ≤
          BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant := by
        unfold BoundedGaps.Maynard.reciprocalTotientCorrectionQuarterConstant
        positivity
      positivity
    push_cast
    have hdnon : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith
  have hcoef : 0 ≤ C₀ * (U : ℝ) / Real.log z := by
    have hlogz : 0 < Real.log (z : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < z by omega))
    positivity
  calc
    ((Erdos387.RoughHarmonic.roughPositiveIoc z A U).card : ℝ) ≤
        (C₀ * (U : ℝ) / Real.log z) *
          Erdos387.roughReciprocalMass z (U / z) := hbase
    _ ≤ (C₀ * (U : ℝ) / Real.log z) *
          roughPolynomialEnvelopeConstant K d :=
      mul_le_mul_of_nonneg_left henv hcoef
    _ ≤ (C₀ * (U : ℝ) / Real.log z) * (B * (d + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left hpolyLinear hcoef
    _ = C * (d + 1 : ℕ) * (U : ℝ) / Real.log z := by
      dsimp [C]
      ring

end Erdos446
