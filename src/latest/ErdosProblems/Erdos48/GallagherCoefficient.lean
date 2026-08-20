/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherHybridTaylor
import ErdosProblems.Erdos48.External.Erdos4.SingletonAsymptotics

/-!
# Lower bounds for Gallagher's arithmetic amplifier coefficient

The all-endpoint Wirsing estimate for the squarefree reciprocal-totient mean
is converted into a uniform half-logarithmic lower bound for every conductor
below the amplifier cutoff.  The final theorem exposes one explicit
logarithmic-size hypothesis suitable for later asymptotic parameter choices.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

/-- The uniform Wirsing estimate supplies one half of the logarithmic
amplifier weight once its explicit varying-modulus error is dominated. -/
theorem exists_uniform_roughAmplifierCoefficient_half_log_lower :
    ∃ K : ℝ, 0 < K ∧
      ∀ {q A : ℕ}, 0 < q →
        20 * (K + primeLogDivisorMass q + Real.log 2) ≤ Real.log A →
        Real.log A / 2 ≤ roughAmplifierCoefficient q A := by
  obtain ⟨K, hK, hmean⟩ :=
    Erdos4.exists_uniform_singletonMean_lower_bound_general
  refine ⟨K, hK, ?_⟩
  intro q A hq hlarge
  have hM := hmean hq hlarge
  have hphi : 0 < q.totient := Nat.totient_pos.mpr hq
  have hfactor : 0 ≤ (q : ℝ) / q.totient := by positivity
  calc
    Real.log A / 2 =
        ((q : ℝ) / q.totient) *
          (coprimeHarmonicDensity q * Real.log A / 2) := by
      unfold coprimeHarmonicDensity
      field_simp
    _ ≤ ((q : ℝ) / q.totient) *
          squarefreeCoprimeInvTotientMean q A :=
      mul_le_mul_of_nonneg_left hM hfactor
    _ = roughAmplifierCoefficient q A := by
      unfold roughAmplifierCoefficient
      rfl

/-- A single explicit logarithmic-size hypothesis gives the coefficient
lower bound simultaneously for all conductors below `Q < A`. -/
theorem exists_uniform_roughAmplifierCoefficient_half_log_lower_up_to :
    ∃ K C : ℝ, 0 < K ∧
      ∀ {Q A : ℕ}, Q < A → 2 ≤ Real.log A →
        20 * (K + (Real.log (Real.log A) + C + 2) + Real.log 2) ≤
          Real.log A →
        ∀ q ∈ Finset.Ioc 0 Q,
          Real.log A / 2 ≤ roughAmplifierCoefficient q A := by
  obtain ⟨K, hK, hcoeff⟩ :=
    exists_uniform_roughAmplifierCoefficient_half_log_lower
  obtain ⟨C, hmass⟩ :=
    exists_uniform_primeLogDivisorMass_le_log_log_add
  refine ⟨K, C, hK, ?_⟩
  intro Q A hQA hlogA hdom q hqmem
  have hqBounds := Finset.mem_Ioc.mp hqmem
  have hradPos : 0 < Erdos4.natRadical q := Nat.radical_pos q
  have hradSq : Squarefree (Erdos4.natRadical q) :=
    UniqueFactorizationMonoid.squarefree_radical
  have hradLe : Erdos4.natRadical q ≤ q := by
    exact Nat.radical_le_self_iff.mpr hqBounds.1.ne'
  have hradA : Erdos4.natRadical q < A :=
    hradLe.trans_lt (hqBounds.2.trans_lt hQA)
  have hmassRad := hmass hradPos hradSq hradA hlogA
  have hmassQ :
      primeLogDivisorMass q ≤ Real.log (Real.log A) + C + 2 := by
    rw [← Erdos4.primeLogDivisorMass_natRadical]
    exact hmassRad
  apply hcoeff hqBounds.1
  linarith

end Erdos48
