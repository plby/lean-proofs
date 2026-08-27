/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCanonicalReserve

/-!
# Scalar inequalities for the canonical outer corridor

With corridor error `t⁻¹⁰⁰` and inverse-clock exponent `67`, the entire
dynamic scale certificate follows from four natural-number power
inequalities.  Keeping those inequalities integral lets the eventual dyadic
hierarchy discharge them by ordinary exponent comparison.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

lemma fineOuterInitialOffset_eq (outside t : ℕ) :
    fineOuterInitialOffset outside t =
      32 * (t : ℝ)⁻¹ ^ fineOuterCorridorExponent * outside := by
  simp only [fineOuterInitialOffset, fineOuterCorridorError,
    NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_inv, NNReal.coe_natCast,
    NNReal.coe_pow]

structure FineOuterCanonicalScalars
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside t K i : ℕ) : Prop where
  small : 100 *
      (fineOuterInitialOffset outside t * (t : ℝ) ^ coupledOuterExponent) ≤
    (outside : ℝ) / (4 * (t : ℝ) ^ 2)
  round_buffer : fineOuterBuffer outside t + 1 ≤
    fineOuterInitialOffset outside t
  round_two : 2 ≤ fineOuterInitialOffset outside t
  lower_one : 1 + fineOuterBuffer outside t +
      fineOuterInitialOffset outside t * (t : ℝ) ^ coupledOuterExponent ≤
    (outside : ℝ) / (4 * (t : ℝ) ^ 2)
  clock : 100 * (4 * outside : ℝ) ≤
    fineOuterInitialOffset outside t * outerSharpEligiblePairs H X i
  aggregate : (K : ℝ) ≤ fineOuterInitialOffset outside t *
    ((outside : ℝ) / (4 * (t : ℝ) ^ 2))

/-- The four integral power inequalities imply all six corridor scalars. -/
theorem fineOuterCanonicalScalars
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside t K i : ℕ)
    (houtside : 0 < outside) (ht : 0 < t)
    (hlowerClock : (outside : ℝ) ^ 2 ≤
      4 * t * outerSharpEligiblePairs H X i)
    (hsmallPower : 12800 ≤ t ^ 31)
    (hoffsetPower : t ^ fineOuterCorridorExponent ≤ 16 * outside)
    (hclockPower : 50 * t ^ 101 ≤ outside ^ 2)
    (haggregatePower : t ^ 102 * K ≤ 8 * outside ^ 2) :
    FineOuterCanonicalScalars H X outside t K i := by
  let T : ℝ := t
  let N : ℝ := outside
  let epsilon : ℝ := (t : ℝ)⁻¹ ^ fineOuterCorridorExponent
  let offset : ℝ := fineOuterInitialOffset outside t
  have hT : 0 < T := by
    dsimp only [T]
    exact_mod_cast ht
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast houtside
  have hepsilon : 0 ≤ epsilon := by
    dsimp only [epsilon]
    positivity
  have hepsilon_mul : epsilon * T ^ fineOuterCorridorExponent = 1 := by
    dsimp only [epsilon, T]
    rw [← mul_pow, inv_mul_cancel₀]
    · exact one_pow _
    · exact_mod_cast ht.ne'
  have hoffset : offset = 32 * epsilon * N := by
    simp only [offset, fineOuterInitialOffset_eq, epsilon, T, N]
  have hsmallPowerReal : (12800 : ℝ) ≤ T ^ 31 := by
    dsimp only [T]
    exact_mod_cast hsmallPower
  have hepsilonSplit : epsilon * T ^ 69 * T ^ 31 = 1 := by
    calc
      epsilon * T ^ 69 * T ^ 31 =
          epsilon * (T ^ 69 * T ^ 31) := by ring
      _ = epsilon * T ^ 100 := by
        rw [← pow_add]
      _ = epsilon * T ^ fineOuterCorridorExponent := by
        norm_num [fineOuterCorridorExponent]
      _ = 1 := hepsilon_mul
  have hcoefficient : 12800 * epsilon * T ^ 69 ≤ 1 := by
    calc
      12800 * epsilon * T ^ 69 =
          (epsilon * T ^ 69) * 12800 := by ring
      _ ≤ (epsilon * T ^ 69) * T ^ 31 := by gcongr
      _ = 1 := by simpa only [mul_assoc] using hepsilonSplit
  have hsmall : 100 * (offset * T ^ coupledOuterExponent) ≤
      N / (4 * T ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * T ^ 2)).2
    calc
      100 * (offset * T ^ coupledOuterExponent) * (4 * T ^ 2) =
          N * (12800 * epsilon * T ^ 69) := by
        rw [hoffset]
        norm_num [coupledOuterExponent]
        ring
      _ ≤ N * 1 := by gcongr
      _ = N := mul_one N
  have hoffsetPowerReal : T ^ fineOuterCorridorExponent ≤ 16 * N := by
    dsimp only [T, N]
    exact_mod_cast hoffsetPower
  have hroundTwo : 2 ≤ offset := by
    have hscaled := mul_le_mul_of_nonneg_left hoffsetPowerReal hepsilon
    rw [hepsilon_mul] at hscaled
    rw [hoffset]
    nlinarith
  have hroundBuffer : fineOuterBuffer outside t + 1 ≤ offset := by
    unfold fineOuterBuffer
    dsimp only [offset]
    linarith
  have hpowOne : 1 ≤ T ^ coupledOuterExponent := by
    have hTone : 1 ≤ T := by
      dsimp only [T]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ht.ne')
    exact one_le_pow₀ hTone
  have hoffset_le_upper : offset ≤ offset * T ^ coupledOuterExponent := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpowOne (by rw [hoffset]; positivity)
  have hupperTwo : 2 ≤ offset * T ^ coupledOuterExponent :=
    hroundTwo.trans hoffset_le_upper
  have hlowerOne : 1 + fineOuterBuffer outside t +
      offset * T ^ coupledOuterExponent ≤ N / (4 * T ^ 2) := by
    have hhalf : fineOuterBuffer outside t = offset / 2 := by
      rfl
    calc
      1 + fineOuterBuffer outside t + offset * T ^ coupledOuterExponent ≤
          2 * (offset * T ^ coupledOuterExponent) := by
        rw [hhalf]
        nlinarith [hoffset_le_upper]
      _ ≤ N / (4 * T ^ 2) := by nlinarith [hsmall]
  have hclockPowerReal : (50 : ℝ) * T ^ 101 ≤ N ^ 2 := by
    dsimp only [T, N]
    exact_mod_cast hclockPower
  have hlowerClock' : N ^ 2 ≤
      4 * T * (outerSharpEligiblePairs H X i : ℝ) := by
    simpa only [N, T, Nat.cast_mul, Nat.cast_ofNat] using hlowerClock
  have hclockCoefficient : (50 : ℝ) ≤
      4 * epsilon * outerSharpEligiblePairs H X i := by
    have hchain := hclockPowerReal.trans hlowerClock'
    have hscaled := mul_le_mul_of_nonneg_left hchain hepsilon
    have hT101 : epsilon * T ^ 101 = T := by
      calc
        epsilon * T ^ 101 =
            (epsilon * T ^ fineOuterCorridorExponent) * T := by
          norm_num [fineOuterCorridorExponent, pow_succ]
          ring
        _ = T := by rw [hepsilon_mul, one_mul]
    have hscaled' : T * 50 ≤
        T * (4 * epsilon * outerSharpEligiblePairs H X i) := by
      calc
        T * 50 = (epsilon * T ^ 101) * 50 := by rw [hT101]
        _ = epsilon * (50 * T ^ 101) := by ring
        _ ≤ epsilon *
            (4 * T * outerSharpEligiblePairs H X i) := hscaled
        _ = T * (4 * epsilon * outerSharpEligiblePairs H X i) := by ring
    exact le_of_mul_le_mul_left hscaled' hT
  have hclock : 100 * (4 * outside : ℝ) ≤
      offset * outerSharpEligiblePairs H X i := by
    rw [hoffset]
    dsimp only [N]
    calc
      100 * (4 * (outside : ℝ)) = (8 * outside) * 50 := by ring
      _ ≤ (8 * outside) *
          (4 * epsilon * outerSharpEligiblePairs H X i) := by
        gcongr
      _ = 32 * epsilon * outside * outerSharpEligiblePairs H X i := by ring
  have haggregateNN : (K : ℝ≥0) ≤
      (t : ℝ≥0)⁻¹ ^ 102 * ((8 * outside ^ 2 : ℕ) : ℝ≥0) := by
    apply cast_le_inv_pow_mul_of_pow_mul_le ht
    simpa only [Nat.mul_comm] using haggregatePower
  have haggregateBase : (K : ℝ) ≤ 8 * (t : ℝ)⁻¹ ^ 102 * N ^ 2 := by
    have haggregateNNReal : (K : ℝ) ≤
        (((t : ℝ≥0)⁻¹ ^ 102 *
          ((8 * outside ^ 2 : ℕ) : ℝ≥0) : ℝ≥0) : ℝ) := by
      exact_mod_cast haggregateNN
    calc
      (K : ℝ) ≤ (t : ℝ)⁻¹ ^ 102 * (8 * (outside : ℝ) ^ 2) := by
        norm_num only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv,
          NNReal.coe_natCast, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
          at haggregateNNReal
        simpa using haggregateNNReal
      _ = 8 * (t : ℝ)⁻¹ ^ 102 * N ^ 2 := by
        dsimp only [N]
        ring
  have haggregateIdentity : offset * (N / (4 * T ^ 2)) =
      8 * T⁻¹ ^ 102 * N ^ 2 := by
    rw [hoffset]
    dsimp only [epsilon]
    norm_num [fineOuterCorridorExponent]
    field_simp
    ring
  have haggregate : (K : ℝ) ≤ offset * (N / (4 * T ^ 2)) := by
    rw [haggregateIdentity]
    simpa only [T] using haggregateBase
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [T, N, offset] using hsmall
  · simpa only [offset] using hroundBuffer
  · simpa only [offset] using hroundTwo
  · simpa only [T, N, offset] using hlowerOne
  · simpa only [offset] using hclock
  · simpa only [T, N, offset] using haggregate

end

end Erdos207
