/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberCoefficientBounds
import ErdosProblems.Erdos207.AbsorberGainDefectFamily

/-! # Uniform polynomial bank bounds for all four crude-moment coefficients -/

namespace Erdos207

open scoped NNReal

noncomputable section

def crudeCommonGoodCoefficient (q : ℕ) : ℕ :=
  2 ^ (4 * q) * (q + 1) ^ 2 * q * 2 ^ (3 * q + 1)

def crudeGainGoodCoefficient (q : ℕ) : ℕ :=
  2 ^ (4 * q) * (q + 1) ^ 2 * 2 ^ q * 2 ^ (3 * q)

def crudeGainReverseCoefficient (q : ℕ) : ℕ :=
  2 * (q + 1) * 2 ^ q * 2 ^ (q + 1)

def crudeExceptionalCoefficient (q : ℕ) : ℕ :=
  2 ^ q * (2 + 2 ^ (q ^ 3) * (q + 1))

def absorberCrudeWeightCoefficient (q : ℕ) : ℕ :=
  2 ^ q + (q + 1) + (q + 1) ^ 2 *
    (2 * crudeCommonGoodCoefficient q + crudeExceptionalCoefficient q) +
    (q + 1) * (crudeGainGoodCoefficient q + crudeGainReverseCoefficient q +
      crudeExceptionalCoefficient q)

def pairBankPolynomialCoefficient (q : ℕ) : ℕ :=
  q * (q + 1) * (2 ^ (q ^ 3) * (q + 1))

def absorberCrudeBankCoefficient (q : ℕ) : ℕ :=
  absorberCrudeWeightCoefficient q * (pairBankPolynomialCoefficient q + 1) ^ 2

lemma nnreal_le_add_one_sq (x : ℝ≥0) : x ≤ (x + 1) ^ 2 := by
  have h : (x : ℝ) ≤ ((x : ℝ) + 1) ^ 2 := by nlinarith [x.property, sq_nonneg (x : ℝ)]
  exact_mod_cast h

lemma nnreal_one_le_add_one_sq (x : ℝ≥0) : 1 ≤ (x + 1) ^ 2 := by
  have h : (1 : ℝ≥0) ≤ x + 1 := le_add_of_nonneg_left zero_le
  simpa only [one_pow] using pow_le_pow_left₀ (show (0 : ℝ≥0) ≤ 1 from zero_le) h 2

lemma four_nat_le_sum (a b c d : ℕ) :
    a ≤ a + b + c + d ∧ b ≤ a + b + c + d ∧
      c ≤ a + b + c + d ∧ d ≤ a + b + c + d := by omega

theorem commonThreatGoodWeightBound_eq_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) :
    commonThreatGoodWeightBound q B = (crudeCommonGoodCoefficient q : ℝ≥0) *
      (pairExactBankExtensionCoefficient q B : ℝ≥0) ^ 2 := by
  simp only [commonThreatGoodWeightBound, crudeCommonGoodCoefficient,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem gainDefectGoodWeightBound_eq_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) :
    gainDefectGoodWeightBound q B = (crudeGainGoodCoefficient q : ℝ≥0) *
      (pairExactBankExtensionCoefficient q B : ℝ≥0) ^ 2 := by
  simp only [gainDefectGoodWeightBound, crudeGainGoodCoefficient,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem gainDefectReverseGoodWeightBound_eq_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) :
    gainDefectReverseGoodWeightBound q B = (crudeGainReverseCoefficient q : ℝ≥0) *
      (pairExactBankExtensionCoefficient q B : ℝ≥0) ^ 2 := by
  simp only [gainDefectReverseGoodWeightBound, crudeGainReverseCoefficient,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  ring

theorem commonThreatExceptionalWeightBound_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) :
    commonThreatExceptionalWeightBound q B ≤ (crudeExceptionalCoefficient q : ℝ≥0) *
      (pairExactBankExtensionCoefficient q B + 1 : ℝ≥0) ^ 2 := by
  let C : ℝ≥0 := pairExactBankExtensionCoefficient q B
  let D : ℝ≥0 := 2 ^ (q ^ 3) * (q + 1)
  have hC := nnreal_le_add_one_sq C
  have hD := mul_le_mul_of_nonneg_left (nnreal_one_le_add_one_sq C) (show 0 ≤ D from zero_le)
  simp only [mul_one] at hD
  have h : 2 * C + D ≤ (2 + D) * (C + 1) ^ 2 := by
    calc
      2 * C + D ≤ 2 * (C + 1) ^ 2 + D * (C + 1) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hC zero_le) hD
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left h (show (0 : ℝ≥0) ≤ 2 ^ q by positivity)
  simpa only [commonThreatExceptionalWeightBound, crudeExceptionalCoefficient,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    C, D, mul_assoc] using hm

theorem absorber_crude_coefficients_le_square
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) :
    let bound := (absorberCrudeWeightCoefficient q : ℝ≥0) *
      (pairExactBankExtensionCoefficient q B + 1 : ℝ≥0) ^ 2
    (2 : ℝ≥0) ^ q * pairExactBankExtensionCoefficient q B ≤ bound ∧
      (pairTwoAwayThreatExtensionCoefficient q B : ℝ≥0) ≤ bound ∧
      absorberCommonThreatWeightBound q B ≤ bound ∧
      absorberGainDefectWeightBound q B ≤ bound := by
  let C : ℝ≥0 := pairExactBankExtensionCoefficient q B
  let Z : ℝ≥0 := (C + 1) ^ 2
  have hC : C ≤ Z := nnreal_le_add_one_sq C
  have hC2 : C ^ 2 ≤ Z := by dsimp only [Z]; gcongr; exact le_add_of_nonneg_right zero_le
  obtain ⟨hroot, hpair, hcommon, hgain⟩ := four_nat_le_sum (2 ^ q) (q + 1)
    ((q + 1) ^ 2 * (2 * crudeCommonGoodCoefficient q + crudeExceptionalCoefficient q))
    ((q + 1) * (crudeGainGoodCoefficient q + crudeGainReverseCoefficient q +
      crudeExceptionalCoefficient q))
  have hc := commonThreatExceptionalWeightBound_le_polynomial q B
  change commonThreatExceptionalWeightBound q B ≤ (crudeExceptionalCoefficient q : ℝ≥0) * Z at hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (2 : ℝ≥0) ^ q * C ≤ (absorberCrudeWeightCoefficient q : ℝ≥0) * Z
    exact mul_le_mul (by exact_mod_cast hroot) hC zero_le zero_le
  · simp only [pairTwoAwayThreatExtensionCoefficient, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    change (q + 1 : ℝ≥0) * C ≤ (absorberCrudeWeightCoefficient q : ℝ≥0) * Z
    exact mul_le_mul (by exact_mod_cast hpair) hC zero_le zero_le
  · unfold absorberCommonThreatWeightBound commonThreatWeightBound
    rw [commonThreatGoodWeightBound_eq_polynomial]
    calc
      _ ≤ (q + 1 : ℝ≥0) ^ 2 * (2 * ((crudeCommonGoodCoefficient q : ℝ≥0) * Z) +
          (crudeExceptionalCoefficient q : ℝ≥0) * Z) := by gcongr
      _ = (((q + 1) ^ 2 * (2 * crudeCommonGoodCoefficient q +
          crudeExceptionalCoefficient q) : ℕ) : ℝ≥0) * Z := by push_cast; ring
      _ ≤ (absorberCrudeWeightCoefficient q : ℝ≥0) * Z := by gcongr; exact hcommon
  · unfold absorberGainDefectWeightBound gainDefectWeightBound
    rw [gainDefectGoodWeightBound_eq_polynomial, gainDefectReverseGoodWeightBound_eq_polynomial]
    calc
      _ ≤ (q + 1 : ℝ≥0) * ((crudeGainGoodCoefficient q : ℝ≥0) * Z +
          (crudeGainReverseCoefficient q : ℝ≥0) * Z +
          (crudeExceptionalCoefficient q : ℝ≥0) * Z) := by gcongr
      _ = (((q + 1) * (crudeGainGoodCoefficient q + crudeGainReverseCoefficient q +
          crudeExceptionalCoefficient q) : ℕ) : ℝ≥0) * Z := by push_cast; ring
      _ ≤ (absorberCrudeWeightCoefficient q : ℝ≥0) * Z := by gcongr; exact hgain

theorem pairExactBankExtensionCoefficient_le_bank_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) :
    pairExactBankExtensionCoefficient q B ≤ pairBankPolynomialCoefficient q * (B.card + 1) ^ q := by
  have h := pairExactBankExtensionCoefficient_le (q := q) (B := B) le_rfl
  calc
    _ ≤ pairExactBankCoefficientUpper q B.card := h
    _ = _ := by unfold pairExactBankCoefficientUpper pairBankPolynomialCoefficient; ring

theorem absorber_crude_coefficients_le_bank_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (B : TripleSystemOn V) :
    let bound := (absorberCrudeBankCoefficient q : ℝ≥0) * (B.card + 1 : ℝ≥0) ^ (2 * q)
    (2 : ℝ≥0) ^ q * pairExactBankExtensionCoefficient q B ≤ bound ∧
      (pairTwoAwayThreatExtensionCoefficient q B : ℝ≥0) ≤ bound ∧
      absorberCommonThreatWeightBound q B ≤ bound ∧
      absorberGainDefectWeightBound q B ≤ bound := by
  have hC := pairExactBankExtensionCoefficient_le_bank_polynomial q B
  have hpow : 1 ≤ (B.card + 1) ^ q := Nat.one_le_pow _ _ (by omega)
  have hbase : pairExactBankExtensionCoefficient q B + 1 ≤
      (pairBankPolynomialCoefficient q + 1) * (B.card + 1) ^ q := by nlinarith
  have hbaseNN : (pairExactBankExtensionCoefficient q B + 1 : ℝ≥0) ≤
      (pairBankPolynomialCoefficient q + 1 : ℝ≥0) * (B.card + 1 : ℝ≥0) ^ q := by
    exact_mod_cast hbase
  have hbound : (absorberCrudeWeightCoefficient q : ℝ≥0) *
      (pairExactBankExtensionCoefficient q B + 1 : ℝ≥0) ^ 2 ≤
      (absorberCrudeBankCoefficient q : ℝ≥0) * (B.card + 1 : ℝ≥0) ^ (2 * q) := by
    calc
      _ ≤ (absorberCrudeWeightCoefficient q : ℝ≥0) *
          ((pairBankPolynomialCoefficient q + 1 : ℝ≥0) * (B.card + 1 : ℝ≥0) ^ q) ^ 2 := by gcongr
      _ = _ := by
        simp only [absorberCrudeBankCoefficient, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
          Nat.cast_one, mul_pow, ← pow_mul, Nat.mul_comm q 2]
        ring
  obtain ⟨hr, hp, hc, hg⟩ := absorber_crude_coefficients_le_square q B
  exact ⟨hr.trans hbound, hp.trans hbound, hc.trans hbound, hg.trans hbound⟩

end

end Erdos207
