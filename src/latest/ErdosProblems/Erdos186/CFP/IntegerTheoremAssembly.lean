/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.AnchoredWitness
import ErdosProblems.Erdos186.CFP.PreprocessedWitness

/-!
# Terminal assembly for the integer CFP theorem

This module contains the outer, input-uniform numerical choices used after
the Bilu--Freiman preprocessing constants have been fixed.  The actual
random-partition/greedy constructor is kept in its dedicated module; the
lemmas here make sure that it will not need to expose a dyadic horizon or an
auxiliary anchoring premise at the source-facing boundary.
-/

namespace Erdos186.CFP.IntegerTheoremAssembly

open Erdos186.CFP

noncomputable section

/-- A dyadic horizon satisfying every outer inequality consumed by
`exists_uniform_preprocessedFixedScaleWitness_of_biluFreiman`.  The source
endpoint and the fixed preprocessing index bound are both absorbed by the
same power of two. -/
theorem exists_preprocessingDyadicHorizon
    (first horizonFactor D sourceEndpoint indexBound : ℕ)
    (hhorizonFactor : 0 < horizonFactor) :
    ∃ last h : ℕ,
      h = horizonFactor * 2 ^ last ∧
      sourceEndpoint < h ∧
      indexBound ≤ h ∧
      first < last ∧
      (2 * D + 1) * first +
          2 * horizonFactor * (D - 1) < last := by
  let outer := (2 * D + 1) * first +
    2 * horizonFactor * (D - 1)
  let size := max (sourceEndpoint + 1) indexBound
  let last := max (first + 1) (outer + 1) + Nat.log 2 size + 1
  let h := horizonFactor * 2 ^ last
  have hfirstLast : first < last := by
    dsimp only [last]
    have hbase : first + 1 ≤ max (first + 1) (outer + 1) :=
      le_max_left _ _
    omega
  have houterLast : outer < last := by
    dsimp only [last]
    have hbase : outer + 1 ≤ max (first + 1) (outer + 1) :=
      le_max_right _ _
    omega
  have hsizePow : size < 2 ^ last := by
    have hlog : size < 2 ^ (Nat.log 2 size + 1) :=
      Nat.lt_pow_succ_log_self Nat.one_lt_two size
    have hexponent : Nat.log 2 size + 1 ≤ last := by
      dsimp only [last]
      omega
    exact hlog.trans_le (Nat.pow_le_pow_right (by omega) hexponent)
  have hpowH : 2 ^ last ≤ h := by
    dsimp only [h]
    calc
      2 ^ last = 1 * 2 ^ last := by simp
      _ ≤ horizonFactor * 2 ^ last :=
        Nat.mul_le_mul_right _ hhorizonFactor
  refine ⟨last, h, rfl, ?_, ?_, hfirstLast, ?_⟩
  · have hsourceSize : sourceEndpoint + 1 ≤ size :=
      le_max_left _ _
    exact lt_of_lt_of_le (lt_of_lt_of_le (Nat.lt_succ_self _) hsourceSize)
      (hsizePow.le.trans hpowH)
  · exact (le_max_right (sourceEndpoint + 1) indexBound).trans
      (hsizePow.le.trans hpowH)
  · simpa only [outer] using houterLast

/-- Choosing the horizon itself as the preprocessing interval length
discharges the two source-horizon comparisons whenever the rank cutoff is
at least two. -/
theorem preprocessingHorizon_powerBounds
    {h D : ℕ} (hh : 0 < h) (hD : 2 ≤ D) :
    h ≤ h ∧ h ≤ h ^ (D - 1) := by
  refine ⟨le_rfl, ?_⟩
  have hexponent : 1 ≤ D - 1 := by omega
  calc
    h = h ^ 1 := by simp
    _ ≤ h ^ (D - 1) := Nat.pow_le_pow_right hh hexponent

/-- A positive-interval source becomes a zero-anchored preprocessing input
inside any strictly larger dyadic horizon. -/
theorem insert_zero_subset_preprocessingInterval
    {A : Finset ℤ} {n h : ℕ}
    (hA : A ⊆ Finset.Icc 1 (n : ℤ)) (hnh : n < h) :
    insert 0 A ⊆ Finset.Icc (0 : ℤ) ((h : ℤ) - 1) := by
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hzA
  · apply Finset.mem_Icc.mpr
    constructor
    · omega
    · have hnhZ : (n : ℤ) < (h : ℤ) := by exact_mod_cast hnh
      omega
  · have hzBounds := Finset.mem_Icc.mp (hA hzA)
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · have hnhZ : (n : ℤ) < (h : ℤ) := by exact_mod_cast hnh
      omega

/-- Sets in the positive source interval do not contain the auxiliary
origin used by preprocessing. -/
theorem zero_not_mem_of_subset_Icc_one
    {A : Finset ℤ} {n : ℕ} (hA : A ⊆ Finset.Icc 1 (n : ℤ)) :
    0 ∉ A := by
  intro hzero
  have := Finset.mem_Icc.mp (hA hzero)
  omega

/-- Fixed additive overhead in the controlled horizon exponent. -/
def preprocessingHorizonOffset
    (first horizonFactor D indexBound : ℕ) : ℕ :=
  max (first + 1)
      ((2 * D + 1) * first + 2 * horizonFactor * (D - 1) + 1) +
    indexBound

/-- Uniform coefficient comparing the logarithm of the preprocessing
horizon to the logarithm of the source cardinality. -/
def preprocessingHorizonLogCoefficient
    (first horizonFactor D indexBound betaNat : ℕ) : ℕ :=
  horizonFactor +
    preprocessingHorizonOffset first horizonFactor D indexBound +
    betaNat + 1

/-- Enlarge the real source exponent to a positive natural exponent.  The
strict lower bound is retained because the preprocessing horizon uses a
genuine positive power of the source cardinality. -/
theorem exists_natExponent_ge (beta : ℝ) (hbeta : 1 < beta) :
    ∃ betaNat : ℕ, 1 < betaNat ∧ beta ≤ (betaNat : ℝ) := by
  obtain ⟨betaNat, hbetaNat⟩ := exists_nat_gt beta
  refine ⟨betaNat, ?_, hbetaNat.le⟩
  exact_mod_cast hbeta.trans hbetaNat

/-- Replace a real source exponent by any larger natural exponent.  This is
the exact cast bridge used before the controlled dyadic-horizon choice. -/
theorem sourceEndpoint_le_card_pow_nat
    {sourceEndpoint card betaNat : ℕ} {beta : ℝ}
    (hcard : 0 < card) (hbeta : beta ≤ (betaNat : ℝ))
    (hsource : (sourceEndpoint : ℝ) ≤ Real.rpow (card : ℝ) beta) :
    sourceEndpoint ≤ card ^ betaNat := by
  have hcardOne : (1 : ℝ) ≤ (card : ℝ) := by exact_mod_cast hcard
  have hrpow : Real.rpow (card : ℝ) beta ≤
      Real.rpow (card : ℝ) (betaNat : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hcardOne hbeta
  change (card : ℝ) ^ beta ≤ (card : ℝ) ^ (betaNat : ℝ) at hrpow
  rw [Real.rpow_natCast] at hrpow
  have hcast : (sourceEndpoint : ℝ) ≤ ((card ^ betaNat : ℕ) : ℝ) := by
    exact_mod_cast hsource.trans hrpow
  exact_mod_cast hcast

/-- Any natural loss bounded by a fixed coefficient times the reserve scale
has the source-facing logarithmic form as soon as the input has at least two
points.  This is the final cast/logarithm bridge used after the preprocessing
and random-reserve losses have been combined in `ℕ`. -/
theorem natCoefficient_mul_scale_le_logb_loss
    (coefficient s card : ℕ) (hcard : 2 ≤ card) :
    ((coefficient * s : ℕ) : ℝ) ≤
      (coefficient : ℝ) * (s : ℝ) * Real.logb 2 (card : ℝ) + 1 := by
  have hcardReal : (2 : ℝ) ≤ (card : ℝ) := by
    exact_mod_cast hcard
  have hlogbOne : 1 ≤ Real.logb 2 (card : ℝ) := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos (by norm_num))]
    simpa using Real.strictMonoOn_log.monotoneOn
      (by norm_num : (0 : ℝ) < 2)
      (zero_lt_two.trans_le hcardReal) hcardReal
  calc
    ((coefficient * s : ℕ) : ℝ) =
        (coefficient : ℝ) * (s : ℝ) := by norm_num
    _ ≤ (coefficient : ℝ) * (s : ℝ) *
        Real.logb 2 (card : ℝ) := by
      exact le_mul_of_one_le_right (by positivity) hlogbOne
    _ ≤ (coefficient : ℝ) * (s : ℝ) *
        Real.logb 2 (card : ℝ) + 1 := by norm_num

/-- Inequality form of `natCoefficient_mul_scale_le_logb_loss`, ready to
consume the natural loss estimate returned by the finite construction. -/
theorem natLoss_le_logb_loss
    {loss coefficient s card : ℕ}
    (hloss : loss ≤ coefficient * s) (hcard : 2 ≤ card) :
    (loss : ℝ) ≤
      (coefficient : ℝ) * (s : ℝ) * Real.logb 2 (card : ℝ) + 1 := by
  have hlossReal : (loss : ℝ) ≤ ((coefficient * s : ℕ) : ℝ) := by
    exact_mod_cast hloss
  exact hlossReal.trans
    (natCoefficient_mul_scale_le_logb_loss coefficient s card hcard)

/-- Cardinality-controlled version of the dyadic horizon choice.  Besides
the exact preprocessing inequalities, it gives the uniform binary-log bound
needed to turn the deterministic preprocessing loss into
`O(s * log |A|)`. -/
theorem exists_preprocessingDyadicHorizon_with_logBound
    (first horizonFactor D sourceEndpoint indexBound betaNat card : ℕ)
    (hhorizonFactor : 0 < horizonFactor) (hbetaNat : 0 < betaNat)
    (hsource : sourceEndpoint ≤ card ^ betaNat) :
    ∃ last h : ℕ,
      h = horizonFactor * 2 ^ last ∧
      sourceEndpoint < h ∧
      indexBound ≤ h ∧
      first < last ∧
      (2 * D + 1) * first +
          2 * horizonFactor * (D - 1) < last ∧
      Nat.log 2 h + 1 ≤
        preprocessingHorizonLogCoefficient first horizonFactor D
          indexBound betaNat * (Nat.log 2 card + 1) := by
  let outer := (2 * D + 1) * first +
    2 * horizonFactor * (D - 1)
  let offset := preprocessingHorizonOffset first horizonFactor D indexBound
  let logCard := Nat.log 2 card + 1
  let last := offset + betaNat * logCard
  let h := horizonFactor * 2 ^ last
  have hoffsetFirst : first < offset := by
    dsimp only [offset, preprocessingHorizonOffset]
    have hle : first + 1 ≤
        max (first + 1) (outer + 1) := le_max_left _ _
    omega
  have hoffsetOuter : outer < offset := by
    dsimp only [offset, preprocessingHorizonOffset]
    have hle : outer + 1 ≤
        max (first + 1) (outer + 1) := le_max_right _ _
    omega
  have hindexOffset : indexBound ≤ offset := by
    dsimp only [offset, preprocessingHorizonOffset]
    omega
  have hlastOffset : offset ≤ last := by
    dsimp only [last]
    omega
  have hfirstLast : first < last := hoffsetFirst.trans_le hlastOffset
  have houterLast : outer < last := hoffsetOuter.trans_le hlastOffset
  have hpowH : 2 ^ last ≤ h := by
    dsimp only [h]
    calc
      2 ^ last = 1 * 2 ^ last := by simp
      _ ≤ horizonFactor * 2 ^ last :=
        Nat.mul_le_mul_right _ hhorizonFactor
  have hindexH : indexBound ≤ h := by
    calc
      indexBound ≤ offset := hindexOffset
      _ ≤ 2 ^ offset := PreprocessingBilu.self_le_two_pow offset
      _ ≤ 2 ^ last := Nat.pow_le_pow_right (by omega) hlastOffset
      _ ≤ h := hpowH
  have hcardPow : card ^ betaNat < 2 ^ (betaNat * logCard) := by
    have hcardLog : card < 2 ^ logCard := by
      simpa only [logCard] using
        Nat.lt_pow_succ_log_self Nat.one_lt_two card
    have hpowers := Nat.pow_lt_pow_left hcardLog (Nat.ne_of_gt hbetaNat)
    calc
      card ^ betaNat < (2 ^ logCard) ^ betaNat := hpowers
      _ = 2 ^ (logCard * betaNat) := (pow_mul 2 logCard betaNat).symm
      _ = 2 ^ (betaNat * logCard) := by rw [Nat.mul_comm logCard betaNat]
  have hsourceH : sourceEndpoint < h := by
    calc
      sourceEndpoint ≤ card ^ betaNat := hsource
      _ < 2 ^ (betaNat * logCard) := hcardPow
      _ ≤ 2 ^ last := by
        apply Nat.pow_le_pow_right (by omega)
        dsimp only [last]
        omega
      _ ≤ h := hpowH
  have hhPow : h ≤ 2 ^ (horizonFactor + last) := by
    dsimp only [h]
    calc
      horizonFactor * 2 ^ last ≤ 2 ^ horizonFactor * 2 ^ last :=
        Nat.mul_le_mul_right _
          (PreprocessingBilu.self_le_two_pow horizonFactor)
      _ = 2 ^ (horizonFactor + last) := (pow_add 2 horizonFactor last).symm
  have hlogH : Nat.log 2 h ≤ horizonFactor + last := by
    calc
      Nat.log 2 h ≤ Nat.log 2 (2 ^ (horizonFactor + last)) :=
        Nat.log_mono_right hhPow
      _ = horizonFactor + last := Nat.log_pow Nat.one_lt_two _
  have hlogCardPos : 1 ≤ logCard := by
    dsimp only [logCard]
    omega
  refine ⟨last, h, rfl, hsourceH, hindexH, hfirstLast, ?_, ?_⟩
  · simpa only [outer] using houterLast
  · dsimp only [preprocessingHorizonLogCoefficient]
    change Nat.log 2 h + 1 ≤
      (horizonFactor + offset + betaNat + 1) * logCard
    calc
      Nat.log 2 h + 1 ≤ horizonFactor + last + 1 :=
        Nat.add_le_add_right hlogH 1
      _ = horizonFactor + offset + betaNat * logCard + 1 := by
        dsimp only [last]
        omega
      _ ≤ (horizonFactor + offset + betaNat + 1) * logCard := by
        nlinarith

end

end Erdos186.CFP.IntegerTheoremAssembly

#print axioms
  Erdos186.CFP.IntegerTheoremAssembly.exists_preprocessingDyadicHorizon
#print axioms
  Erdos186.CFP.IntegerTheoremAssembly.insert_zero_subset_preprocessingInterval
#print axioms
  Erdos186.CFP.IntegerTheoremAssembly.exists_preprocessingDyadicHorizon_with_logBound
#print axioms
  Erdos186.CFP.IntegerTheoremAssembly.sourceEndpoint_le_card_pow_nat
#print axioms
  Erdos186.CFP.IntegerTheoremAssembly.natCoefficient_mul_scale_le_logb_loss
#print axioms Erdos186.CFP.IntegerTheoremAssembly.natLoss_le_logb_loss
#print axioms Erdos186.CFP.IntegerTheoremAssembly.exists_natExponent_ge
