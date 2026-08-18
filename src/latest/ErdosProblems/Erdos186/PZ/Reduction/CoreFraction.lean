/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.CanonicalScale

/-!
# A fixed retained fraction of every canonical CFP core

The canonical scale is `m / (D (log₂ m)²)`.  Consequently the CFP loss,
which is at most a fixed multiple of `scale * log₂ m`, is `o(m)`.  This file
records the exact finite threshold form used by the PZ iteration.
-/

namespace Erdos186.PZ.Reduction

open Filter
open scoped Topology

noncomputable section

/-- At a fixed ambient dimension, the selected loss of the canonical-scale
selector is eventually at most any prescribed positive fraction of the input
population.  This is the source-strength form used when the intersection
parameters have already been frozen. -/
theorem exists_scaleSelector_loss_fraction_threshold
    {beta eta exponent xi : ℝ} (C : HigherDimensionalContext beta eta)
    (d : ℕ) (hxi : 0 < xi) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ (A : Finset (LatticePoint d))
        (hA : (C.scaleSelector exponent).Eligible A),
        threshold ≤ A.card →
        (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
          xi * (A.card : ℝ) := by
  have hlog : Tendsto
      (fun m : ℕ ↦ Real.logb 2 (m : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have hlogEventually := hlog.eventually_ge_atTop
    (2 * (C.lossConstant d : ℝ) / xi)
  have hcardEventually : ∀ᶠ m : ℕ in atTop,
      2 / xi ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (2 / xi))
  have htwoEventually : ∀ᶠ m : ℕ in atTop, 2 ≤ m :=
    eventually_ge_atTop 2
  have hall : ∀ᶠ m : ℕ in atTop,
      2 * (C.lossConstant d : ℝ) / xi ≤ Real.logb 2 (m : ℝ) ∧
        2 / xi ≤ (m : ℝ) ∧ 2 ≤ m := by
    filter_upwards [hlogEventually, hcardEventually, htwoEventually] with
      m hmLog hmCard hmTwo
    exact ⟨hmLog, hmCard, hmTwo⟩
  obtain ⟨threshold, hthreshold⟩ := eventually_atTop.1 hall
  have hthresholdSelf := hthreshold threshold le_rfl
  refine ⟨threshold, hthresholdSelf.2.2, ?_⟩
  intro A hA hlarge
  have hthresholdA := hthreshold A.card hlarge
  have htwo : 2 ≤ A.card := hthresholdA.2.2
  have hlogLower : 2 * (C.lossConstant d : ℝ) / xi ≤
      Real.logb 2 (A.card : ℝ) := hthresholdA.1
  have hcardLower : 2 / xi ≤ (A.card : ℝ) :=
    hthresholdA.2.1
  have hmOne : (1 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast (by omega : 1 < A.card)
  have hmPos : (0 : ℝ) < (A.card : ℝ) := zero_lt_one.trans hmOne
  have hlogPos : 0 < Real.logb 2 (A.card : ℝ) :=
    Real.logb_pos (by norm_num) hmOne
  have hdenPos : 0 < (C.scaleDen d : ℝ) *
      (Real.logb 2 (A.card : ℝ)) ^ 2 :=
    mul_pos (by exact_mod_cast C.scaleDen_pos d) (sq_pos_of_pos hlogPos)
  have hcanonical :
      (canonicalScale C d A.card : ℝ) ≤ canonicalScaleReal C d A.card :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hdenPos.le)
  have hscale :
      (canonicalScale C d A.card : ℝ) ≤
        (A.card : ℝ) / (Real.logb 2 (A.card : ℝ)) ^ 2 := by
    rw [canonicalScaleReal] at hcanonical
    have hdenOne : (1 : ℝ) ≤ C.scaleDen d := by
      exact_mod_cast C.scaleDen_pos d
    calc
      (canonicalScale C d A.card : ℝ) ≤
          (A.card : ℝ) /
            ((C.scaleDen d : ℝ) *
              (Real.logb 2 (A.card : ℝ)) ^ 2) := hcanonical
      _ ≤ (A.card : ℝ) / (Real.logb 2 (A.card : ℝ)) ^ 2 := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
          (sq_pos_of_pos hlogPos)
        nlinarith [sq_pos_of_pos hlogPos]
  have hloss :=
    ((C.scaleSelector exponent).input A hA).selectedCFP_loss_le
  rw [C.scaleSelector_input_scale hA] at hloss
  have hscaled :
      (C.lossConstant d : ℝ) * (canonicalScale C d A.card : ℝ) *
          Real.logb 2 (A.card : ℝ) ≤
        xi * (A.card : ℝ) / 2 := by
    calc
      (C.lossConstant d : ℝ) * (canonicalScale C d A.card : ℝ) *
            Real.logb 2 (A.card : ℝ) ≤
          (C.lossConstant d : ℝ) *
              ((A.card : ℝ) /
                (Real.logb 2 (A.card : ℝ)) ^ 2) *
                Real.logb 2 (A.card : ℝ) := by
        gcongr
      _ = (C.lossConstant d : ℝ) * (A.card : ℝ) /
          Real.logb 2 (A.card : ℝ) := by
        field_simp
      _ ≤ xi * (A.card : ℝ) / 2 := by
        apply (div_le_iff₀ hlogPos).2
        have hmul := mul_le_mul_of_nonneg_right hlogLower
          (mul_nonneg (half_pos hxi).le hmPos.le)
        have hxiNe : xi ≠ 0 := hxi.ne'
        field_simp [hxiNe] at hmul
        nlinarith
  have hone : (1 : ℝ) ≤ xi * (A.card : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcardLower hxi.le
    field_simp at hmul ⊢
    nlinarith
  change (((C.scaleSelector exponent).input A hA).selectedCFP.loss : ℝ) ≤
    xi * (A.card : ℝ)
  linarith

/-- The arbitrary-fraction loss threshold is uniform over every ambient
dimension below a fixed finite ceiling. -/
theorem exists_scaleSelector_loss_fraction_threshold_boundedDimension
    {beta eta exponent xi : ℝ} (C : HigherDimensionalContext beta eta)
    (R : ℕ) (hxi : 0 < xi) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ {d : ℕ}, d ≤ R →
      ∀ (A : Finset (LatticePoint d))
        (hA : (C.scaleSelector exponent).Eligible A),
        threshold ≤ A.card →
        (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
          xi * (A.card : ℝ) := by
  choose t ht using fun d ↦
    exists_scaleSelector_loss_fraction_threshold
      (exponent := exponent) C d hxi
  let threshold := 2 + ∑ d ∈ Finset.range (R + 1), t d
  refine ⟨threshold, by simp [threshold], ?_⟩
  intro d hd A hA hlarge
  have hdmem : d ∈ Finset.range (R + 1) := by simp; omega
  have hdt : t d ≤ ∑ i ∈ Finset.range (R + 1), t i :=
    Finset.single_le_sum (fun i hi ↦ Nat.zero_le (t i)) hdmem
  exact (ht d).2 A hA (by dsimp [threshold] at hlarge; omega)

/-- A selected loss of at most `xi` times the population leaves at least the
complementary fraction in the identified structured core. -/
theorem one_sub_fraction_card_le_identifiedCore_of_loss
    {beta eta exponent xi : ℝ} {C : HigherDimensionalContext beta eta}
    {d : ℕ} (A : Finset (LatticePoint d))
    (hA : (C.scaleSelector exponent).Eligible A)
    (hxi : xi ≤ 1)
    (hloss : (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
      xi * (A.card : ℝ)) :
    (1 - xi) * (A.card : ℝ) ≤
      (((C.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) := by
  let S := (C.scaleSelector exponent).chosen A hA
  have hmnonneg : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hlossNat : S.loss ≤ A.card := by
    exact_mod_cast hloss.trans (mul_le_of_le_one_left hmnonneg hxi)
  have hcoreNat : A.card - S.loss ≤ S.core.card :=
    S.witness.card_sub_loss_le_core
  have hcoreReal : (A.card : ℝ) - (S.loss : ℝ) ≤
      (S.core.card : ℝ) := by
    rw [← Nat.cast_sub hlossNat]
    exact_mod_cast hcoreNat
  change (1 - xi) * (A.card : ℝ) ≤ (S.identifiedCore.card : ℝ)
  rw [S.card_identifiedCore]
  linarith

/-- At a fixed ambient dimension, the selected loss of the canonical-scale
selector is eventually at most half the input population. -/
theorem exists_scaleSelector_loss_half_threshold
    {beta eta exponent : ℝ} (C : HigherDimensionalContext beta eta)
    (d : ℕ) :
    ∃ threshold : ℕ, 4 ≤ threshold ∧
      ∀ (A : Finset (LatticePoint d))
        (hA : (C.scaleSelector exponent).Eligible A),
        threshold ≤ A.card →
        (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
          (A.card : ℝ) / 2 := by
  have hlog : Tendsto
      (fun m : ℕ ↦ Real.logb 2 (m : ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have heventually := hlog.eventually_ge_atTop
    (4 * (C.lossConstant d : ℝ))
  obtain ⟨t, ht⟩ := eventually_atTop.1 heventually
  refine ⟨max 4 t, le_max_left _ _, ?_⟩
  intro A hA hlarge
  have hfour : 4 ≤ A.card := (le_max_left 4 t).trans hlarge
  have htA : t ≤ A.card := (le_max_right 4 t).trans hlarge
  have hlogLower : 4 * (C.lossConstant d : ℝ) ≤
      Real.logb 2 (A.card : ℝ) := ht A.card htA
  have hmOne : (1 : ℝ) < (A.card : ℝ) := by exact_mod_cast (by omega : 1 < A.card)
  have hmPos : (0 : ℝ) < (A.card : ℝ) := zero_lt_one.trans hmOne
  have hlogPos : 0 < Real.logb 2 (A.card : ℝ) :=
    Real.logb_pos (by norm_num) hmOne
  have hdenPos : 0 < (C.scaleDen d : ℝ) *
      (Real.logb 2 (A.card : ℝ)) ^ 2 :=
    mul_pos (by exact_mod_cast C.scaleDen_pos d) (sq_pos_of_pos hlogPos)
  have hcanonical :
      (canonicalScale C d A.card : ℝ) ≤ canonicalScaleReal C d A.card :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg _) hdenPos.le)
  have hscale :
      (canonicalScale C d A.card : ℝ) ≤
        (A.card : ℝ) / (Real.logb 2 (A.card : ℝ)) ^ 2 := by
    rw [canonicalScaleReal] at hcanonical
    have hdenOne : (1 : ℝ) ≤ C.scaleDen d := by
      exact_mod_cast C.scaleDen_pos d
    calc
      (canonicalScale C d A.card : ℝ) ≤
          (A.card : ℝ) /
            ((C.scaleDen d : ℝ) *
              (Real.logb 2 (A.card : ℝ)) ^ 2) := hcanonical
      _ ≤ (A.card : ℝ) / (Real.logb 2 (A.card : ℝ)) ^ 2 := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (sq_pos_of_pos hlogPos)
        nlinarith [sq_pos_of_pos hlogPos]
  have hloss :=
    ((C.scaleSelector exponent).input A hA).selectedCFP_loss_le
  rw [C.scaleSelector_input_scale hA] at hloss
  have hscaled :
      (C.lossConstant d : ℝ) * (canonicalScale C d A.card : ℝ) *
          Real.logb 2 (A.card : ℝ) ≤
        (A.card : ℝ) / 4 := by
    calc
      (C.lossConstant d : ℝ) * (canonicalScale C d A.card : ℝ) *
            Real.logb 2 (A.card : ℝ) ≤
          (C.lossConstant d : ℝ) *
              ((A.card : ℝ) /
                (Real.logb 2 (A.card : ℝ)) ^ 2) *
                Real.logb 2 (A.card : ℝ) := by
        gcongr
      _ = (C.lossConstant d : ℝ) * (A.card : ℝ) /
          Real.logb 2 (A.card : ℝ) := by
        field_simp
      _ ≤ (A.card : ℝ) / 4 := by
        apply (div_le_iff₀ hlogPos).2
        have hmul := mul_le_mul_of_nonneg_right hlogLower hmPos.le
        nlinarith
  have hone : (1 : ℝ) ≤ (A.card : ℝ) / 4 := by
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by exact_mod_cast hfour)
  change (((C.scaleSelector exponent).input A hA).selectedCFP.loss : ℝ) ≤
    (A.card : ℝ) / 2
  linarith

/-- The half-loss threshold can be chosen uniformly over every ambient
dimension at most a prescribed finite ceiling. -/
theorem exists_scaleSelector_loss_half_threshold_boundedDimension
    {beta eta exponent : ℝ} (C : HigherDimensionalContext beta eta)
    (R : ℕ) :
    ∃ threshold : ℕ, 4 ≤ threshold ∧
      ∀ {d : ℕ}, d ≤ R →
      ∀ (A : Finset (LatticePoint d))
        (hA : (C.scaleSelector exponent).Eligible A),
        threshold ≤ A.card →
        (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
          (A.card : ℝ) / 2 := by
  choose t ht using fun d ↦
    exists_scaleSelector_loss_half_threshold (exponent := exponent) C d
  let threshold := 4 + ∑ d ∈ Finset.range (R + 1), t d
  refine ⟨threshold, by simp [threshold], ?_⟩
  intro d hd A hA hlarge
  have hdmem : d ∈ Finset.range (R + 1) := by simp; omega
  have hdt : t d ≤ ∑ i ∈ Finset.range (R + 1), t i :=
    Finset.single_le_sum (fun i hi ↦ Nat.zero_le (t i)) hdmem
  exact (ht d).2 A hA (by dsimp [threshold] at hlarge; omega)

/-- Beyond the uniform loss threshold, at least half of the population lies
in the identified structured core selected at the canonical scale. -/
theorem scaleSelector_half_card_le_identifiedCore
    {beta eta exponent : ℝ} {C : HigherDimensionalContext beta eta}
    {R d : ℕ} {threshold : ℕ}
    (hloss : ∀ {e : ℕ}, e ≤ R →
      ∀ (A : Finset (LatticePoint e))
        (hA : (C.scaleSelector exponent).Eligible A),
        threshold ≤ A.card →
        (((C.scaleSelector exponent).chosen A hA).loss : ℝ) ≤
          (A.card : ℝ) / 2)
    (hd : d ≤ R) (A : Finset (LatticePoint d))
    (hA : (C.scaleSelector exponent).Eligible A)
    (hlarge : threshold ≤ A.card) :
    (1 / 2 : ℝ) * (A.card : ℝ) ≤
      (((C.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) := by
  let S := (C.scaleSelector exponent).chosen A hA
  have hlossReal : (S.loss : ℝ) ≤ (A.card : ℝ) / 2 :=
    hloss hd A hA hlarge
  have hlossNat : S.loss ≤ A.card := by
    have hmnonneg : (0 : ℝ) ≤ (A.card : ℝ) := Nat.cast_nonneg _
    exact_mod_cast hlossReal.trans (by nlinarith : (A.card : ℝ) / 2 ≤ A.card)
  have hcoreNat : A.card - S.loss ≤ S.core.card :=
    S.witness.card_sub_loss_le_core
  have hcoreReal : (A.card : ℝ) - (S.loss : ℝ) ≤ (S.core.card : ℝ) := by
    rw [← Nat.cast_sub hlossNat]
    exact_mod_cast hcoreNat
  change (1 / 2 : ℝ) * (A.card : ℝ) ≤ (S.identifiedCore.card : ℝ)
  rw [S.card_identifiedCore]
  linarith

/-- A half-population core has enough room for the two balanced pools used
by Theorem 4 once the density parameter is at most `1/8`.  The explicit
`16` threshold absorbs the two discarded endpoints and the natural-number
division in the public post-CFP interface. -/
theorem density_mul_card_le_half_core_sub_two
    {delta : ℝ} {population core : ℕ}
    (hdelta : delta ≤ 1 / 8)
    (hlarge : 16 ≤ population)
    (hhalf : (1 / 2 : ℝ) * (population : ℝ) ≤ (core : ℝ)) :
    delta * (population : ℝ) ≤ ((((core - 2) / 2 : ℕ) : ℝ)) := by
  have hpopCore : population ≤ 2 * core := by
    exact_mod_cast (show (population : ℝ) ≤ 2 * core by nlinarith)
  have hcoreLarge : 8 ≤ core := by omega
  have hnat : population ≤ 8 * ((core - 2) / 2) := by omega
  have hdeltaPop : delta * (population : ℝ) ≤ (population : ℝ) / 8 := by
    have hpopNonneg : (0 : ℝ) ≤ population := Nat.cast_nonneg _
    nlinarith
  calc
    delta * (population : ℝ) ≤ (population : ℝ) / 8 := hdeltaPop
    _ ≤ ((((core - 2) / 2 : ℕ) : ℝ)) := by
      have hnatReal : (population : ℝ) ≤
          8 * ((((core - 2) / 2 : ℕ) : ℝ)) := by exact_mod_cast hnat
      nlinarith

end

end Erdos186.PZ.Reduction
