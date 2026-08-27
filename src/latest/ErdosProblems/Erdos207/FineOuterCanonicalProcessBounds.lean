/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCanonicalScheduleBounds

/-!
# Process bounds from a canonical outer corridor

This file removes the remaining schedule-valued hypotheses of the sharp
initial-process theorem.  Once a corridor supplies a uniform lower degree,
upper degree, availability floor, and schedule order, elementary monotonicity
controls both deletion rates, both variance budgets, and all positivity and
effective-supply clauses.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def fineOuterUpperJump (_Umax : ℕ) : ℕ := 1

def fineOuterUpperRateBound (reserve Umax : ℕ) : ℝ :=
  (12 * Umax : ℕ) / (reserve : ℕ)

def fineOuterLowerRateBound (Dcut Umax Kinc : ℕ) : ℝ :=
  ((2 * Umax ^ 2 + Kinc : ℕ) : ℝ) / (Dcut - Umax : ℕ)

def fineOuterVarianceBound
    (Dcut Umax Kpair Kglobal Kinc : ℕ) (jUpper jLower : ℝ) : ℝ :=
  (2 * ((Dcut : ℝ)⁻¹ * Umax *
      ((3 + Kpair : ℕ) * (3 * Umax + Kglobal))) + 2 * jUpper ^ 2) +
  (2 * ((Dcut : ℝ)⁻¹ *
      ((3 + Kpair : ℕ) * (Umax * (3 * Umax) + Kinc))) +
        2 * jLower ^ 2)

lemma sharpScheduledPairUpperRate_le_fineOuterRateBound
    {E reserve d u Umax : ℕ}
    (hreservePos : 0 < reserve) (hreserve : reserve ≤ E)
    (huPos : 0 < u) (hdu : d ≤ u) (hu : u ≤ Umax)
    (hlarge : 12 * Umax ≤ reserve) :
    sharpScheduledPairUpperRate (E * u / 3) d u ≤
      fineOuterUpperRateBound reserve Umax := by
  let M := E * u / 3
  have hUpos : 0 < Umax := huPos.trans_le hu
  have hprod : 12 ≤ E * u := by
    calc
      12 ≤ 12 * Umax * u := by nlinarith
      _ ≤ E * u := Nat.mul_le_mul_right u (hlarge.trans hreserve)
  have hMfour : 4 ≤ M := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
    simpa only [M] using hprod
  have hlt : E * u < (M + 1) * 3 := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).1
    simpa only [M] using Nat.lt_succ_self (E * u / 3)
  have hfour : E * u ≤ 4 * M := by omega
  have hloss : 3 * d - 2 - u ≤ 3 * u := by omega
  have hcross : reserve * (d * (3 * d - 2 - u)) ≤
      (12 * Umax) * M := by
    calc
      reserve * (d * (3 * d - 2 - u)) ≤ reserve * (u * (3 * u)) := by
        gcongr
      _ ≤ E * (u * (3 * u)) := by gcongr
      _ = 3 * u * (E * u) := by ring
      _ ≤ 3 * u * (4 * M) := by gcongr
      _ ≤ (12 * Umax) * M := by nlinarith
  have hMpos : 0 < M := by omega
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hRreal : (0 : ℝ) < reserve := by exact_mod_cast hreservePos
  unfold sharpScheduledPairUpperRate fineOuterUpperRateBound
  rw [show (M : ℝ)⁻¹ * d * (3 * d - 2 - u : ℕ) =
      ((d * (3 * d - 2 - u) : ℕ) : ℝ) / M by
        rw [div_eq_mul_inv]
        push_cast
        ring]
  rw [div_le_div_iff₀ hMreal hRreal]
  exact_mod_cast (by simpa [Nat.mul_comm] using hcross)

lemma fineOuterUpperRateBound_le_one
    {reserve Umax : ℕ} (hreservePos : 0 < reserve)
    (hlarge : 12 * Umax ≤ reserve) :
    fineOuterUpperRateBound reserve Umax ≤ 1 := by
  unfold fineOuterUpperRateBound
  rw [div_le_one (by exact_mod_cast hreservePos)]
  exact_mod_cast hlarge

/-- A single cross-multiplied scalar inequality makes the conservative lower
deletion rate no larger than the uniform degree floor. -/
lemma sharpScheduledPairLowerRate_le_uniformFloor
    {D u K dmin Umax Dcut : ℕ}
    (huPos : 0 < u) (hu : u ≤ Umax) (hD : Dcut ≤ D)
    (hgap : Umax < Dcut)
    (hscalar : 2 * Umax ^ 2 + K ≤ dmin * (Dcut - Umax)) :
    sharpScheduledPairLowerRate D u K ≤ dmin := by
  have huD : u < D := hu.trans_lt (hgap.trans_le hD)
  have hdenNat : 0 < D - u := Nat.sub_pos_of_lt huD
  have hden : (0 : ℝ) < (D - u : ℕ) := by exact_mod_cast hdenNat
  have hnum : u * (2 * u) + K ≤ 2 * Umax ^ 2 + K := by
    nlinarith [Nat.mul_le_mul hu hu]
  have hdenMono : Dcut - Umax ≤ D - u := by omega
  have hcross : u * (2 * u) + K ≤ dmin * (D - u) :=
    hnum.trans <| hscalar.trans <| Nat.mul_le_mul_left dmin hdenMono
  rw [sharpScheduledPairLowerRate]
  have hrw : (((D - u : ℕ) : ℝ)⁻¹) * ((u : ℝ) * (2 * u : ℕ) + K) =
      ((u * (2 * u) + K : ℕ) : ℝ) / (D - u : ℕ) := by
    rw [div_eq_mul_inv]
    push_cast
    ring
  rw [hrw, div_le_iff₀ hden]
  exact_mod_cast hcross

lemma sharpScheduledPairLowerRate_le_fineOuterLowerRateBound
    {D u K Umax Dcut : ℕ}
    (hu : u ≤ Umax) (hD : Dcut ≤ D) (hgap : Umax < Dcut) :
    sharpScheduledPairLowerRate D u K ≤
      fineOuterLowerRateBound Dcut Umax K := by
  have huD : u < D := hu.trans_lt (hgap.trans_le hD)
  have hdenNat : 0 < D - u := Nat.sub_pos_of_lt huD
  have hcutNat : 0 < Dcut - Umax := Nat.sub_pos_of_lt hgap
  have hden : (0 : ℝ) < (D - u : ℕ) := by exact_mod_cast hdenNat
  have hcut : (0 : ℝ) < (Dcut - Umax : ℕ) := by exact_mod_cast hcutNat
  have hnum : u * (2 * u) + K ≤ 2 * Umax ^ 2 + K := by
    nlinarith [Nat.mul_le_mul hu hu]
  have hdenMono : Dcut - Umax ≤ D - u := by omega
  rw [sharpScheduledPairLowerRate, fineOuterLowerRateBound]
  have hlhs : (((D - u : ℕ) : ℝ)⁻¹) *
      ((u : ℝ) * (2 * u : ℕ) + K) =
      ((u * (2 * u) + K : ℕ) : ℝ) / (D - u : ℕ) := by
    rw [div_eq_mul_inv]
    push_cast
    ring
  rw [hlhs, div_le_div_iff₀ hden hcut]
  exact_mod_cast (Nat.mul_le_mul hnum hdenMono)

lemma sharpScheduledPairUpperVariance_le_fineOuterVarianceBound
    {D u Dcut Umax Kpair Kglobal Kinc : ℕ} {jUpper jLower r : ℝ}
    (hDcut : 0 < Dcut) (hD : Dcut ≤ D) (hu : u ≤ Umax)
    (hr0 : 0 ≤ r) (hr : r ≤ jUpper) :
    sharpScheduledPairUpperVariance D u Kpair Kglobal r ≤
      fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc jUpper jLower := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hDcut.trans_le hD
  have hcutPos : (0 : ℝ) < Dcut := by exact_mod_cast hDcut
  have hinv : (D : ℝ)⁻¹ ≤ (Dcut : ℝ)⁻¹ :=
    (inv_le_inv₀ hDpos hcutPos).mpr (by exact_mod_cast hD)
  unfold sharpScheduledPairUpperVariance fineOuterVarianceBound
  push_cast
  have hmain :
      2 * ((D : ℝ)⁻¹ * u *
          (((3 : ℝ) + Kpair) * (3 * u + Kglobal))) + 2 * r ^ 2 ≤
        2 * ((Dcut : ℝ)⁻¹ * Umax *
          (((3 : ℝ) + Kpair) * (3 * Umax + Kglobal))) +
            2 * jUpper ^ 2 := by
    gcongr
  have hinvCut : 0 ≤ (Dcut : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  calc
    _ ≤ 2 * ((Dcut : ℝ)⁻¹ * Umax *
          (((3 : ℝ) + Kpair) * (3 * Umax + Kglobal))) +
            2 * jUpper ^ 2 := hmain
    _ ≤ (2 * ((Dcut : ℝ)⁻¹ * Umax *
          (((3 : ℝ) + Kpair) * (3 * Umax + Kglobal))) +
            2 * jUpper ^ 2) +
        (2 * ((Dcut : ℝ)⁻¹ *
          (((3 : ℝ) + Kpair) * (Umax * (3 * Umax) + Kinc))) +
            2 * jLower ^ 2) := by
      apply le_add_of_nonneg_right
      apply add_nonneg <;> positivity

lemma sharpScheduledPairLowerVariance_le_fineOuterVarianceBound
    {D u Dcut Umax Kpair Kglobal Kinc : ℕ} {jUpper jLower r : ℝ}
    (hDcut : 0 < Dcut) (hD : Dcut ≤ D) (hu : u ≤ Umax)
    (hr0 : 0 ≤ r) (hr : r ≤ jLower) :
    sharpScheduledPairLowerVariance D u Kpair Kinc r ≤
      fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc jUpper jLower := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hDcut.trans_le hD
  have hcutPos : (0 : ℝ) < Dcut := by exact_mod_cast hDcut
  have hinv : (D : ℝ)⁻¹ ≤ (Dcut : ℝ)⁻¹ :=
    (inv_le_inv₀ hDpos hcutPos).mpr (by exact_mod_cast hD)
  unfold sharpScheduledPairLowerVariance fineOuterVarianceBound
  push_cast
  have hmain :
      2 * ((D : ℝ)⁻¹ *
          (((3 : ℝ) + Kpair) * (u * (3 * u) + Kinc))) + 2 * r ^ 2 ≤
        2 * ((Dcut : ℝ)⁻¹ *
          (((3 : ℝ) + Kpair) * (Umax * (3 * Umax) + Kinc))) +
            2 * jLower ^ 2 := by
    gcongr
  have hinvCut : 0 ≤ (Dcut : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  calc
    _ ≤ 2 * ((Dcut : ℝ)⁻¹ *
          (((3 : ℝ) + Kpair) * (Umax * (3 * Umax) + Kinc))) +
            2 * jLower ^ 2 := hmain
    _ ≤ (2 * ((Dcut : ℝ)⁻¹ * Umax *
          (((3 : ℝ) + Kpair) * (3 * Umax + Kglobal))) +
            2 * jUpper ^ 2) +
        (2 * ((Dcut : ℝ)⁻¹ *
          (((3 : ℝ) + Kpair) * (Umax * (3 * Umax) + Kinc))) +
            2 * jLower ^ 2) := by
      apply le_add_of_nonneg_left
      apply add_nonneg <;> positivity

/-- All dynamic side conditions used by
`outerSharpRecursive_absorberInitialProductLaw`. -/
structure FineOuterProcessBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ)
    (Kinc K fuel dmin Umax Dcut Kpair Kglobal reserve : ℕ) :
    Prop where
  upper_jump : ∀ i, i < fuel →
    sharpScheduledPairUpperRate
      (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i)
      (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i)
      (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i) ≤
        fineOuterUpperJump Umax
  lower_death : ∀ i, i < fuel →
    sharpScheduledPairLowerRate
      (outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i)
      (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i) Kinc ≤
        outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i
  variance_upper : ∀ i, i < fuel →
    sharpScheduledPairUpperVariance
      (outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i)
      (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i)
      Kpair Kglobal
      (sharpScheduledPairUpperRate
        (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i)
        (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i)
        (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i)) ≤
      fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc
        (fineOuterUpperRateBound reserve Umax)
        (fineOuterLowerRateBound Dcut Umax Kinc)
  variance_lower : ∀ i, i < fuel →
    sharpScheduledPairLowerVariance
      (outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i)
      (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i)
      Kpair Kinc
      (sharpScheduledPairLowerRate
        (outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i)
        (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i) Kinc) ≤
      fineOuterVarianceBound Dcut Umax Kpair Kglobal Kinc
        (fineOuterUpperRateBound reserve Umax)
        (fineOuterLowerRateBound Dcut Umax Kinc)
  degree_le_availability : ∀ i, i < fuel →
    outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i ≤
      outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i
  effective : ∀ i, i < fuel →
      outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i - 3 * K <
      outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i
  upper_availability_pos : ∀ i, i < fuel →
    0 < outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i
  half : ∀ i, i < fuel →
      2 * (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i -
      3 * K) ≤
        outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i
  three : ∀ i, i < fuel →
    3 ≤ outerSharpEligiblePairs H X i *
      outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i

theorem fineOuterProcessBounds_of_uniform
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ)
    (Kinc K fuel dmin Umax Dcut Kpair Kglobal reserve : ℕ)
    (hreserveSix : 6 ≤ reserve) (hdminPos : 0 < dmin)
    (hDcutPos : 0 < Dcut) (hgap : Umax < Dcut)
    (hupperScalar : 12 * Umax ≤ reserve)
    (hscalar : 2 * Umax ^ 2 + Kinc ≤ dmin * (Dcut - Umax))
    (hbounds : ∀ i, i ≤ fuel →
      dmin ≤ outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i ∧
      outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i ≤ Umax ∧
      Dcut ≤ outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i)
    (horder : ∀ i, i ≤ fuel →
      outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i ≤
        outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i)
    (hreserve : ∀ i, i ≤ fuel → reserve ≤ outerSharpEligiblePairs H X i) :
    FineOuterProcessBounds H X upper₀ lower₀ buffer Kinc K fuel dmin Umax
      Dcut Kpair Kglobal reserve := by
  have hpoint : ∀ i, i < fuel →
      let d := outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i
      let u := outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i
      let D := outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i
      let M := outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i
      0 < d ∧ 0 < u ∧ d ≤ u ∧ u ≤ Umax ∧ Dcut ≤ D ∧
        0 < M ∧ u < M ∧ 2 * d ≤ M := by
    intro i hi
    dsimp only
    have hb := hbounds i hi.le
    have hdu := horder i hi.le
    have hdPos := hdminPos.trans_le hb.1
    have huPos := hdPos.trans_le hdu
    have hE := hreserveSix.trans (hreserve i hi.le)
    rw [outerSharpUpperAvailability_eq]
    have hMpos : 0 < outerSharpEligiblePairs H X i *
        outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i / 3 := by
      apply Nat.div_pos
      · nlinarith [Nat.mul_le_mul hE (Nat.one_le_iff_ne_zero.mpr huPos.ne')]
      · norm_num
    have htwoUM : 2 * outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i ≤
        outerSharpEligiblePairs H X i *
          outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i / 3 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
      nlinarith [Nat.mul_le_mul_right
        (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i) hE]
    have htwoM : 2 * outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i ≤
        outerSharpEligiblePairs H X i *
          outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i / 3 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
      nlinarith [Nat.mul_le_mul
        (show 6 ≤ outerSharpEligiblePairs H X i from hE) hdu]
    have huM : outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i <
        outerSharpEligiblePairs H X i *
          outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i / 3 := by
      calc
        outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i <
            2 * outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i := by
              omega
        _ ≤ _ := htwoUM
    exact ⟨hdPos, huPos, hdu, hb.2.1, hb.2.2, hMpos, huM, htwoM⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hp := hpoint i hi
    have hr : sharpScheduledPairUpperRate
        (outerSharpUpperAvailability H X upper₀ lower₀ buffer Kinc i)
        (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i)
        (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i) ≤
          fineOuterUpperRateBound reserve Umax := by
      rw [outerSharpUpperAvailability_eq]
      exact sharpScheduledPairUpperRate_le_fineOuterRateBound
        (by omega) (hreserve i hi.le) hp.2.1 hp.2.2.1 hp.2.2.2.1
          hupperScalar
    exact hr.trans (by
      simpa [fineOuterUpperJump] using
        fineOuterUpperRateBound_le_one (by omega) hupperScalar)
  · intro i hi
    have hp := hpoint i hi
    have hrate : sharpScheduledPairLowerRate
        (outerSharpLowerAvailability H X upper₀ lower₀ buffer Kinc i)
        (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i) Kinc ≤
          (dmin : ℝ) := sharpScheduledPairLowerRate_le_uniformFloor hp.2.1
            hp.2.2.2.1 hp.2.2.2.2.1 hgap hscalar
    have hfloor : (dmin : ℝ) ≤
        outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i := by
      exact_mod_cast (hbounds i hi.le).1
    exact hrate.trans hfloor
  · intro i hi
    have hp := hpoint i hi
    apply sharpScheduledPairUpperVariance_le_fineOuterVarianceBound
      hDcutPos hp.2.2.2.2.1 hp.2.2.2.1
      (sharpScheduledPairUpperRate_nonneg _ _ _)
    rw [outerSharpUpperAvailability_eq]
    exact sharpScheduledPairUpperRate_le_fineOuterRateBound
      (by omega) (hreserve i hi.le) hp.2.1 hp.2.2.1 hp.2.2.2.1
        hupperScalar
  · intro i hi
    have hp := hpoint i hi
    apply sharpScheduledPairLowerVariance_le_fineOuterVarianceBound
      hDcutPos hp.2.2.2.2.1 hp.2.2.2.1
      (sharpScheduledPairLowerRate_nonneg _ _ _)
    exact sharpScheduledPairLowerRate_le_fineOuterLowerRateBound
      hp.2.2.2.1 hp.2.2.2.2.1 hgap
  · intro i hi
    exact (hpoint i hi).2.2.1.trans (hpoint i hi).2.2.2.2.2.2.1.le
  · intro i hi
    have hp := hpoint i hi
    exact (Nat.sub_le _ _).trans_lt (hp.2.2.1.trans_lt hp.2.2.2.2.2.2.1)
  · intro i hi
    exact (hpoint i hi).2.2.2.2.2.1
  · intro i hi
    exact (Nat.mul_le_mul_left 2 (Nat.sub_le _ _)).trans
      (hpoint i hi).2.2.2.2.2.2.2
  · intro i hi
    have hp := hpoint i hi
    nlinarith [Nat.mul_le_mul (hreserveSix.trans (hreserve i hi.le))
      (show 1 ≤ outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i from
        Nat.one_le_iff_ne_zero.mpr hp.1.ne')]

end

end Erdos207
