/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCertifiedInitialProductLaw

/-!
# Static arithmetic for the canonical outer phase

These lemmas replace real floors and ceilings by coarse integral scales.
They also prove the two cubic-cancellation scalars from the elementary facts
that the protected first vortex level has size at most half the ambient
order and that the initial eligible-pair graph has density close to one.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def fineOuterCoarseDegreeFloor (outside t : ℕ) : ℕ :=
  outside / (16 * t ^ 2)

structure FineFirstOutsideFacts {n : ℕ} (U : Finset (Fin n)) : Prop where
  positive : 0 < (Finset.univ \ U).card
  le_ambient : (Finset.univ \ U).card ≤ n
  ambient_le_twice : n ≤ 2 * (Finset.univ \ U).card
  four_le : 4 ≤ (Finset.univ \ U).card

lemma fineFirstOutsideFacts_of_levelSmall
    {n : ℕ} (U : Finset (Fin n)) (hsmall : 2 * U.card + 8 ≤ n) :
    FineFirstOutsideFacts U := by
  have hU : U.card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ U
  have hout : (Finset.univ \ U).card = n - U.card := by
    simp [Finset.card_sdiff, Fintype.card_fin]
  constructor <;> rw [hout] <;> omega

lemma fineOuterDegreeCeil_eq (outside : ℕ) :
    fineOuterDegreeCeil outside = 5 * outside := by
  unfold fineOuterDegreeCeil nonnegativeNatCeil
  rw [max_eq_right (show (0 : ℝ) ≤ 5 * (outside : ℝ) by positivity)]
  rw [show 5 * (outside : ℝ) = ((5 * outside : ℕ) : ℝ) by norm_num,
    Nat.ceil_natCast]

lemma fineOuterCoarseDegreeFloor_pos
    {outside t : ℕ} (ht : 0 < t) (hlarge : 16 * t ^ 2 ≤ outside) :
    0 < fineOuterCoarseDegreeFloor outside t := by
  unfold fineOuterCoarseDegreeFloor
  exact Nat.div_pos hlarge (by positivity)

lemma fineOuterCoarseDegreeFloor_le
    {outside t : ℕ} (ht : 0 < t) :
    fineOuterCoarseDegreeFloor outside t ≤ fineOuterDegreeFloor outside t := by
  unfold fineOuterCoarseDegreeFloor fineOuterDegreeFloor nonnegativeNatFloor
  apply Nat.le_floor
  rw [max_eq_right (by positivity : (0 : ℝ) ≤
    (outside : ℝ) / (8 * (t : ℝ) ^ 2))]
  have hden : 0 < 16 * t ^ 2 := by positivity
  have hmul : outside / (16 * t ^ 2) * (16 * t ^ 2) ≤ outside :=
    Nat.div_mul_le_self outside (16 * t ^ 2)
  have hmulReal :
      ((outside / (16 * t ^ 2) : ℕ) : ℝ) *
          (8 * (t : ℝ) ^ 2) ≤ outside := by
    exact_mod_cast (show outside / (16 * t ^ 2) * (8 * t ^ 2) ≤ outside by
      calc
        outside / (16 * t ^ 2) * (8 * t ^ 2) ≤
            outside / (16 * t ^ 2) * (16 * t ^ 2) := by gcongr <;> omega
        _ ≤ outside := hmul)
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (t : ℝ) ^ 2)).2
    hmulReal

/-- Once the coarse quotient is positive, its one-unit division loss costs
at most a factor two. -/
lemma outside_le_32_mul_sq_mul_coarseDegree
    {outside t : ℕ} (ht : 0 < t)
    (hd : 0 < fineOuterCoarseDegreeFloor outside t) :
    outside ≤ 32 * t ^ 2 * fineOuterCoarseDegreeFloor outside t := by
  let d := fineOuterCoarseDegreeFloor outside t
  let den := 16 * t ^ 2
  have hden : 0 < den := by dsimp only [den]; positivity
  have hlt : outside < (d + 1) * den := by
    apply (Nat.div_lt_iff_lt_mul hden).1
    simpa only [d, den, fineOuterCoarseDegreeFloor] using
      Nat.lt_succ_self (outside / (16 * t ^ 2))
  have htwo : d + 1 ≤ 2 * d := by omega
  calc
    outside ≤ (d + 1) * den := hlt.le
    _ ≤ (2 * d) * den := Nat.mul_le_mul_right den htwo
    _ = 32 * t ^ 2 * fineOuterCoarseDegreeFloor outside t := by
      simp only [d, den]
      ring

/-- Cubic-cancellation scale: `E²` is absorbed by `64 t² n³ d`. -/
lemma fineOuter_pair_scale_scalar
    {E outside t n : ℕ}
    (hE : E ≤ outside ^ 2) (houtn : outside ≤ n)
    (hnout : n ≤ 2 * outside) (ht : 0 < t)
    (hd : 0 < fineOuterCoarseDegreeFloor outside t) :
    (E : ℝ≥0) ^ 2 ≤
      (64 * t ^ 2 : ℕ) * (n : ℝ≥0) ^ 3 *
        fineOuterCoarseDegreeFloor outside t := by
  have hcross := outside_le_32_mul_sq_mul_coarseDegree ht hd
  have hE' : (E : ℝ≥0) ≤ (outside : ℝ≥0) ^ 2 := by exact_mod_cast hE
  have houtn' : (outside : ℝ≥0) ≤ n := by exact_mod_cast houtn
  have hnout' : (n : ℝ≥0) ≤ 2 * outside := by exact_mod_cast hnout
  have hcross' : (outside : ℝ≥0) ≤
      (32 * t ^ 2 : ℕ) * fineOuterCoarseDegreeFloor outside t := by
    exact_mod_cast hcross
  calc
    (E : ℝ≥0) ^ 2 ≤ ((outside : ℝ≥0) ^ 2) ^ 2 :=
      pow_le_pow_left' hE' 2
    _ = (outside : ℝ≥0) ^ 3 * outside := by ring
    _ ≤ (n : ℝ≥0) ^ 3 * outside := by gcongr
    _ ≤ (n : ℝ≥0) ^ 3 * (2 * outside) := by
      gcongr
      simpa [two_mul] using
        (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ outside by positivity))
    _ ≤ (n : ℝ≥0) ^ 3 *
        (2 * ((32 * t ^ 2 : ℕ) *
          fineOuterCoarseDegreeFloor outside t)) := by gcongr
    _ = (64 * t ^ 2 : ℕ) * (n : ℝ≥0) ^ 3 *
        fineOuterCoarseDegreeFloor outside t := by push_cast; ring

/-- A `1%` eligible-pair defect and a half-sized protected set give a fixed
quadratic comparison between the ambient order and the initial clock. -/
lemma fineOuter_quadratic_scalar
    {E outside n : ℕ} {epsilon : ℝ≥0}
    (hnout : n ≤ 2 * outside)
    (hepsilon : (epsilon : ℝ) ≤ 1 / 100)
    (hpair : (outside : ℝ) ^ 2 * (1 - 3 * epsilon) ≤ 2 * E) :
    (n : ℝ≥0) ^ 2 ≤ 20 * (E : ℝ≥0) := by
  have hnoutReal : (n : ℝ) ≤ 2 * outside := by exact_mod_cast hnout
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have houtnonneg : (0 : ℝ) ≤ outside := by positivity
  have hepsnonneg : (0 : ℝ) ≤ epsilon := by positivity
  have hreal : (n : ℝ) ^ 2 ≤ 20 * E := by
    nlinarith [sq_nonneg ((n : ℝ) - 2 * outside)]
  exact_mod_cast hreal

end

end Erdos207
