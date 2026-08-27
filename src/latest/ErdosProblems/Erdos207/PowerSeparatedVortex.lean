/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PaddedAbsorberSeparatedVortex

/-!
# Power schedules for absorber-separated vortices

The positive levels in the eventual construction are powers of a common
integer scale.  This file isolates the elementary monotonicity and capacity
facts, so the later analytic hierarchy only has to choose the scale and
verify its scalar inequalities.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

/-- A decreasing power schedule, with the terminal free part forced to be
empty.  Level zero is assigned the unused upper-envelope value
`t ^ (step * ell)`. -/
def powerFreeSize (t step ell : ℕ) (i : Fin (ell + 1)) : ℕ :=
  if i = Fin.last ell then 0 else t ^ (step * (ell - i.val))

@[simp]
lemma powerFreeSize_last (t step ell : ℕ) :
    powerFreeSize t step ell (Fin.last ell) = 0 := by
  simp [powerFreeSize]

lemma powerFreeSize_of_ne_last (t step ell : ℕ) (i : Fin (ell + 1))
    (hi : i ≠ Fin.last ell) :
    powerFreeSize t step ell i = t ^ (step * (ell - i.val)) := by
  simp [powerFreeSize, hi]

lemma powerFreeSize_le_top (t step ell : ℕ) (ht : 1 ≤ t)
    (i : Fin (ell + 1)) :
    powerFreeSize t step ell i ≤ t ^ (step * ell) := by
  by_cases hi : i = Fin.last ell
  · simp [hi]
  rw [powerFreeSize_of_ne_last t step ell i hi]
  exact Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le ht)
    (Nat.mul_le_mul_left step
    (Nat.sub_le ell i.val))

lemma powerFreeSize_antitone (t step ell : ℕ) (ht : 1 ≤ t) :
    Antitone (powerFreeSize t step ell) := by
  intro i j hij
  by_cases hj : j = Fin.last ell
  · simp [hj]
  have hi : i ≠ Fin.last ell := by
    intro hilast
    have hji : j.val ≤ i.val := by simpa [hilast] using j.is_le
    have : i = j := Fin.ext (Nat.le_antisymm (by simpa using hij) hji)
    exact hj (this ▸ hilast)
  rw [powerFreeSize_of_ne_last t step ell i hi,
    powerFreeSize_of_ne_last t step ell j hj]
  apply Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le ht)
  apply Nat.mul_le_mul_left step
  exact Nat.sub_le_sub_left (by simpa using hij) ell

lemma powerFreeSize_positive_fit
    {t step ell C n : ℕ}
    (ht : 1 ≤ t)
    (hfit : t ^ (step * ell) + 2 * C ≤ n) :
    ∀ i : Fin (ell + 1), i ≠ 0 →
      powerFreeSize t step ell i + 2 * C ≤ n := by
  intro i _hi
  exact (Nat.add_le_add_right (powerFreeSize_le_top t step ell ht i) _).trans hfit

/-- Only positive levels have to fit inside the absorber-free set.  Their
largest scheduled free part is level one, so the unused level-zero value
`t ^ (step * ell)` need not be charged to ambient capacity. -/
lemma powerFreeSize_positive_le_first
    {t step ell : ℕ} (ht : 1 ≤ t) (hell : 0 < ell)
    (i : Fin (ell + 1)) (hi : i ≠ 0) :
    powerFreeSize t step ell i ≤ t ^ (step * (ell - 1)) := by
  by_cases hilast : i = Fin.last ell
  · simp [hilast]
  rw [powerFreeSize_of_ne_last t step ell i hilast]
  apply Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le ht)
  apply Nat.mul_le_mul_left step
  have hiOne : 1 ≤ i.val := by
    have hiPos : 0 < i.val := by
      by_contra hzero
      apply hi
      have hval : i.val = 0 := Nat.eq_zero_of_not_pos hzero
      exact Fin.ext (by simpa using hval)
    omega
  omega

lemma powerFreeSize_positive_fit_sharp
    {t step ell C n : ℕ}
    (ht : 1 ≤ t) (hell : 0 < ell)
    (hfit : t ^ (step * (ell - 1)) + 2 * C ≤ n) :
    ∀ i : Fin (ell + 1), i ≠ 0 →
      powerFreeSize t step ell i + 2 * C ≤ n := by
  intro i hi
  exact (Nat.add_le_add_right
    (powerFreeSize_positive_le_first ht hell i hi) _).trans hfit

/-- The separated padded-absorber wrapper specialized to a common-base power
schedule.  All positive level cardinalities are now explicit powers. -/
theorem exists_paddedAbsorber_with_initial_power_typicality
    {q h t rootPower step n ell : ℕ} {xi : ℝ≥0}
    (hell : 0 < ell) (ht : 1 ≤ t)
    (habsorberFit : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * t ^ rootPower) ^ 156 ≤ n)
    (hfreeFit : t ^ (step * ell) + 2 *
      (highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ rootPower) ^ 156) ≤ n)
    (hxi : xi ≤ 1)
    (hDegreeAmbient :
      ((highGirthAbsorberCardCoefficient (q + 2) *
          (2 * t ^ rootPower) ^ 156 + 1 : ℕ) : ℝ≥0) ≤
        xi * (n : ℝ≥0))
    (hDegreeInner : (15 : ℝ≥0) ≤ xi * ((t ^ rootPower : ℕ) : ℝ≥0))
    (hExtensionAmbient :
      ((h + h ^ 2 *
          (3 * (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156)) : ℕ) : ℝ≥0) ≤
        xi * (n : ℝ≥0))
    (hExtensionInner :
      (h + h ^ 2 * 36 : ℝ≥0) ≤ xi * ((t ^ rootPower : ℕ) : ℝ≥0)) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystemOn (Fin n), ∃ W : Vortex (Fin n) ell,
        X.card = t ^ rootPower ∧
        W = separatedCardinalVortex H X B (powerFreeSize t step ell)
          (powerFreeSize_antitone t step ell ht) ∧
        W.U (Fin.last ell) = X ∧
        (∀ i, i ≠ 0 →
          (W.U i).card = t ^ rootPower + powerFreeSize t step ell i) ∧
        (∀ i, (W.U i).Nonempty) ∧
        HasHighGirthAbsorptionBank q H X B ∧
        HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
        (verticesOn B).card ≤
          highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156 ∧
        (graphSupportFinset H).card ≤
          highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156 ∧
        (∀ v, H.degree v ≤
          highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156) ∧
        B.card ≤
          (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156) ^ 3 ∧
        HasPaddedAbsorberRootBounds q H X B ∧
        HasPaddedAbsorberRootLocalization q X B ∧
        IsIterationTypical W 0
          (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outsideAvailableTriangles H B)).available
          1 1 xi h := by
  apply exists_paddedAbsorber_with_initial_separated_typicality
    hell (Nat.one_le_pow rootPower t (Nat.zero_lt_one.trans_le ht))
    habsorberFit
    (powerFreeSize t step ell) (powerFreeSize_antitone t step ell ht)
    (powerFreeSize_last t step ell)
  · exact powerFreeSize_positive_fit ht hfreeFit
  · exact hxi
  · exact hDegreeAmbient
  · exact hDegreeInner
  · exact hExtensionAmbient
  · exact hExtensionInner

/-- Sharpened capacity form of the initial power-vortex construction.  It
budgets the actual first positive level rather than the unused level-zero
entry of the power schedule. -/
theorem exists_paddedAbsorber_with_initial_power_typicality_sharp
    {q h t rootPower step n ell : ℕ} {xi : ℝ≥0}
    (hell : 0 < ell) (ht : 1 ≤ t)
    (habsorberFit : highGirthAbsorberCardCoefficient (q + 2) *
      (2 * t ^ rootPower) ^ 156 ≤ n)
    (hfreeFit : t ^ (step * (ell - 1)) + 2 *
      (highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ rootPower) ^ 156) ≤ n)
    (hxi : xi ≤ 1)
    (hDegreeAmbient :
      ((highGirthAbsorberCardCoefficient (q + 2) *
          (2 * t ^ rootPower) ^ 156 + 1 : ℕ) : ℝ≥0) ≤
        xi * (n : ℝ≥0))
    (hDegreeInner : (15 : ℝ≥0) ≤ xi * ((t ^ rootPower : ℕ) : ℝ≥0))
    (hExtensionAmbient :
      ((h + h ^ 2 *
          (3 * (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156)) : ℕ) : ℝ≥0) ≤
        xi * (n : ℝ≥0))
    (hExtensionInner :
      (h + h ^ 2 * 36 : ℝ≥0) ≤ xi * ((t ^ rootPower : ℕ) : ℝ≥0)) :
    ∃ H : SimpleGraph (Fin n), ∃ X : Finset (Fin n),
      ∃ B : TripleSystemOn (Fin n), ∃ W : Vortex (Fin n) ell,
        X.card = t ^ rootPower ∧
        W = separatedCardinalVortex H X B (powerFreeSize t step ell)
          (powerFreeSize_antitone t step ell ht) ∧
        W.U (Fin.last ell) = X ∧
        (∀ i, i ≠ 0 →
          (W.U i).card = t ^ rootPower + powerFreeSize t step ell i) ∧
        (∀ i, (W.U i).Nonempty) ∧
        HasHighGirthAbsorptionBank q H X B ∧
        HasAbsorberLocalization q (12 * (q + 2) ^ 2) H X B ∧
        (verticesOn B).card ≤
          highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156 ∧
        (graphSupportFinset H).card ≤
          highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156 ∧
        (∀ v, H.degree v ≤
          highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156) ∧
        B.card ≤
          (highGirthAbsorberCardCoefficient (q + 2) *
            (2 * t ^ rootPower) ^ 156) ^ 3 ∧
        HasPaddedAbsorberRootBounds q H X B ∧
        HasPaddedAbsorberRootLocalization q X B ∧
        IsIterationTypical W 0
          (graphDifference (SimpleGraph.completeGraph (Fin n)) H)
          (absorberGreedyInitialState
            (absorberErdosForbiddenConfigurationsOn q B)
            (outsideAvailableTriangles H B)).available
          1 1 xi h := by
  apply exists_paddedAbsorber_with_initial_separated_typicality
    hell (Nat.one_le_pow rootPower t (Nat.zero_lt_one.trans_le ht))
    habsorberFit
    (powerFreeSize t step ell) (powerFreeSize_antitone t step ell ht)
    (powerFreeSize_last t step ell)
  · exact powerFreeSize_positive_fit_sharp ht hell hfreeFit
  · exact hxi
  · exact hDegreeAmbient
  · exact hDegreeInner
  · exact hExtensionAmbient
  · exact hExtensionInner

end

end Erdos207
