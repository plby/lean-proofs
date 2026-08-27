/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CoupledOuterRateAlgebra

/-!
# Widening barriers for the coupled outer trajectories

The central trajectory is the usual quadratic `4 E² / N³`.  Unlike an
independent fixed-width corridor, a valid coupled corridor has a window that
widens as the eligible-pair clock `E` falls.  The lemmas below separate the
exact quadratic decrement from the amount of widening required to absorb the
two conservative rate errors.
-/

namespace Erdos207

noncomputable section

/-- The real central pair-degree trajectory at eligible-pair budget `E` and
outside-vertex scale `N`. -/
def coupledOuterCenter (N E : ℝ) : ℝ :=
  4 * E ^ 2 * N⁻¹ ^ 3

/-- An inverse-power widening window.  The exponent is chosen later; any
`k` with `200 ≤ 3*k` supplies the amount of widening required by
`coupledOuter_barrier_step`. -/
def coupledOuterWindow (A : ℝ) (k : ℕ) (E : ℝ) : ℝ :=
  A / E ^ k

lemma coupledOuterCenter_nonneg {N E : ℝ} (hN : 0 ≤ N) :
    0 ≤ coupledOuterCenter N E := by
  unfold coupledOuterCenter
  positivity

lemma coupledOuterCenter_pos {N E : ℝ} (hN : 0 < N) (hE : 0 < E) :
    0 < coupledOuterCenter N E := by
  unfold coupledOuterCenter
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hE))
    (pow_pos (inv_pos.mpr hN) 3)

/-- Exact one-step decrement when three eligible pairs are consumed. -/
lemma coupledOuterCenter_sub_three
    {N E : ℝ} (hN : 0 < N) (hE : 0 < E) :
    coupledOuterCenter N E - coupledOuterCenter N (E - 3) =
      (6 - 9 / E) * coupledOuterCenter N E / E := by
  unfold coupledOuterCenter
  field_simp
  ring

/-- The central decrement is at most its leading term `6y/E`. -/
lemma coupledOuterCenter_decrement_le
    {N E : ℝ} (hN : 0 < N) (hE : 0 < E) :
    coupledOuterCenter N E - coupledOuterCenter N (E - 3) ≤
      6 * coupledOuterCenter N E / E := by
  rw [coupledOuterCenter_sub_three hN hE]
  have hy := coupledOuterCenter_nonneg (N := N) (E := E) hN.le
  have hinv : 0 ≤ E⁻¹ := inv_nonneg.mpr hE.le
  have hdiv : 0 ≤ 9 / E := div_nonneg (by norm_num) hE.le
  calc
    (6 - 9 / E) * coupledOuterCenter N E / E ≤
        6 * coupledOuterCenter N E / E := by
      gcongr
      linarith

/-- If reciprocal-clock rounding is charged to `z`, the central decrement
is at least `(6 - 10z)y/E`. -/
lemma coupledOuterCenter_decrement_ge
    {N E z : ℝ} (hN : 0 < N) (hE : 0 < E)
    (hz : 0 ≤ z) (hinv : E⁻¹ ≤ z) :
    (6 - 10 * z) * coupledOuterCenter N E / E ≤
      coupledOuterCenter N E - coupledOuterCenter N (E - 3) := by
  rw [coupledOuterCenter_sub_three hN hE]
  have hy := coupledOuterCenter_nonneg (N := N) (E := E) hN.le
  have hcoef : 6 - 10 * z ≤ 6 - 9 / E := by
    have : 9 / E ≤ 10 * z := by
      rw [div_eq_mul_inv]
      nlinarith
    linarith
  gcongr

/-- A widening of `200 z y / E` dominates both rate errors from
`CoupledOuterRateAlgebra`. -/
lemma coupledOuter_barrier_step
    {y y' w w' z E upperRate lowerRate : ℝ}
    (hE : 0 < E) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hcenterUpper : y - y' ≤ 6 * y / E)
    (hcenterLower : (6 - 10 * z) * y / E ≤ y - y')
    (hwiden : 200 * z * y / E ≤ w' - w)
    (hupperRate : (6 - 100 * z) * y / E ≤ upperRate)
    (hlowerRate : lowerRate ≤ (6 + 100 * z) * y / E) :
    (y + w) - (y' + w') ≤ upperRate ∧
      lowerRate ≤ (y - w) - (y' - w') := by
  constructor
  · calc
      (y + w) - (y' + w') = (y - y') - (w' - w) := by ring
      _ ≤ 6 * y / E - 200 * z * y / E := sub_le_sub hcenterUpper hwiden
      _ ≤ (6 - 100 * z) * y / E := by
        have hyE : 0 ≤ y / E := div_nonneg hy hE.le
        calc
          6 * y / E - 200 * z * y / E =
              (6 - 200 * z) * (y / E) := by ring
          _ ≤ (6 - 100 * z) * (y / E) := by gcongr <;> nlinarith
          _ = (6 - 100 * z) * y / E := by ring
      _ ≤ upperRate := hupperRate
  · calc
      lowerRate ≤ (6 + 100 * z) * y / E := hlowerRate
      _ ≤ (6 - 10 * z) * y / E + 200 * z * y / E := by
        have hyE : 0 ≤ y / E := div_nonneg hy hE.le
        calc
          (6 + 100 * z) * y / E =
              (6 + 100 * z) * (y / E) := by ring
          _ ≤ (6 + 190 * z) * (y / E) := by gcongr <;> nlinarith
          _ = (6 - 10 * z) * y / E + 200 * z * y / E := by ring
      _ ≤ (y - y') + (w' - w) := add_le_add hcenterLower hwiden
      _ = (y - w) - (y' - w') := by ring

/-- Bernoulli's inequality turns an inverse power into an explicit widening
increment when the clock drops from `E` to `E-3`. -/
lemma coupledOuterWindow_growth
    {A E : ℝ} {k : ℕ} (hA : 0 ≤ A) (hE : 3 < E) :
    (3 * k : ℝ) * coupledOuterWindow A k E / E ≤
      coupledOuterWindow A k (E - 3) - coupledOuterWindow A k E := by
  have hEpos : 0 < E := by linarith
  have hEmpos : 0 < E - 3 := by linarith
  let r : ℝ := E / (E - 3)
  have hr : r = 1 + 3 / (E - 3) := by
    dsimp only [r]
    field_simp
    ring
  have hfrac : 0 ≤ 3 / (E - 3) := div_nonneg (by norm_num) hEmpos.le
  have hbern : 1 + (k : ℝ) * (3 / E) ≤ r ^ k := by
    calc
      1 + (k : ℝ) * (3 / E) ≤
          1 + (k : ℝ) * (3 / (E - 3)) := by
        gcongr
        linarith
      _ ≤ (1 + 3 / (E - 3)) ^ k :=
        one_add_mul_le_pow (by nlinarith : (-2 : ℝ) ≤ 3 / (E - 3)) k
      _ = r ^ k := by rw [hr]
  have hw : 0 ≤ coupledOuterWindow A k E := by
    unfold coupledOuterWindow
    positivity
  have hfactor : (k : ℝ) * (3 / E) ≤ r ^ k - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hfactor hw
  have hratio : coupledOuterWindow A k E * r ^ k =
      coupledOuterWindow A k (E - 3) := by
    unfold coupledOuterWindow
    dsimp only [r]
    rw [div_pow]
    field_simp [pow_ne_zero _ hEpos.ne', pow_ne_zero _ hEmpos.ne']
  calc
    (3 * k : ℝ) * coupledOuterWindow A k E / E =
        coupledOuterWindow A k E * ((k : ℝ) * (3 / E)) := by
      push_cast
      ring
    _ ≤ coupledOuterWindow A k E * (r ^ k - 1) := hmul
    _ = coupledOuterWindow A k (E - 3) -
        coupledOuterWindow A k E := by rw [mul_sub, mul_one, hratio]

/-- Convenient specialization of the preceding growth estimate to the
`200 z y / E` margin used by the rate algebra. -/
lemma coupledOuterWindow_growth_two_hundred
    {A E y z : ℝ} {k : ℕ}
    (hA : 0 ≤ A) (hE : 3 < E) (hky : coupledOuterWindow A k E = z * y)
    (hk : 200 ≤ 3 * k) :
    200 * z * y / E ≤
      coupledOuterWindow A k (E - 3) - coupledOuterWindow A k E := by
  have hEpos : 0 < E := by linarith
  have hw : 0 ≤ coupledOuterWindow A k E := by
    unfold coupledOuterWindow
    positivity
  calc
    200 * z * y / E = 200 * coupledOuterWindow A k E / E := by
      rw [hky]
      ring
    _ ≤ (3 * k : ℝ) * coupledOuterWindow A k E / E := by
      gcongr
      exact_mod_cast hk
    _ ≤ coupledOuterWindow A k (E - 3) - coupledOuterWindow A k E :=
      coupledOuterWindow_growth hA hE

end

end Erdos207
