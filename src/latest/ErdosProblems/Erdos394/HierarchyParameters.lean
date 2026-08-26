import ErdosProblems.Erdos394.DenominatorEulerLower
import ErdosProblems.Erdos394.EulerGapAlgebra
import ErdosProblems.Erdos394.EndpointEulerLower
import ErdosProblems.Erdos394.GeometricBrun

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sparse polynomial grid for the adjacent-block hierarchy
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

/-- Integer degree in the exact powered Euler gap. -/
def hierarchyGapDegree (K : ℕ) : ℕ := (K + 1) * (2 * K + 1)

/-- A deliberately generous polynomial scale, leaving room for every endpoint
and finite-sieve loss. -/
def hierarchyScaleDegree (K : ℕ) : ℕ :=
  1000 * (hierarchyGapDegree K + 1)

/-- Exponent of the global power-of-sixteen cutoff. -/
def hierarchyGlobalExponent (K j : ℕ) : ℕ :=
  j ^ hierarchyScaleDegree K

/-- Exponent of the lower medium-prime endpoint. -/
def hierarchyLowerExponent (_K j : ℕ) : ℕ := j ^ 2

/-- Exponent of the upper medium-prime endpoint. -/
def hierarchyUpperExponent (K j : ℕ) : ℕ :=
  j ^ (hierarchyScaleDegree K - 4)

/-- Global cutoff and medium-prime endpoints. -/
def hierarchyX (K j : ℕ) : ℕ := 16 ^ hierarchyGlobalExponent K j
def hierarchyZ (K j : ℕ) : ℕ := 16 ^ hierarchyLowerExponent K j
def hierarchyY (K j : ℕ) : ℕ := 16 ^ hierarchyUpperExponent K j

/-- Root-box auxiliary height, shifted-bad dilution, and common truncation
order. -/
def hierarchyRootHeight (_K j : ℕ) : ℕ := 16 ^ j
def hierarchyDilution (_K j : ℕ) : ℕ := j ^ 60
noncomputable def hierarchyOrder (K j : ℕ) : ℕ :=
  geometricBrunOrder (hierarchyUpperExponent K j)

lemma hierarchyGapDegree_pos (K : ℕ) : 0 < hierarchyGapDegree K := by
  unfold hierarchyGapDegree
  positivity

lemma hierarchyScaleDegree_ge_thousand (K : ℕ) :
    1000 ≤ hierarchyScaleDegree K := by
  unfold hierarchyScaleDegree
  have h := hierarchyGapDegree_pos K
  nlinarith

lemma hierarchyScaleDegree_sub_four_pos (K : ℕ) :
    0 < hierarchyScaleDegree K - 4 := by
  have h := hierarchyScaleDegree_ge_thousand K
  omega

lemma hierarchyOrder_even (K j : ℕ) : Even (hierarchyOrder K j) :=
  geometricBrunOrder_even _

lemma hierarchyLower_le_upper_exponent (K : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    hierarchyLowerExponent K j ≤ hierarchyUpperExponent K j := by
  unfold hierarchyLowerExponent hierarchyUpperExponent
  apply Nat.pow_le_pow_right hj
  have h := hierarchyScaleDegree_ge_thousand K
  omega

lemma hierarchyZ_le_Y (K : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    hierarchyZ K j ≤ hierarchyY K j := by
  unfold hierarchyZ hierarchyY
  exact Nat.pow_le_pow_right (by omega)
    (hierarchyLower_le_upper_exponent K hj)

lemma hierarchyUpper_lt_global_exponent (K : ℕ) {j : ℕ} (hj : 2 ≤ j) :
    hierarchyUpperExponent K j < hierarchyGlobalExponent K j := by
  unfold hierarchyUpperExponent hierarchyGlobalExponent
  apply Nat.pow_lt_pow_right hj
  have h := hierarchyScaleDegree_ge_thousand K
  omega

set_option maxRecDepth 10000 in
/-- Although the upper endpoint exponent has enormous fixed degree, its
logarithmic Brun order is eventually below the grid variable itself. -/
theorem eventually_hierarchyOrder_le (K : ℕ) :
    ∀ᶠ j : ℕ in atTop, hierarchyOrder K j ≤ j := by
  let D := hierarchyScaleDegree K
  have hD1000 : 1000 ≤ D := hierarchyScaleDegree_ge_thousand K
  have hDposR : (0 : ℝ) < D := by positivity
  have heps : (0 : ℝ) < 1 / (1000 * (D : ℝ)) := by positivity
  have hsmallR := Real.isLittleO_log_id_atTop.bound heps
  have hsmall := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallR
  filter_upwards [eventually_ge_atTop 1000, hsmall] with j hj hlog
  have hjpos : (0 : ℝ) < j := by positivity
  have hlog0 : 0 ≤ Real.log (j : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hjpos.le,
    abs_of_nonneg hlog0] at hlog
  have hlogJ : Real.log (hierarchyUpperExponent K j : ℕ) =
      (D - 4 : ℕ) * Real.log (j : ℝ) := by
    dsimp [hierarchyUpperExponent, D]
    rw [Nat.cast_pow, Real.log_pow]
  have harg0 : 0 ≤ 100 *
      (1 + Real.log (hierarchyUpperExponent K j : ℕ)) := by
    have : 0 ≤ Real.log (hierarchyUpperExponent K j : ℕ) :=
      Real.log_nonneg (by exact_mod_cast
        (show 1 ≤ hierarchyUpperExponent K j by
          unfold hierarchyUpperExponent
          exact Nat.one_le_pow _ _ (by omega)))
    positivity
  have hceil := Nat.ceil_lt_add_one harg0
  have hRcast : (hierarchyOrder K j : ℝ) <
      200 * (1 + Real.log (hierarchyUpperExponent K j : ℕ)) + 2 := by
    unfold hierarchyOrder geometricBrunOrder
    push_cast
    nlinarith
  have hDsub : ((D - 4 : ℕ) : ℝ) ≤ (D : ℝ) := by exact_mod_cast Nat.sub_le D 4
  have hlogBound : (D : ℝ) * Real.log j ≤ (j : ℝ) / 1000 := by
    have := mul_le_mul_of_nonneg_left hlog hDposR.le
    field_simp at this ⊢
    nlinarith
  have hRj : (hierarchyOrder K j : ℝ) ≤ (j : ℝ) := by
    rw [hlogJ] at hRcast
    have hsublog : ((D - 4 : ℕ) : ℝ) * Real.log j ≤
        (D : ℝ) * Real.log j :=
      mul_le_mul_of_nonneg_right hDsub hlog0
    have hjR : (1000 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  exact_mod_cast hRj

end Erdos394
