import Wikipedia.HopfProblem.EllipticEquivariantData
import Wikipedia.HopfProblem.EllipticBundleCharacters

/-!
# Explicit holomorphic units for the elliptic canonical sections

The multiplicative covariance equation of Lemma 9.10(ii) admits an
explicit solution for the actual period transformations.  The reciprocal
of `τ - (1 - ρ)` in the order-three case, and of `τ + I` in the order-four
case, is holomorphic and nowhere zero on the entire disc.  The upper-half-
plane condition rules out both denominators' zeros.  No logarithm,
supplied coboundary, or additional cocycle assumption is needed.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.SectionsUnit

open Elliptic

local notation "I" => modelWithCornersSelf ℂ ℂ

/-- The exponents `m - 1 - a` in the two actual elliptic cases. -/
def vanishingOrder : Kind → ℕ
  | .three => 0
  | .four => 2

/-- The admissible fixed value of the first period coordinate. -/
def fixedTau : Kind → ℂ
  | .three => rho
  | .four => Complex.I

/-- The other, lower-half-plane fixed point of the period transformation. -/
def lowerFixedTau : Kind → ℂ
  | .three => 1 - rho
  | .four => -Complex.I

theorem fixedTau_im_pos (j : Kind) : 0 < (fixedTau j).im := by
  cases j
  · exact rho_im_pos
  · norm_num [fixedTau]

theorem lowerFixedTau_im_neg (j : Kind) : (lowerFixedTau j).im < 0 := by
  cases j
  · simpa only [lowerFixedTau, Complex.sub_im, Complex.one_im, zero_sub] using
      neg_neg_of_pos rho_im_pos
  · norm_num [lowerFixedTau]

theorem fixedTau_ne_zero (j : Kind) : fixedTau j ≠ 0 := by
  intro h
  have hp := fixedTau_im_pos j
  simp [h] at hp

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual varying period minus the fixed lower-half-plane point. -/
def denominator (s : Disc) : ℂ := (D.periods.point s).val.τ - lowerFixedTau j

theorem denominator_im_pos (s : Disc) : 0 < (denominator D s).im := by
  change 0 < (D.periods.point s).val.τ.im - (lowerFixedTau j).im
  have ht := (D.periods.point s).property.1
  have hl := lowerFixedTau_im_neg j
  linarith

theorem denominator_ne_zero (s : Disc) : denominator D s ≠ 0 := by
  intro h
  have hp := denominator_im_pos D s
  simp [h] at hp

theorem denominator_holomorphic : ContMDiff I I ω (denominator D) :=
  D.periods.holomorphic_tau.sub contMDiff_const

/-- A globally defined, nowhere-zero holomorphic unit on the actual disc. -/
def periodUnit (s : Disc) : ℂ := (denominator D s)⁻¹

theorem periodUnit_ne_zero (s : Disc) : periodUnit D s ≠ 0 :=
  inv_ne_zero (denominator_ne_zero D s)

theorem periodUnit_holomorphic : ContMDiff I I ω (periodUnit D) :=
  (denominator_holomorphic D).inv₀ (denominator_ne_zero D)

/-- The unit's denominator has the exact covariance forced by the
original period-coordinate laws. -/
theorem denominator_covariance (s : Disc) :
    denominator D (familyRotation j s) =
      fixedTau j * denominator D s / (D.periods.point s).val.τ := by
  have ht := (D.periods.point s).val.τ_ne_zero (D.periods.point s).property.1
  have h := congrArg (fun p : PeriodDomain => p.val.τ) (D.covariance s)
  cases j
  · change (D.periods.point (familyRotation .three s)).val.τ =
      ((D.periods.point s).val.τ - 1) / (D.periods.point s).val.τ at h
    change (D.periods.point (familyRotation .three s)).val.τ - (1 - rho) =
      rho * ((D.periods.point s).val.τ - (1 - rho)) / (D.periods.point s).val.τ
    rw [h]
    field_simp [ht]
    linear_combination -rho_sq
  · change (D.periods.point (familyRotation .four s)).val.τ =
      -1 / (D.periods.point s).val.τ at h
    change (D.periods.point (familyRotation .four s)).val.τ - -Complex.I =
      Complex.I * ((D.periods.point s).val.τ - -Complex.I) / (D.periods.point s).val.τ
    rw [h]
    field_simp [ht]
    linear_combination -Complex.I_sq

theorem periodUnit_covariance_ratio (s : Disc) :
    periodUnit D (familyRotation j s) * (fixedTau j / (D.periods.point s).val.τ) =
      periodUnit D s := by
  change (denominator D (familyRotation j s))⁻¹ * _ = (denominator D s)⁻¹
  rw [denominator_covariance]
  field_simp [fixedTau_ne_zero j, denominator_ne_zero D s,
    (D.periods.point s).val.τ_ne_zero (D.periods.point s).property.1]

/-- The canonical weight agrees exactly with the denominator's period
factor, for the actual matrices and the exponents zero and two. -/
theorem phase_determinant_ratio (j : Kind) (p : PeriodDomain) :
    normalPhase j ^ vanishingOrder j * (normalPhase j * (linearMatrix j p).det) =
      fixedTau j / p.val.τ := by
  cases j
  · simp only [vanishingOrder, pow_zero, one_mul, normalPhase, linearMatrix,
      PeriodPoint.det_R₁, fixedTau]
    ring
  · simp [vanishingOrder, normalPhase, linearMatrix, PeriodPoint.det_R₂,
      fixedTau, pow_succ, div_eq_mul_inv]

theorem periodUnit_covariance (s : Disc) :
    periodUnit D (familyRotation j s) *
        (normalPhase j ^ vanishingOrder j *
          (normalPhase j * (linearMatrix j (D.periods.point s)).det)) =
      periodUnit D s := by
  rw [phase_determinant_ratio]
  exact periodUnit_covariance_ratio D s

/-- The actual invariant canonical coefficient `s^k u(s)`. -/
def coefficient (s : Disc) : ℂ := (s : ℂ) ^ vanishingOrder j * periodUnit D s

theorem coefficient_holomorphic : ContMDiff I I ω (coefficient D) :=
  (contMDiff_subtype_val.pow (vanishingOrder j)).mul (periodUnit_holomorphic D)

theorem coefficient_ne_zero_iff (s : Disc) :
    coefficient D s ≠ 0 ↔ vanishingOrder j = 0 ∨ (s : ℂ) ≠ 0 := by
  cases j <;> simp [coefficient, vanishingOrder, periodUnit_ne_zero]

theorem coefficient_eq_zero_iff (s : Disc) :
    coefficient D s = 0 ↔ vanishingOrder j ≠ 0 ∧ (s : ℂ) = 0 := by
  cases j <;> simp [coefficient, vanishingOrder, periodUnit_ne_zero]

/-- Exact covariance under the genuine family rotation and the actual
complex matrix determinant.  This holds on the whole disc, including zero. -/
theorem coefficient_covariance_raw (s : Disc) :
    coefficient D (familyRotation j s) *
        (normalPhase j * (linearMatrix j (D.periods.point s)).det) =
      coefficient D s := by
  rw [coefficient, coefficient, familyRotation_val, mul_pow]
  calc
    _ = (s : ℂ) ^ vanishingOrder j *
        (periodUnit D (familyRotation j s) *
          (normalPhase j ^ vanishingOrder j *
            (normalPhase j * (linearMatrix j (D.periods.point s)).det))) := by ring
    _ = _ := congrArg (fun z : ℂ => (s : ℂ) ^ vanishingOrder j * z)
      (periodUnit_covariance D s)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.SectionsUnit
