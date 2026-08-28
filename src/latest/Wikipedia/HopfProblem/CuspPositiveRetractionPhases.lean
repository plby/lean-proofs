import Wikipedia.HopfProblem.CuspPositiveRetractionTwist
import Wikipedia.HopfProblem.CuspPositiveRetractionCompactNormalizer

/-!
# Compact phases of the frozen cusp action

The constant complex multiplier factors as its positive real modulus and
an actual compact-torus element.  Combined with the integral shear of the
compact torus, this gives the polar covariance from Lemma 7.7(i) on the
whole glued toric space, including its boundary strata.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspPositive

open ToricCharts ToricFan ToricSpace

/-- The phase of one frozen exponential multiplier, as an element of the
actual unit circle. -/
def frozenPhaseCoordinate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (i : Fin 2) : Circle :=
  ⟨(exponentialMultiplier (fun _ => C₀) v 0 i : ℂ) /
      (exponentialMultiplier (positiveTwist C₀) v 0 i : ℂ), by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div, exponentialMultiplier_positiveTwist_norm]
    exact div_self (norm_ne_zero_iff.mpr
      (exponentialMultiplier (fun _ => C₀) v 0 i).ne_zero)⟩

@[simp] theorem frozenPhaseCoordinate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    (frozenPhaseCoordinate C₀ v i : ℂ) =
      (exponentialMultiplier (fun _ => C₀) v 0 i : ℂ) /
        (exponentialMultiplier (positiveTwist C₀) v 0 i : ℂ) := rfl

/-- The phase is exactly the source's exponential of the real part of
the constant period correction. -/
theorem frozenPhaseCoordinate_eq_exp (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (i : Fin 2) :
    frozenPhaseCoordinate C₀ v i =
      Circle.exp (2 * Real.pi * ((C₀ *ᵥ (fun j => (v j : ℂ))) i).re) := by
  apply Circle.ext
  simp only [frozenPhaseCoordinate_coe, Circle.coe_exp, exponentialMultiplier,
    Units.val_mk0, ← Complex.exp_sub]
  congr 1
  apply Complex.ext <;>
    simp [positiveTwist, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im]

/-- The compact phase changes only the two fibre factors. -/
def frozenPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) : CompactTorus :=
  ![frozenPhaseCoordinate C₀ v 0, frozenPhaseCoordinate C₀ v 1, 1]

@[simp] theorem frozenPhase_two (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    frozenPhase C₀ v 2 = 1 := rfl

theorem compactTorusUnits_frozenPhase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) :
    compactTorusUnits (frozenPhase C₀ v) =
      fibreMultiplier (exponentialMultiplier (fun _ => C₀) v 0 /
        exponentialMultiplier (positiveTwist C₀) v 0) := by
  funext i
  apply Units.ext
  fin_cases i <;> simp [frozenPhase, fibreMultiplier]

/-- Exact factorization of the acting-torus multiplier, not merely an
equality of its moduli. -/
theorem frozenMultiplier_phase_positive (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) :
    fibreMultiplier (exponentialMultiplier (fun _ => C₀) v 0) =
      compactTorusUnits (frozenPhase C₀ v) *
        fibreMultiplier (exponentialMultiplier (positiveTwist C₀) v 0) := by
  rw [compactTorusUnits_frozenPhase, ← fibreMultiplier_mul, div_mul_cancel]

theorem twistedTranslate_constant_eq (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : Space) :
    twistedTranslate (fun _ => C₀) v x =
      torusAction (fibreMultiplier (exponentialMultiplier (fun _ => C₀) v 0))
        (translate (cuspVector v) x) := rfl

/-- The frozen action differs from the positive action by a fixed compact
fibre phase, independent of the point. -/
theorem twistedTranslate_constant_phase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : Space) :
    twistedTranslate (fun _ => C₀) v x =
      compactTorusAction (frozenPhase C₀ v) (twistedTranslate (positiveTwist C₀) v x) := by
  rw [twistedTranslate_constant_eq, frozenMultiplier_phase_positive,
    twistedTranslate_positiveTwist_eq]
  exact (torusAction_mul _ _ _).symm

/-- The phase transformation of Lemma 7.7(i): an integral compact-torus
shear followed by the constant fibre phase. -/
def phaseTransform (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (u : CompactTorus) : CompactTorus :=
  frozenPhase C₀ v * phaseShear (cuspVector v) u

@[simp] theorem phaseTransform_two (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (u : CompactTorus) : phaseTransform C₀ v u 2 = u 2 := by
  simp [phaseTransform]

/-- The exact frozen-versus-positive polar covariance on the original
toric space.  The phase depends on the lattice element and the input
compact phase, but not on the positive point. -/
theorem twistedTranslate_constant_polar (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (u : CompactTorus) (x : Space) :
    twistedTranslate (fun _ => C₀) v (compactTorusAction u x) =
      compactTorusAction (phaseTransform C₀ v u)
        (twistedTranslate (positiveTwist C₀) v x) := by
  rw [twistedTranslate_constant_eq, translate_compactTorusAction,
    twistedTranslate_positiveTwist_eq]
  simp only [phaseTransform, compactTorusAction, map_mul, torusAction_mul]
  rw [frozenMultiplier_phase_positive]
  congr 1
  ac_rfl

/-- The positive action restricted to the literal closed positive
sub-tube used in the polar quotient. -/
def closedPositiveTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (q : ClosedPositiveTube η) : ClosedPositiveTube η :=
  ⟨⟨twistedTranslate (positiveTwist C₀) v q.1,
      twistedTranslate_positiveTwist_preserves_positivePart C₀ v q.1.2⟩,
    by simpa only [time_twistedTranslate] using q.2⟩

@[simp] theorem closedPositiveTranslate_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (v : Fin 2 → ℤ) (q : ClosedPositiveTube η) :
    ((closedPositiveTranslate C₀ η v q).1 : Space) =
      twistedTranslate (positiveTwist C₀) v q.1 := rfl

@[simp] theorem closedPositiveTranslate_zero (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (q : ClosedPositiveTube η) : closedPositiveTranslate C₀ η 0 q = q :=
  Subtype.ext (Subtype.ext (twistedTranslate_zero (positiveTwist C₀) q.1))

theorem closedPositiveTranslate_add (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (v w : Fin 2 → ℤ) (q : ClosedPositiveTube η) :
    closedPositiveTranslate C₀ η v (closedPositiveTranslate C₀ η w q) =
      closedPositiveTranslate C₀ η (v + w) q :=
  Subtype.ext (Subtype.ext (twistedTranslate_add (positiveTwist C₀) v w q.1))

end Wikipedia.HopfProblem.CuspPositive
