import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCollarBasic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# The native real-analytic radial annulus collar

The source carries the original stereographic atlas of the Euclidean unit
three-sphere and the original open-interval atlas. The target carries the
original open-subspace atlas in Euclidean four-space. Normalization is
real analytic away from zero, so the literal radial inverse is analytic.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar

local notation "IR" => 𝓘(ℝ, ℝ)
local notation "I₄" => 𝓘(ℝ, Space)
local notation "IC" => ModelWithCorners.prod (𝓡 3) 𝓘(ℝ, ℝ)

local instance ambientDimension : Fact (Module.finrank ℝ Space = 3 + 1) :=
  ⟨by simp⟩

/-- The actual affine radial scale is real analytic. -/
theorem radialScale_contDiff : ContDiff ℝ ω radialScale :=
  contDiff_const.add (contDiff_id.div_const 2)

/-- Native real analyticity of the actual radial parametrization. -/
theorem forward_contMDiff : ContMDiff IC I₄ ω forward := by
  have ht : ContMDiff IC IR ω (fun p : Sphere × interval => (p.2 : ℝ)) :=
    contMDiff_subtype_val.comp contMDiff_snd
  have hu : ContMDiff IC I₄ ω (fun p : Sphere × interval => (p.1 : Space)) :=
    contMDiff_coe_sphere.comp contMDiff_fst
  have h : ContMDiff IC I₄ ω
      (fun p : Sphere × interval => radialScale p.2 • (p.1 : Space)) :=
    (radialScale_contDiff.contMDiff.comp ht).smul hu
  intro p
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
  exact h p

/-- The norm is analytic at every actual point of this annulus. -/
theorem annulus_norm_contMDiff :
    ContMDiff I₄ IR ω (fun x : annulus => ‖(x : Space)‖) := by
  intro x
  exact (contDiffAt_norm ℝ (annulus_ne_zero x)).contMDiffAt.comp x
    contMDiff_subtype_val.contMDiffAt

/-- The inverse norm is analytic on the same actual annulus. -/
theorem annulus_inv_norm_contMDiff :
    ContMDiff I₄ IR ω (fun x : annulus => ‖(x : Space)‖⁻¹) := by
  intro x
  exact ((contDiffAt_norm ℝ (annulus_ne_zero x)).inv
    (annulus_norm_ne_zero x)).contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt

/-- Normalization lands smoothly in the original stereographic sphere atlas. -/
theorem unitDirection_contMDiff : ContMDiff I₄ (𝓡 3) ω unitDirection := by
  have h : ContMDiff I₄ I₄ ω
      (fun x : annulus => ‖(x : Space)‖⁻¹ • (x : Space)) :=
    annulus_inv_norm_contMDiff.smul contMDiff_subtype_val
  exact h.codRestrict_sphere (fun x => (unitDirection x).property)

/-- The inverse affine radial parameter uses the original open interval atlas. -/
theorem inverseParameter_contMDiff : ContMDiff I₄ IR ω inverseParameter := by
  have ha : ContDiff ℝ ω (fun r : ℝ => 2 * r - 1) :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  have h : ContMDiff I₄ IR ω
      (fun x : annulus => 2 * ‖(x : Space)‖ - 1) :=
    ha.contMDiff.comp annulus_norm_contMDiff
  intro x
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
  exact h x

/-- Native real analyticity of the literal direction-and-radius inverse. -/
theorem inverse_contMDiff : ContMDiff I₄ IC ω inverse :=
  unitDirection_contMDiff.prodMk inverseParameter_contMDiff

/-- The genuine standard radial collar, with neither smooth structure transported. -/
def radialDiffeomorph : Diffeomorph IC I₄ (Sphere × interval) annulus ω where
  toEquiv := radialHomeomorph.toEquiv
  contMDiff_toFun := forward_contMDiff
  contMDiff_invFun := inverse_contMDiff

@[simp] theorem radialDiffeomorph_coe (p : Sphere × interval) :
    (radialDiffeomorph p : Space) = radialScale p.2 • (p.1 : Space) := rfl

@[simp] theorem radialDiffeomorph_symm_fst_coe (x : annulus) :
    ((radialDiffeomorph.symm x).1 : Space) = ‖(x : Space)‖⁻¹ • (x : Space) := rfl

@[simp] theorem radialDiffeomorph_symm_snd_coe (x : annulus) :
    ((radialDiffeomorph.symm x).2 : ℝ) = 2 * ‖(x : Space)‖ - 1 := rfl

@[simp] theorem radialDiffeomorph_zeroParameter_coe (u : Sphere) :
    (radialDiffeomorph (u, zeroParameter) : Space) = (1 / 2 : ℝ) • (u : Space) :=
  forward_zeroParameter_coe u

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Collar
