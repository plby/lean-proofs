import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryEndpointVariation
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Smoothness and the actual parameter derivative of the constrained variations -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open ImaginarySymmetricMatrices RealSymmetricMixing
open scoped Matrix.Norms.Operator ContDiff

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem hasDerivAt_exponentialCurve_matrix (A : DirectionSpace N) (t : ℝ) :
    HasDerivAt (fun r : ℝ ↦ (exponentialCurve A r).val.val.val)
      ((exponentialCurve A t).val.val.val * imaginary A.val) t := by
  change HasDerivAt (fun r : ℝ ↦ NormedSpace.exp (imaginary (r • A.val)))
    (NormedSpace.exp (imaginary (t • A.val)) * imaginary A.val) t
  simp only [map_smul]
  exact hasDerivAt_exp_smul_const (imaginary A.val) t

theorem hasDerivAt_exponentialCurve_zero (A : DirectionSpace N) :
    HasDerivAt (fun r : ℝ ↦ (exponentialCurve A r).val.val.val) (imaginary A.val) 0 := by
  have h := hasDerivAt_exponentialCurve_matrix A 0
  rw [exponentialCurve_zero] at h
  change HasDerivAt _ ((1 : Matrix N N ℂ) * imaginary A.val) 0 at h
  simpa only [one_mul] using h

theorem hasDerivAt_endpointVariation_matrix (A C : DirectionSpace N) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (endpointVariation A C s t).val.val.val)
      ((exponential ((1 / 2 : ℝ) • (t • A))).val.val.val *
        (Real.sin (Real.pi * t) • imaginary C.val) *
        (exponential ((1 / 2 : ℝ) • (t • A))).val.val.val.transpose) 0 := by
  let F := (exponential ((1 / 2 : ℝ) • (t • A))).val.val.val
  let D : DirectionSpace N := Real.sin (Real.pi * t) • C
  have h := ((hasDerivAt_exponentialCurve_zero D).const_mul F).mul_const F.transpose
  convert! h using 1
  · funext s
    rw [endpointVariation, sandwich_matrix]
    change F * (exponential ((s * Real.sin (Real.pi * t)) • C)).val.val.val * F.transpose =
      F * (exponential (s • (Real.sin (Real.pi * t) • C))).val.val.val * F.transpose
    rw [smul_smul]
  · change F * (Real.sin (Real.pi * t) • imaginary C.val) * F.transpose =
      F * imaginary (Real.sin (Real.pi * t) • C.val) * F.transpose
    rw [map_smul]

theorem contDiff_endpointVariation_matrix (A C : DirectionSpace N) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ (endpointVariation A C z.1 z.2).val.val.val) := by
  have he : ContDiff ℝ ∞ (NormedSpace.exp : Matrix N N ℂ → Matrix N N ℂ) :=
    contDiff_iff_contDiffAt.mpr (fun X ↦ (NormedSpace.exp_analytic (𝕂 := ℝ) X).contDiffAt)
  have hh : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ (1 / 2 : ℝ) * z.2) :=
    contDiff_const.mul contDiff_snd
  have hp : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦ z.1 * Real.sin (Real.pi * z.2)) :=
    contDiff_fst.mul (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd))
  have hF : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦
      NormedSpace.exp (((1 / 2 : ℝ) * z.2) • imaginary A.val)) :=
    he.comp (hh.smul contDiff_const)
  have hC : ContDiff ℝ ∞ (fun z : ℝ × ℝ ↦
      NormedSpace.exp ((z.1 * Real.sin (Real.pi * z.2)) • imaginary C.val)) :=
    he.comp (hp.smul contDiff_const)
  convert! (hF.mul hC).mul hF using 1
  funext z
  rw [endpointVariation, sandwich_matrix,
    (exponential ((1 / 2 : ℝ) • (z.2 • A))).val.property]
  change NormedSpace.exp (imaginary ((1 / 2 : ℝ) • (z.2 • A.val))) *
      NormedSpace.exp (imaginary ((z.1 * Real.sin (Real.pi * z.2)) • C.val)) *
      NormedSpace.exp (imaginary ((1 / 2 : ℝ) • (z.2 • A.val))) = _
  simp only [map_smul, smul_smul]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
