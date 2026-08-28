import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelShear
import Mathlib.Topology.Homotopy.Basic

/-!
# The frozen phase shear on actual planar subspaces

Multiplication by the displayed phase character is a homeomorphism over
every planar subspace.  Scaling its real argument gives a genuine isotopy
to the identity without moving the base point.  This applies in particular
to the strict hexagon annulus used by the specialization open cover.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCover

open ToricSpace SpecializationModel

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (s : Set Plane)

/-- The phase character acts on the fibres of every literal planar subspace. -/
def phaseCellShear : (CompactFibreTorus × s) ≃ₜ (CompactFibreTorus × s) where
  toFun p := (p.1 * sourcePhaseCharacter C₀ (p.2 : Plane), p.2)
  invFun p := (p.1 * (sourcePhaseCharacter C₀ (p.2 : Plane))⁻¹, p.2)
  left_inv p := by simp only [mul_inv_cancel_right, Prod.eta]
  right_inv p := by simp only [mul_assoc, inv_mul_cancel, mul_one, Prod.eta]
  continuous_toFun :=
    (continuous_fst.mul ((sourcePhaseCharacter_continuous C₀).comp
      (continuous_subtype_val.comp continuous_snd))).prodMk continuous_snd
  continuous_invFun :=
    (continuous_fst.mul (((sourcePhaseCharacter_continuous C₀).comp
      (continuous_subtype_val.comp continuous_snd)).inv)).prodMk continuous_snd

@[simp] theorem phaseCellShear_apply (p : CompactFibreTorus × s) :
    phaseCellShear C₀ s p = (p.1 * sourcePhaseCharacter C₀ (p.2 : Plane), p.2) := rfl

@[simp] theorem phaseCellShear_symm_apply (p : CompactFibreTorus × s) :
    (phaseCellShear C₀ s).symm p =
      (p.1 * (sourcePhaseCharacter C₀ (p.2 : Plane))⁻¹, p.2) := rfl

/-- Scaling only the real argument of the phase character keeps every
point of the planar subspace fixed throughout the isotopy. -/
def phaseCellShearHomotopy :
    (ContinuousMap.id (CompactFibreTorus × s)).Homotopy
      (phaseCellShear C₀ s : C(CompactFibreTorus × s, CompactFibreTorus × s)) where
  toFun p := (p.2.1 * sourcePhaseCharacter C₀ ((p.1 : ℝ) • (p.2.2 : Plane)), p.2.2)
  continuous_toFun := by
    have hy : Continuous (fun p : unitInterval × (CompactFibreTorus × s) =>
        (p.1 : ℝ) • (p.2.2 : Plane)) :=
      (continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
    have hχ : Continuous (fun p : unitInterval × (CompactFibreTorus × s) =>
        sourcePhaseCharacter C₀ ((p.1 : ℝ) • (p.2.2 : Plane))) := by
      simpa only [Function.comp_def] using (sourcePhaseCharacter_continuous C₀).comp hy
    exact ((continuous_fst.comp continuous_snd).mul hχ).prodMk
      (continuous_snd.comp continuous_snd)
  map_zero_left p := by simp [sourcePhaseCharacter_zero]
  map_one_left p := by simp [phaseCellShear_apply]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCover
