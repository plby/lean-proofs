import Wikipedia.SchoenfliesTheorem.SquareMesh
import StackExchange.Puzzling139335.CentralRotation.CircleArcs

/-!
# Radial retraction to the model Jordan curve

The model curve is the boundary of the square `[-1,1]²`. Dividing a nonzero
vector by its sup norm gives a continuous retraction onto that boundary.
-/

open Set Schoenflies

namespace Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero

noncomputable section

private theorem supNorm_ne_zero {p : Plane} (hp : p ≠ 0) :
    Schoenflies.Plane.supNorm p ≠ 0 := by
  intro h
  apply hp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg p)
  simpa only [h, mul_zero] using Schoenflies.Plane.norm_le_sqrt_two_mul_supNorm p

theorem modelCurve_ne_zero {p : Plane} (hp : p ∈ Schoenflies.modelCurve) : p ≠ 0 := by
  intro h
  apply (zero_ne_one : (0 : ℝ) ≠ 1)
  simpa only [h, Schoenflies.modelCurve, mem_setOf_eq,
    Schoenflies.Plane.supNorm, PiLp.zero_apply, abs_zero, max_self] using hp

/-- Projection from the punctured plane onto the boundary of the model square. -/
def modelRadial : C(({0}ᶜ : Set Plane), Schoenflies.modelCurve) where
  toFun p := ⟨(Schoenflies.Plane.supNorm p)⁻¹ • (p : Plane), by
    change Schoenflies.Plane.supNorm _ = 1
    rw [Schoenflies.Plane.supNorm_smul,
      abs_of_nonneg (inv_nonneg.mpr (Schoenflies.Plane.supNorm_nonneg p))]
    exact inv_mul_cancel₀ (supNorm_ne_zero (by
      simpa only [mem_compl_iff, mem_singleton_iff] using p.property))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((Schoenflies.continuous_supNorm.comp continuous_subtype_val).inv₀
      (fun p => supNorm_ne_zero (by
        simpa only [mem_compl_iff, mem_singleton_iff] using p.property))).smul
      continuous_subtype_val

/-- The radial projection fixes every point of the model boundary. -/
theorem modelRadial_of_mem (p : ({0}ᶜ : Set Plane))
    (hp : (p : Plane) ∈ Schoenflies.modelCurve) :
    modelRadial p = ⟨p, hp⟩ := by
  apply Subtype.ext
  change (Schoenflies.Plane.supNorm p)⁻¹ • (p : Plane) = (p : Plane)
  rw [show Schoenflies.Plane.supNorm p = 1 from hp, inv_one, one_smul]

/-- A continuous circle embedding, with its codomain restricted to its image. -/
def circleRangeHomeomorph {f : AddCircle (1 : ℝ) → Plane}
    (hf : Continuous f) (hfi : Function.Injective f) :
    AddCircle (1 : ℝ) ≃ₜ range f :=
  (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorph

@[simp] theorem circleRangeHomeomorph_apply {f : AddCircle (1 : ℝ) → Plane}
    (hf : Continuous f) (hfi : Function.Injective f) (z : AddCircle (1 : ℝ)) :
    (circleRangeHomeomorph hf hfi z : Plane) = f z := rfl

@[simp] theorem circleRangeHomeomorph_symm_apply {f : AddCircle (1 : ℝ) → Plane}
    (hf : Continuous f) (hfi : Function.Injective f) (z : AddCircle (1 : ℝ)) :
    (circleRangeHomeomorph hf hfi).symm ⟨f z, mem_range_self z⟩ = z :=
  (circleRangeHomeomorph hf hfi).symm_apply_apply z

end

end Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero
