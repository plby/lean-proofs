import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Displacement in a smoothly varying frame

The derivative at zero normal displacement is exactly the direct sum of the
base derivative and the frame. Dependence of the frame on the base point
contributes no extra term there, because the normal vector is zero.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable {D Z F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual vector-space displacement by a varying frame. -/
def displacement (H : D → F) (A : D → Z →L[ℝ] F) (p : D × Z) : F := H p.1 + A p.1 p.2

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem displacement_zero (H : D → F) (A : D → Z →L[ℝ] F) (x : D) :
    displacement H A (x, 0) = H x := by simp [displacement]

/-- Smoothness holds on the entire product over the given frame domain. -/
theorem contDiffOn_displacement {H : D → F} {A : D → Z →L[ℝ] F} {V : Set D}
    (hH : ContDiff ℝ ∞ H) (hA : ContDiffOn ℝ ∞ A V) :
    ContDiffOn ℝ ∞ (displacement H A) (V ×ˢ univ) :=
  (hH.comp contDiff_fst).contDiffOn.add
    ((hA.comp contDiffOn_fst (fun _ hp => hp.1)).clm_apply contDiffOn_snd)

/-- At zero, the derivative is the base derivative plus the actual frame. -/
theorem hasFDerivAt_displacement_zero {H : D → F} {A : D → Z →L[ℝ] F} {x : D}
    (hH : ContDiffAt ℝ ∞ H x) (hA : ContDiffAt ℝ ∞ A x) :
    HasFDerivAt (displacement H A) ((fderiv ℝ H x).coprod (A x)) (x, 0) := by
  have hfst : HasFDerivAt (Prod.fst : D × Z → D) (ContinuousLinearMap.fst ℝ D Z) (x, 0) :=
    hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : D × Z → Z) (ContinuousLinearMap.snd ℝ D Z) (x, 0) :=
    hasFDerivAt_snd
  have h₁ : HasFDerivAt (fun p : D × Z => H p.1)
      ((fderiv ℝ H x).comp (ContinuousLinearMap.fst ℝ D Z)) (x, 0) :=
    (hH.differentiableAt (by simp)).hasFDerivAt.comp (x, 0) hfst
  have h₂ : HasFDerivAt (fun p : D × Z => A p.1)
      ((fderiv ℝ A x).comp (ContinuousLinearMap.fst ℝ D Z)) (x, 0) :=
    (hA.differentiableAt (by simp)).hasFDerivAt.comp (x, 0) hfst
  have h := h₁.add (h₂.clm_apply hsnd)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro q
  change fderiv ℝ H x q.1 + (A x q.2 + (fderiv ℝ A x q.1) 0) =
    fderiv ℝ H x q.1 + A x q.2
  rw [map_zero, add_zero]

end Wikipedia.SmoothSixDPoincare.DiskFraming
