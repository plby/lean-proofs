import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Genuine tangent coordinates for different complex models

For analytic complex manifolds with arbitrary normed-space self models,
the derivative of an actual coordinate expression factors through the
manifold derivative and the original tangent-bundle coordinate changes.
The source and target models need not be the same normed space.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) ω X]
  [TopologicalSpace Y] [ChartedSpace F Y] [IsManifold (modelWithCornersSelf ℂ F) ω Y]

/-- In a self model, the tangent-bundle coordinate change is the ordinary
complex derivative of the actual transition map. -/
theorem tangentBundleCore_coordChange_self (i j : atlas E X) (x : X) :
    (tangentBundleCore (modelWithCornersSelf ℂ E) X).coordChange i j x =
      fderiv ℂ (j.val ∘ i.val.symm) (i.val x) := by
  simp [tangentBundleCore_coordChange, mfld_simps]

/-- The manifold derivative of an actual chart is its tangent coordinate
change from the preferred chart. -/
theorem mfderiv_atlas_self (i : atlas E X) {x : X} (hx : x ∈ i.val.source) :
    mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) i.val x =
      (tangentBundleCore (modelWithCornersSelf ℂ E) X).coordChange (achart E x) i x := by
  have hi : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) i.val x := mdifferentiableAt_atlas i.property hx
  rw [hi.mfderiv, tangentBundleCore_coordChange_self]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ, chartAt_self_eq]
  rfl

/-- The inverse chart differentiates to the reverse tangent coordinate
change at every point in the actual chart source. -/
theorem mfderiv_atlas_symm_self (i : atlas E X) {x : X} (hx : x ∈ i.val.source) :
    mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) i.val.symm (i.val x) =
      (tangentBundleCore (modelWithCornersSelf ℂ E) X).coordChange i (achart E x) x := by
  have hi : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) i.val.symm (i.val x) :=
    mdifferentiableAt_atlas_symm i.property (i.val.map_source hx)
  rw [hi.mfderiv, tangentBundleCore_coordChange_self]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ, i.val.left_inv hx,
    chartAt_self_eq]
  rfl

/-- The genuine coordinate chain rule with arbitrary complex source and
target models.  No coordinate derivative data is an additional hypothesis. -/
theorem fderiv_coordinates_eq_tangentCore (f : X → Y)
    (i : atlas E X) (j : atlas F Y) {x : X}
    (hi : x ∈ i.val.source) (hj : f x ∈ j.val.source)
    (hf : MDifferentiableAt (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) f x) :
    fderiv ℂ (j.val ∘ f ∘ i.val.symm) (i.val x) =
      ((tangentBundleCore (modelWithCornersSelf ℂ F) Y).coordChange (achart F (f x)) j (f x)).comp
        ((mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) f x).comp
          ((tangentBundleCore (modelWithCornersSelf ℂ E) X).coordChange i (achart E x) x)) := by
  have his : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) i.val.symm (i.val x) :=
    mdifferentiableAt_atlas_symm i.property (i.val.map_source hi)
  have hjd : MDifferentiableAt (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ F) j.val (f x) :=
    mdifferentiableAt_atlas j.property hj
  have hfd : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ F) f (i.val.symm (i.val x)) := by
    simpa only [i.val.left_inv hi] using hf
  have hjd' : MDifferentiableAt (modelWithCornersSelf ℂ F)
      (modelWithCornersSelf ℂ F) j.val ((f ∘ i.val.symm) (i.val x)) := by
    simpa only [Function.comp_apply, i.val.left_inv hi] using hjd
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp (i.val x) hjd' (hfd.comp (i.val x) his),
    mfderiv_comp (i.val x) hfd his]
  apply ContinuousLinearMap.ext
  intro v
  change mfderiv (modelWithCornersSelf ℂ F) (modelWithCornersSelf ℂ F) j.val
    (f (i.val.symm (i.val x)))
    (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) f (i.val.symm (i.val x))
      (mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E)
        i.val.symm (i.val x) v)) = _
  rw [i.val.left_inv hi]
  rw [mfderiv_atlas_self j hj, mfderiv_atlas_symm_self i hi]
  rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback
