import Wikipedia.HopfProblem.DegreeCollapseSupportedCuspModel
import Wikipedia.HopfProblem.DegreeCollapseCuspStraightening

/-!
# The literal plane as a continuous linear coordinate inclusion

The canonical first-three/last-three split identifies the previously defined
plane formula with the zero section of the product. These exact identities
are used to put the constructed kink in an original immersion chart.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere.GLOrthonormalization

def planeSplit : Vector 6 ≃L[ℝ] Vector 3 × Vector 3 :=
  EuclideanSpace.finAddEquivProd (n := 3) (m := 3)

theorem planeSplit_plane (x : Vector 3) : planeSplit (plane x) = (x, 0) := by
  apply Prod.ext
  · ext i
    fin_cases i <;> rfl
  · ext i
    fin_cases i <;> rfl

def planeLinear : Vector 3 →L[ℝ] Vector 6 :=
  planeSplit.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (Vector 3) (Vector 3))

theorem planeLinear_apply (x : Vector 3) : planeLinear x = plane x := by
  apply planeSplit.injective
  change planeSplit (planeSplit.symm (x, 0)) = planeSplit (plane x)
  rw [planeSplit.apply_symm_apply, planeSplit_plane]

theorem contDiff_plane : ContDiff ℝ ∞ plane := by
  have he : (planeLinear : Vector 3 → Vector 6) = plane := funext planeLinear_apply
  exact he ▸ planeLinear.contDiff

theorem plane_smul (c : ℝ) (x : Vector 3) : plane (c • x) = c • plane x := by
  simpa only [planeLinear_apply] using planeLinear.map_smul c x

theorem plane_zero : plane (0 : Vector 3) = 0 := by
  simpa only [planeLinear_apply] using planeLinear.map_zero

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
