import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSignProjectedDifferential

/-!
# The determinant-one sign comparison in seven-dimensional target coordinates

The fixed target chart is applied to every sign family. The chain rule
preserves the exact derivative factorization, so the comparison uses the
actual source and target sphere coordinates rather than only ambient entries.
-/

noncomputable section

open scoped ContDiff Matrix.Norms.Elementwise

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

theorem signProjection_postcompose_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (Fin 2 → ℍ) → E) (hg : DifferentiableAt ℝ g targetColumn) (x y : Bool) :
    fderiv ℝ (g ∘ signProjection x y) 0 =
      (fderiv ℝ (g ∘ signProjection true true) 0).comp
        (signParameterComparison x y).toContinuousLinearMap := by
  have hf (a b : Bool) :=
    ((contDiff_signProjection a b (n := 1)).differentiable (by decide)) 0
  have hgc (a b : Bool) : DifferentiableAt ℝ g (signProjection a b 0) := by
    rw [signProjection_zero]
    exact hg
  rw [fderiv_comp 0 (hgc x y) (hf x y), fderiv_comp 0 (hgc true true) (hf true true),
    signProjection_zero, signProjection_zero, signProjection_fderiv_eq_comp]
  rfl

theorem targetColumn_toLp :
    (WithLp.toLp 2 targetColumn : QuaternionSpace 1) = (localColumn input 0).val := by
  change WithLp.toLp 2 targetColumn = WithLp.toLp 2 (localProjection input 0)
  rw [localProjection_zero, input_hits_target]

def fixedTargetCoordinates (v : Fin 2 → ℍ) : TargetSpace input :=
  stereoToFun (-(localColumn input 0).val) (WithLp.toLp 2 v)

theorem contDiffAt_fixedTargetCoordinates {n : ℕ∞ω} :
    ContDiffAt ℝ n fixedTargetCoordinates targetColumn := by
  have hs : ContDiffAt ℝ n (stereoToFun (-(localColumn input 0).val))
      (WithLp.toLp 2 targetColumn : QuaternionSpace 1) := by
    rw [targetColumn_toLp]
    exact SphereCenteredCoordinates.contDiffAt_stereoToFun (localColumn input 0)
  exact hs.comp targetColumn PiLp.contDiff_toLp.contDiffAt

theorem fixedTargetCoordinates_target : fixedTargetCoordinates targetColumn = 0 := by
  unfold fixedTargetCoordinates
  rw [targetColumn_toLp]
  exact SphereCenteredCoordinates.chart_self (localColumn input 0)

def signCoordinateMap (x y : Bool) : ParameterSpace rotatedInput → TargetSpace input :=
  fixedTargetCoordinates ∘ signProjection x y

theorem signCoordinateMap_zero (x y : Bool) : signCoordinateMap x y 0 = 0 := by
  change fixedTargetCoordinates (signProjection x y 0) = 0
  rw [signProjection_zero, fixedTargetCoordinates_target]

theorem contDiffAt_signCoordinateMap (x y : Bool) {n : ℕ∞ω} :
    ContDiffAt ℝ n (signCoordinateMap x y) 0 := by
  have hg : ContDiffAt ℝ n fixedTargetCoordinates (signProjection x y 0) := by
    rw [signProjection_zero]
    exact contDiffAt_fixedTargetCoordinates
  exact hg.comp 0 (contDiff_signProjection x y).contDiffAt

theorem signCoordinateMap_fderiv_eq_comp (x y : Bool) :
    fderiv ℝ (signCoordinateMap x y) 0 =
      (fderiv ℝ (signCoordinateMap true true) 0).comp
        (signParameterComparison x y).toContinuousLinearMap :=
  signProjection_postcompose_fderiv fixedTargetCoordinates
    ((contDiffAt_fixedTargetCoordinates (n := 1)).differentiableAt (by decide)) x y

theorem signCoordinateMap_determinant_one_comparison (x y : Bool) :
    ∃ K : ParameterSpace rotatedInput →L[ℝ] ParameterSpace rotatedInput,
      K.det = 1 ∧ fderiv ℝ (signCoordinateMap x y) 0 =
        (fderiv ℝ (signCoordinateMap true true) 0).comp K := by
  refine ⟨(signParameterComparison x y).toContinuousLinearMap, ?_,
    signCoordinateMap_fderiv_eq_comp x y⟩
  exact signParameterComparison_det x y

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
