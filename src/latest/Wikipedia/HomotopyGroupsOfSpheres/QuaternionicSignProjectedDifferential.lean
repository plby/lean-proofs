import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSignMatrixFamily

/-!
# The full projected derivatives at the four sign inputs differ by determinant one

Both angular directions are retained. The actual first-column formula in
the sign-transported sphere charts has derivative equal to the seed formula's
derivative composed with the proved determinant-one parameter automorphism.
-/

noncomputable section

open scoped ContDiff Matrix.Norms.Elementwise

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix

local notation "ℍ" => Quaternion ℝ

def signProjection (x y : Bool) (p : ParameterSpace rotatedInput) : Fin 2 → ℍ :=
  firstColumnFormula (Real.pi / 2 + p.1) (Real.pi / 2 + p.2.1) (signMatrixFamily x y p)

theorem signProjection_zero (x y : Bool) : signProjection x y 0 = targetColumn := by
  simp only [signProjection, Prod.fst_zero, Prod.snd_zero, add_zero]
  exact midpoint_target_of_matrix _ (midpointPhases 0) (signMatrixFamily_zero x y)

theorem contDiff_signProjection (x y : Bool) {n : ℕ∞ω} : ContDiff ℝ n (signProjection x y) := by
  apply contDiff_pi.mpr
  intro r
  exact contDiff_firstColumnFormula_entry _ _ _
    (contDiff_const.add contDiff_fst) (contDiff_const.add contDiff_snd.fst)
    (contDiff_signMatrixFamily_entry x y) r

theorem hasDerivAt_signProjection_line (x y : Bool) (v : ParameterSpace rotatedInput) :
    HasDerivAt (fun t : ℝ ↦ signProjection x y (t • v))
      (midpointColumnVariation (angularVelocity v.1 v.2.1) (midpointPhases 0)
        (signMatrixVariation x y v)) 0 := by
  have hs : HasDerivAt (fun t : ℝ ↦ Real.pi / 2 + (t • v).1) v.1 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_add (Real.pi / 2) using 1 <;>
      try rfl
    simp
  have ht : HasDerivAt (fun t : ℝ ↦ Real.pi / 2 + (t • v).2.1) v.2.1 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const v.2.1).const_add (Real.pi / 2) using 1 <;>
      try rfl
    simp
  apply hasDerivAt_pi.mpr
  intro r
  apply hasDerivAt_firstColumn_midpoint
    (fun t : ℝ ↦ Real.pi / 2 + (t • v).1)
    (fun t : ℝ ↦ Real.pi / 2 + (t • v).2.1)
    (fun t : ℝ ↦ signMatrixFamily x y (t • v)) v.1 v.2.1 0 (signMatrixVariation x y v)
    hs ht (hasDerivAt_signMatrixFamily_entry x y v) (by simp) (by simp) (midpointPhases 0)
  rw [zero_smul]
  convert signMatrixFamily_zero x y using 1
  rfl

theorem signProjection_fderiv_apply (x y : Bool) (v : ParameterSpace rotatedInput) :
    fderiv ℝ (signProjection x y) 0 v =
      midpointColumnVariation (angularVelocity v.1 v.2.1) (midpointPhases 0)
        (signMatrixVariation x y v) := by
  have hf := (contDiff_signProjection x y (n := 1)).differentiable (by decide)
  have hfd : HasFDerivAt (signProjection x y) (fderiv ℝ (signProjection x y) 0)
      ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact (hf 0).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ ↦ signProjection x y (t • v))
      (fderiv ℝ (signProjection x y) 0 v) 0 := by
    convert hfd.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;> try rfl
    simp only [one_smul]
  exact hl.unique (hasDerivAt_signProjection_line x y v)

theorem signProjection_fderiv_comparison (x y : Bool) (v : ParameterSpace rotatedInput) :
    fderiv ℝ (signProjection x y) 0 v =
      fderiv ℝ (signProjection true true) 0 (signParameterComparison x y v) := by
  rw [signProjection_fderiv_apply, signProjection_fderiv_apply]
  change midpointColumnVariation (angularVelocity v.1 v.2.1) (midpointPhases 0)
      (signMatrixVariation x y v) =
    midpointColumnVariation (angularVelocity v.1 v.2.1) (midpointPhases 0)
      (signMatrixVariation true true (signParameterComparison x y v))
  rw [signMatrixVariation_comparison]

theorem signProjection_fderiv_eq_comp (x y : Bool) :
    fderiv ℝ (signProjection x y) 0 =
      (fderiv ℝ (signProjection true true) 0).comp
        (signParameterComparison x y).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  exact signProjection_fderiv_comparison x y v

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
