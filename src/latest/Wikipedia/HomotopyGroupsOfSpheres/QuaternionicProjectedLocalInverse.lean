import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicProjectedTargetCoordinates
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# A local inverse at every selected-target preimage

Both coordinate spaces have real dimension seven. The proved injective
differential is therefore an isomorphism, so the inverse function theorem
gives an actual open partial homeomorphism with the original coordinate
map as its forward function. No orientation or local-degree sign is assumed.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix QuaternionicColumns

theorem parameterSpace_finrank (z : UnitSphere) :
    Module.finrank ℝ (ParameterSpace z) = 7 := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin 3)) = 6 := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin 3 → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  let : Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 3)) = 5 + 1) := ⟨hdim⟩
  have ht := SphereCenteredCoordinates.tangent_finrank z (n := 5)
  simp only [ParameterSpace, Module.finrank_prod, Module.finrank_self, ht]

theorem targetSpace_finrank (z : UnitSphere) : Module.finrank ℝ (TargetSpace z) = 7 := by
  let : Fact (Module.finrank ℝ (QuaternionSpace 1) = 7 + 1) :=
    ⟨by simpa using quaternionSpace_finrank 1⟩
  exact SphereCenteredCoordinates.tangent_finrank (localColumn z 0)

def localCoordinateDerivativeEquiv (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    ParameterSpace z ≃L[ℝ] TargetSpace z :=
  ((fderiv ℝ (localCoordinateMap z) 0).toLinearMap.linearEquivOfInjective
    (localCoordinateMap_fderiv_injective z hz)
    (by rw [parameterSpace_finrank, targetSpace_finrank])).toContinuousLinearEquiv

theorem localCoordinateDerivativeEquiv_apply (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (v : ParameterSpace z) :
    localCoordinateDerivativeEquiv z hz v = fderiv ℝ (localCoordinateMap z) 0 v := rfl

theorem hasFDerivAt_localCoordinateDerivativeEquiv (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    HasFDerivAt (localCoordinateMap z)
      (localCoordinateDerivativeEquiv z hz : ParameterSpace z →L[ℝ] TargetSpace z) 0 := by
  have he : (localCoordinateDerivativeEquiv z hz : ParameterSpace z →L[ℝ] TargetSpace z) =
      fderiv ℝ (localCoordinateMap z) 0 := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [he]
  exact ((contDiffAt_localCoordinateMap z (n := 1)).differentiableAt (by decide)).hasFDerivAt

def projectedLocalHomeomorph (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    OpenPartialHomeomorph (ParameterSpace z) (TargetSpace z) :=
  (contDiffAt_localCoordinateMap z (n := 1)).toOpenPartialHomeomorph _
    (hasFDerivAt_localCoordinateDerivativeEquiv z hz) (by decide)

theorem projectedLocalHomeomorph_apply (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (p : ParameterSpace z) : projectedLocalHomeomorph z hz p = localCoordinateMap z p := rfl

theorem zero_mem_projectedLocalHomeomorph_source (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    0 ∈ (projectedLocalHomeomorph z hz).source :=
  (contDiffAt_localCoordinateMap z (n := 1)).mem_toOpenPartialHomeomorph_source
    (hasFDerivAt_localCoordinateDerivativeEquiv z hz) (by decide)

theorem zero_mem_projectedLocalHomeomorph_target (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    0 ∈ (projectedLocalHomeomorph z hz).target := by
  have he := (projectedLocalHomeomorph z hz).map_source
    (zero_mem_projectedLocalHomeomorph_source z hz)
  simpa only [projectedLocalHomeomorph_apply, localCoordinateMap_zero] using he

theorem projectedLocalHomeomorph_symm_zero (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    (projectedLocalHomeomorph z hz).symm 0 = 0 := by
  have he := (projectedLocalHomeomorph z hz).left_inv
    (zero_mem_projectedLocalHomeomorph_source z hz)
  simpa only [projectedLocalHomeomorph_apply, localCoordinateMap_zero] using he

theorem contDiffAt_projectedLocalHomeomorph_symm (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    {n : ℕ∞ω} : ContDiffAt ℝ n (projectedLocalHomeomorph z hz).symm 0 := by
  apply (projectedLocalHomeomorph z hz).contDiffAt_symm
    (zero_mem_projectedLocalHomeomorph_target z hz)
    (f₀' := localCoordinateDerivativeEquiv z hz)
  · rw [projectedLocalHomeomorph_symm_zero]
    convert hasFDerivAt_localCoordinateDerivativeEquiv z hz using 1 <;> rfl
  · rw [projectedLocalHomeomorph_symm_zero]
    change ContDiffAt ℝ n (localCoordinateMap z) 0
    exact contDiffAt_localCoordinateMap z

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
