import Wikipedia.HopfProblem.DegreeCollapseMatrixComponentPaths
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Determinant correction in an unused normal direction

A nonzero normal space carries a linear automorphism of any prescribed
nonzero determinant. Applying it only in the normal factor fixes the whole
disk plane and makes a given invertible ambient derivative special-linear.
-/

noncomputable section

open Set Function Matrix

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms

variable {A B ι : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [Fintype ι] [DecidableEq ι]

theorem exists_linearEquiv_with_det (b : Module.Basis ι ℝ B) (i : ι)
    {r : ℝ} (hr : r ≠ 0) : ∃ R : B ≃L[ℝ] B, R.toLinearMap.det = r := by
  let L : B →ₗ[ℝ] B := Matrix.toLin b b (LinearFramePaths.scalarDiagonal i r)
  have hdet : L.det = r := by
    rw [← LinearMap.det_toMatrix b L]
    change Matrix.det (LinearMap.toMatrix b b
      (Matrix.toLin b b (LinearFramePaths.scalarDiagonal i r))) = r
    rw [LinearMap.toMatrix_toLin]
    exact LinearFramePaths.det_scalarDiagonal i r
  have hker : L.ker = ⊥ := by
    by_contra hk
    exact hr (hdet.symm.trans (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk))
  have hi : Injective L := LinearMap.ker_eq_bot.mp hker
  have hbij : Bijective L :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩
  exact ⟨(LinearEquiv.ofBijective L hbij).toContinuousLinearEquiv, hdet⟩

theorem exists_normal_det_correction (b : Module.Basis ι ℝ B) (i : ι)
    (C : (A × B) ≃L[ℝ] (A × B)) :
    ∃ R : B ≃L[ℝ] B,
      (((ContinuousLinearEquiv.refl ℝ A).prodCongr R).toContinuousLinearMap.comp
        C.toContinuousLinearMap).toLinearMap.det = 1 := by
  have hne : C.toLinearMap.det ≠ 0 := C.toLinearEquiv.isUnit_det'.ne_zero
  obtain ⟨R, hR⟩ := exists_linearEquiv_with_det b i (inv_ne_zero hne)
  refine ⟨R, ?_⟩
  change LinearMap.det ((LinearMap.id.prodMap R.toLinearMap).comp C.toLinearMap) = 1
  rw [LinearMap.det_comp, LinearMap.det_prodMap, LinearMap.det_id, one_mul, hR,
    inv_mul_cancel₀ hne]

end Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms
