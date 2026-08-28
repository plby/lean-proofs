import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

/-! # Relative derivative determinants under fixed coordinate changes -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.LocalBoundaryComparison

variable {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem relativeDet_transport (A B : E ≃L[ℝ] F) (P : D ≃L[ℝ] E) (Q : F ≃L[ℝ] G) :
    (((P.trans A).trans Q).trans ((P.trans B).trans Q).symm).toLinearMap.det =
      (A.trans B.symm).toLinearMap.det := by
  have h : (((P.trans A).trans Q).trans ((P.trans B).trans Q).symm).toLinearMap =
      P.symm.toLinearMap.comp ((A.trans B.symm).toLinearMap.comp P.toLinearMap) := by
    apply LinearMap.ext
    intro v
    change P.symm (B.symm (Q.symm (Q (A (P v))))) = P.symm (B.symm (A (P v)))
    rw [Q.symm_apply_apply]
  rw [h]
  exact LinearMap.det_conj (A.trans B.symm).toLinearMap P.symm.toLinearEquiv

theorem relativeDet_trans (A B C : E ≃L[ℝ] F) :
    (A.trans C.symm).toLinearMap.det =
      (B.trans C.symm).toLinearMap.det * (A.trans B.symm).toLinearMap.det := by
  have h : (A.trans C.symm).toLinearMap =
      (B.trans C.symm).toLinearMap.comp (A.trans B.symm).toLinearMap := by
    apply LinearMap.ext
    intro v
    change C.symm (A v) = C.symm (B (B.symm (A v)))
    rw [B.apply_symm_apply]
  rw [h, LinearMap.det_comp]

theorem relativeDet_pos_trans (A B C : E ≃L[ℝ] F)
    (hAB : 0 < (A.trans B.symm).toLinearMap.det)
    (hBC : 0 < (B.trans C.symm).toLinearMap.det) :
    0 < (A.trans C.symm).toLinearMap.det := by
  rw [relativeDet_trans A B C]
  exact mul_pos hBC hAB

end Wikipedia.HomotopyGroupsOfSpheres.LocalBoundaryComparison
