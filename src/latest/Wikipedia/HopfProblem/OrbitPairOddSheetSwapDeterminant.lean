import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Determinant of interchanging equal-dimensional sheets

The sum-and-difference coordinates conjugate interchange of the two
factors to identity on one factor and negation on the other. Consequently
interchanging two sheets of odd dimension reverses their joint
determinant. This concerns the order of the sheets, not an ambient motion.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.OrbitPair.SheetOrder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem det_prodComm :
    (LinearEquiv.prodComm ℝ E E).toLinearMap.det = (-1 : ℝ) ^ Module.finrank ℝ E := by
  let L : (E × E) →ₗ[ℝ] (E × E) :=
    ((LinearMap.fst ℝ E E) + (LinearMap.snd ℝ E E)).prod
      ((LinearMap.fst ℝ E E) - (LinearMap.snd ℝ E E))
  let R : (E × E) →ₗ[ℝ] (E × E) :=
    (LinearMap.id : E →ₗ[ℝ] E).prodMap (-LinearMap.id)
  have hker : L.ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    have hsum : p.1 + p.2 = 0 := congrArg Prod.fst hp
    have hdiff : p.1 - p.2 = 0 := congrArg Prod.snd hp
    have heq : p.1 = p.2 := sub_eq_zero.mp hdiff
    have hdouble : (2 : ℝ) • p.2 = 0 := by simpa [two_smul, heq] using hsum
    have hp₂ : p.2 = 0 := (smul_eq_zero.mp hdouble).resolve_left (by norm_num)
    exact Prod.ext (heq.trans hp₂) hp₂
  have hdet : L.det ≠ 0 := fun hz => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) hker
  have hcomp : L.comp (LinearEquiv.prodComm ℝ E E).toLinearMap = R.comp L := by
    apply LinearMap.ext
    intro p
    apply Prod.ext
    · change p.2 + p.1 = p.1 + p.2
      abel
    · change p.2 - p.1 = -(p.1 - p.2)
      abel
  have hneg : (-LinearMap.id : E →ₗ[ℝ] E).det = (-1 : ℝ) ^ Module.finrank ℝ E := by
    rw [show (-LinearMap.id : E →ₗ[ℝ] E) = (-1 : ℝ) • LinearMap.id by simp,
      LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hR : R.det = (-1 : ℝ) ^ Module.finrank ℝ E := by
    change ((LinearMap.id : E →ₗ[ℝ] E).prodMap
      (-LinearMap.id : E →ₗ[ℝ] E)).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_id, hneg, one_mul]
  have h := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, LinearMap.det_comp, hR, mul_comm _ L.det] at h
  exact mul_left_cancel₀ hdet h

theorem det_continuous_prodComm :
    (ContinuousLinearEquiv.prodComm ℝ E E).toContinuousLinearMap.det =
      (-1 : ℝ) ^ Module.finrank ℝ E :=
  det_prodComm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem det_coprod_swap (A B : E →L[ℝ] V) (J : (E × E) ≃L[ℝ] V) :
    (J.symm.toContinuousLinearMap.comp (B.coprod A)).det =
      (-1 : ℝ) ^ Module.finrank ℝ E *
        (J.symm.toContinuousLinearMap.comp (A.coprod B)).det := by
  let T : (E × E) →L[ℝ] (E × E) := J.symm.toContinuousLinearMap.comp (A.coprod B)
  let S : (E × E) →L[ℝ] (E × E) :=
    (ContinuousLinearEquiv.prodComm ℝ E E).toContinuousLinearMap
  have h : J.symm.toContinuousLinearMap.comp (B.coprod A) = T.comp S := by
    apply ContinuousLinearMap.ext
    intro p
    change J.symm (B p.1 + A p.2) = J.symm (A p.2 + B p.1)
    rw [add_comm]
  rw [h]
  calc
    (T.comp S).det = T.det * S.det := LinearMap.det_comp _ _
    _ = (-1 : ℝ) ^ Module.finrank ℝ E * T.det := by
      rw [det_continuous_prodComm, mul_comm]

end Wikipedia.HopfProblem.OrbitPair.SheetOrder
