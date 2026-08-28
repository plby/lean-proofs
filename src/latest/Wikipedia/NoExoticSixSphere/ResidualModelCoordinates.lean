import Wikipedia.NoExoticSixSphere.ResidualLinkOperators

/-!
# Removing the constant leading block and the positive residual scale

The source change is an actual continuous linear equivalence: apply the
inverse leading block to the first two coordinates and the inverse positive
scale to the last. It changes the constant residual model exactly to the
checked unit residual model.
-/

noncomputable section

namespace NoExoticSixSphere.ResidualCoordinates

open GLOrthonormalization CorankOne CorankOneEuclidean Stiefel

def inverseScale (ε : ℝ) (hε : ε ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toFun t := ε⁻¹ * t
  invFun t := ε * t
  left_inv t := by
    change ε * (ε⁻¹ * t) = t
    rw [← mul_assoc, mul_inv_cancel₀ hε, one_mul]
  right_inv t := by
    change ε⁻¹ * (ε * t) = t
    rw [← mul_assoc, inv_mul_cancel₀ hε, one_mul]
  map_add' x y := mul_add _ _ _
  map_smul' r t := by simp only [RingHom.id_apply, smul_eq_mul]; ring
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def normalizingSource (a : Vector 2 ≃L[ℝ] Vector 2) (ε : ℝ) (hε : ε ≠ 0) :
    Vector 3 ≃L[ℝ] Vector 3 :=
  sourceSplit.trans ((a.symm.prodCongr (inverseScale ε hε)).trans sourceSplit.symm)

theorem normalizingSource_apply (a : Vector 2 ≃L[ℝ] Vector 2) (ε : ℝ) (hε : ε ≠ 0)
    (v : Vector 3) : sourceSplit (normalizingSource a ε hε v) =
      (a.symm (sourceSplit v).1, ε⁻¹ * (sourceSplit v).2) :=
  sourceSplit.apply_symm_apply _

theorem normalized_model_operator (a : Vector 2 ≃L[ℝ] Vector 2) (ε : ℝ) (hε : ε ≠ 0)
    (z : Vector 4) :
    (CorankOneEuclidean.toEuclidean (diagonal a.toContinuousLinearMap (ε • z))).comp
      (normalizingSource a ε hε).toContinuousLinearMap =
        CorankOneEuclidean.toEuclidean (diagonal (ContinuousLinearMap.id ℝ (Vector 2)) z) := by
  apply ContinuousLinearMap.ext
  intro v
  change targetSplit.symm
    (a (sourceSplit (normalizingSource a ε hε v)).1,
      (sourceSplit (normalizingSource a ε hε v)).2 • (ε • z)) =
    targetSplit.symm ((sourceSplit v).1, (sourceSplit v).2 • z)
  rw [normalizingSource_apply, a.apply_symm_apply]
  apply congrArg targetSplit.symm
  apply Prod.ext
  · rfl
  · change (ε⁻¹ * (sourceSplit v).2) • (ε • z) = (sourceSplit v).2 • z
    rw [smul_smul, mul_right_comm, inv_mul_cancel₀ hε, one_mul]

def constantModel (a : Vector 2 ≃L[ℝ] Vector 2) {ε : ℝ} (hε : 0 < ε) :
    C(Sphere 3, Monomorphism.Space 6 3) :=
  monoMap (fun q ↦ diagonal a.toContinuousLinearMap (scaledParameter ε q))
    (fun q ↦ injective_diagonal _ a.injective _ (scaledParameter_ne_zero hε q))
    ((contDiff_diagonal (E := Vector 2) (F := Vector 4)).continuous.comp
      (continuous_const.prodMk (continuous_scaledParameter ε)))

theorem constantModel_change (a : Vector 2 ≃L[ℝ] Vector 2) {ε : ℝ} (hε : 0 < ε) :
    ((Monomorphism.linearHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector 6))
      (normalizingSource a ε hε.ne') : C(_, _)).comp (constantModel a hε)) =
        (Monomorphism.inclusion 6 3).comp WhitneyCusp.simpleFrameMap := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change (CorankOneEuclidean.toEuclidean (diagonal a.toContinuousLinearMap
    (ε • WhitneyCusp.residualCoordinates q.val))).comp
      (normalizingSource a ε hε.ne').toContinuousLinearMap = WhitneyCusp.deformation 0 q.val
  rw [normalized_model_operator, simple_diagonal_eq]

end NoExoticSixSphere.ResidualCoordinates
