import Wikipedia.NoExoticSixSphere.StabilizedResidualCoordinates

/-!
# The actual constant-leading residual model has nonzero obstruction

An invertible source change removes its actual constant leading operator
and its positive residual scale. The resulting map is exactly the checked
identity-column stabilization, so an extension of this model would give an
extension of the original nonextending cusp frame.
-/

noncomputable section

namespace NoExoticSixSphere.StabilizedResidual

open GLOrthonormalization CorankOne Stiefel ResidualCoordinates DiskBoundary

def normalizingSource (k : ℕ) (a : Vector (k + 2) ≃L[ℝ] Vector (k + 2))
    (ε : ℝ) (hε : ε ≠ 0) : Vector (k + 3) ≃L[ℝ] Vector (k + 3) :=
  (sourceSplit k).trans ((a.symm.prodCongr (inverseScale ε hε)).trans (sourceSplit k).symm)

theorem normalizingSource_apply (k : ℕ) (a : Vector (k + 2) ≃L[ℝ] Vector (k + 2))
    (ε : ℝ) (hε : ε ≠ 0) (v : Vector (k + 3)) :
    sourceSplit k (normalizingSource k a ε hε v) =
      (a.symm (sourceSplit k v).1, ε⁻¹ * (sourceSplit k v).2) :=
  (sourceSplit k).apply_symm_apply _

theorem normalized_model_operator (k : ℕ) (a : Vector (k + 2) ≃L[ℝ] Vector (k + 2))
    (ε : ℝ) (hε : ε ≠ 0) (z : Vector 4) :
    (toEuclidean k (diagonal a.toContinuousLinearMap (ε • z))).comp
      (normalizingSource k a ε hε).toContinuousLinearMap =
        toEuclidean k (diagonal (ContinuousLinearMap.id ℝ (Vector (k + 2))) z) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    toEuclidean_apply, normalizingSource_apply, diagonal_apply,
    ContinuousLinearMap.id_apply, a.apply_symm_apply]
  apply congrArg (targetSplit k).symm
  apply Prod.ext
  · rfl
  · change (ε⁻¹ * (sourceSplit k v).2) • (ε • z) = (sourceSplit k v).2 • z
    rw [smul_smul, mul_right_comm, inv_mul_cancel₀ hε, one_mul]

def constantModel (k : ℕ) (a : Vector (k + 2) ≃L[ℝ] Vector (k + 2))
    {ε : ℝ} (hε : 0 < ε) : C(Sphere 3, Monomorphism.Space (k + 6) (k + 3)) :=
  monoMap k (fun q ↦ diagonal a.toContinuousLinearMap (scaledParameter ε q))
    (fun q ↦ injective_diagonal _ a.injective _ (scaledParameter_ne_zero hε q))
    ((contDiff_diagonal (E := Vector (k + 2)) (F := Vector 4)).continuous.comp
      (continuous_const.prodMk (continuous_scaledParameter ε)))

theorem constantModel_change (k : ℕ) (a : Vector (k + 2) ≃L[ℝ] Vector (k + 2))
    {ε : ℝ} (hε : 0 < ε) :
    ((Monomorphism.linearHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector (k + 6)))
      (normalizingSource k a ε hε.ne') : C(_, _)).comp (constantModel k a hε)) =
        unitModel k := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change (toEuclidean k (diagonal a.toContinuousLinearMap
    (ε • WhitneyCusp.residualCoordinates q.val))).comp
      (normalizingSource k a ε hε.ne').toContinuousLinearMap = (unitModel k q).val
  rw [normalized_model_operator, unitModel_value]

theorem constantModel_not_extends (k : ℕ) (a : Vector (k + 2) ≃L[ℝ] Vector (k + 2))
    {ε : ℝ} (hε : 0 < ε) : ¬ Extends (constantModel k a hε) := by
  rintro ⟨G, hG⟩
  apply unitModel_not_extends k
  rw [← constantModel_change k a hε]
  let H : C(Monomorphism.Space (k + 6) (k + 3), Monomorphism.Space (k + 6) (k + 3)) :=
    Monomorphism.linearHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector (k + 6)))
      (normalizingSource k a ε hε.ne')
  exact ⟨H.comp G, fun q ↦ congrArg H (hG q)⟩

end NoExoticSixSphere.StabilizedResidual
