import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppend
import Wikipedia.NoExoticSixSphere.EuclideanBlockProjection

/-!
# Exact column changes for appending a boundary normal after stabilization

The time-normal column must move past the new ambient coordinate axes.
These fixed Euclidean isometries perform that permutation and extend any
existing column change, without dropping a column or changing its sign.
-/

noncomputable section

namespace NoExoticSixSphere.OrthogonalFrameAppend

open GLOrthonormalization Stiefel

def extendColumnChange {k l : ℕ} (Q : Vector k ≃ₗᵢ[ℝ] Vector l) (m : ℕ) :
    Vector (k + m) ≃ₗᵢ[ℝ] Vector (l + m) :=
  ((EuclideanTailCoordinates.finAdd k m).trans
    (LinearIsometryEquiv.withLpProdCongr 2 Q (LinearIsometryEquiv.refl ℝ (Vector m)))).trans
      (EuclideanTailCoordinates.finAdd l m).symm

theorem extendColumnChange_split {k l : ℕ} (Q : Vector k ≃ₗᵢ[ℝ] Vector l) (m : ℕ)
    (v : Vector (k + m)) :
    EuclideanSpace.finAddEquivProd (extendColumnChange Q m v) =
      (Q (EuclideanSpace.finAddEquivProd v).1, (EuclideanSpace.finAddEquivProd v).2) := by
  change WithLp.ofLp
    (EuclideanTailCoordinates.finAdd l m
      ((EuclideanTailCoordinates.finAdd l m).symm _)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem operator_comp_columnChange {N k l : ℕ} (B : Vector l →L[ℝ] Vector N)
    (Q : Vector k ≃ₗᵢ[ℝ] Vector l) (ν : Vector N) :
    operator (B.comp Q.toContinuousLinearMap) ν =
      (operator B ν).comp (extendColumnChange Q 1).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change operator (B.comp Q.toContinuousLinearMap) ν v =
    operator B ν (extendColumnChange Q 1 v)
  rw [operator_apply, operator_apply, extendColumnChange_split]
  rfl

theorem block_comp_columnChange {N k l : ℕ} (m : ℕ) (B : Vector l →L[ℝ] Vector N)
    (Q : Vector k ≃ₗᵢ[ℝ] Vector l) :
    BlockSum.operator m (B.comp Q.toContinuousLinearMap) =
      (BlockSum.operator m B).comp (extendColumnChange Q m).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change BlockSum.operator m (B.comp Q.toContinuousLinearMap) v =
    BlockSum.operator m B (extendColumnChange Q m v)
  rw [BlockSum.operator_apply, BlockSum.operator_apply, extendColumnChange_split]
  rfl

theorem block_comp_columnChange_symm {N k l : ℕ} (m : ℕ)
    (B : Vector l →L[ℝ] Vector N) (Q : Vector k ≃ₗᵢ[ℝ] Vector l) (w : Vector (l + m)) :
    BlockSum.operator m (B.comp Q.toContinuousLinearMap) ((extendColumnChange Q m).symm w) =
      BlockSum.operator m B w := by
  rw [block_comp_columnChange]
  change BlockSum.operator m B (extendColumnChange Q m ((extendColumnChange Q m).symm w)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

def appendBlockCoordinates (k m : ℕ) : Vector ((k + m) + 1) ≃L[ℝ] Vector ((k + 1) + m) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + m) (m := 1)).trans
    (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := m)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (Vector 1))).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector m) (Vector 1)).trans
          (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
            (ContinuousLinearEquiv.prodComm ℝ (Vector m) (Vector 1))).trans
              ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector 1) (Vector m)).symm.trans
                (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 1)).symm.prodCongr
                  (ContinuousLinearEquiv.refl ℝ (Vector m))).trans
                    EuclideanSpace.finAddEquivProd.symm)))))

theorem appendBlockCoordinates_apply (k m : ℕ) (v : Vector ((k + m) + 1)) :
    appendBlockCoordinates k m v = EuclideanSpace.finAddEquivProd.symm
      (EuclideanSpace.finAddEquivProd.symm
        ((EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd v).1).1,
          (EuclideanSpace.finAddEquivProd v).2),
        (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd v).1).2) := rfl

theorem inner_appendBlockCoordinates (k m : ℕ) (u v : Vector ((k + m) + 1)) :
    inner ℝ (appendBlockCoordinates k m u) (appendBlockCoordinates k m v) =
      inner ℝ u v := by
  rw [appendBlockCoordinates_apply, appendBlockCoordinates_apply,
    inner_finAdd_symm, inner_finAdd_symm, inner_finAdd_split u v,
    inner_finAdd_split (EuclideanSpace.finAddEquivProd u).1
      (EuclideanSpace.finAddEquivProd v).1]
  ring

def appendBlockPermutation (k m : ℕ) :
    Vector ((k + m) + 1) ≃ₗᵢ[ℝ] Vector ((k + 1) + m) where
  toLinearEquiv := (appendBlockCoordinates k m).toLinearEquiv
  norm_map' v := by
    change ‖appendBlockCoordinates k m v‖ = ‖v‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [real_inner_self_eq_norm_sq] using inner_appendBlockCoordinates k m v v

theorem appendBlockPermutation_apply (k m : ℕ) (v : Vector ((k + m) + 1)) :
    appendBlockPermutation k m v = appendBlockCoordinates k m v := rfl

theorem operator_block {N k : ℕ} (m : ℕ) (B : Vector k →L[ℝ] Vector N) (ν : Vector N) :
    operator (BlockSum.operator m B) (appendZeroMap N m ν) =
      (BlockSum.operator m (operator B ν)).comp
        (appendBlockPermutation k m).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change operator (BlockSum.operator m B) (appendZeroMap N m ν) v =
    BlockSum.operator m (operator B ν) (appendBlockPermutation k m v)
  rw [operator_apply, BlockSum.operator_apply,
    appendBlockPermutation_apply, appendBlockCoordinates_apply,
    BlockSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply,
    operator_apply, ContinuousLinearEquiv.apply_symm_apply]
  change EuclideanSpace.finAddEquivProd.symm (_, _) +
    _ • EuclideanSpace.finAddEquivProd.symm (ν, (0 : Vector m)) = _
  rw [← map_smul, ← map_add]
  congr 1
  simp

end NoExoticSixSphere.OrthogonalFrameAppend
