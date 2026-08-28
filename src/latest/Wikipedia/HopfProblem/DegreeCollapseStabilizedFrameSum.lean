import Wikipedia.NoExoticSixSphere.RoundedTraceOriginalFrameStabilization

/-!
# Explicit constant coordinates for the retained normal-plus-tangent frame

The negative outward height column is a fixed reflection of the original
end-column convention. A fixed permutation moves the added normal axes
past the original three tangent columns. These are actual continuous
linear equivalences, and the operator identities retain every column.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.FrameStabilization

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open StabilizedSpanningDisk

theorem isometry_trans_clm {n m l : ℕ} (L : Vector n ≃ₗᵢ[ℝ] Vector m)
    (R : Vector m ≃L[ℝ] Vector l) :
    (L.toContinuousLinearEquiv.trans R).toContinuousLinearMap =
      R.toContinuousLinearMap.comp L.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  rfl

def flipLast (k : ℕ) : Vector (k + 1) ≃L[ℝ] Vector (k + 1) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := 1)).trans
    (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
      (ContinuousLinearEquiv.neg ℝ : Vector 1 ≃L[ℝ] Vector 1)).trans
        EuclideanSpace.finAddEquivProd.symm)

theorem flipLast_apply (k : ℕ) (w : Vector (k + 1)) :
    flipLast k w = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd w).1, -(EuclideanSpace.finAddEquivProd w).2) := rfl

theorem append_negative {N k : ℕ} (B : Vector k →L[ℝ] Vector N) (ν : Vector N) :
    OrthogonalFrameAppend.operator B (-ν) =
      (OrthogonalFrameAppend.operator B ν).comp (flipLast k).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  change OrthogonalFrameAppend.operator B (-ν) w =
    OrthogonalFrameAppend.operator B ν (flipLast k w)
  rw [flipLast_apply, OrthogonalFrameAppend.operator_apply, OrthogonalFrameAppend.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  simp only [map_neg, neg_smul, smul_neg]

def negativeEndCoordinates (k : ℕ) : Vector ((k + 5) + 1) ≃L[ℝ] Vector (k + 6) :=
  (flipLast (k + 5)).trans (endColumnPermutation k).toContinuousLinearEquiv

theorem append_negative_height_eq_block {N k : ℕ} (B : Vector k →L[ℝ] Vector N) :
    OrthogonalFrameAppend.operator (boundaryFrameOperator B) (-heightUnit N) =
      (Stiefel.BlockSum.operator 6 B).comp (negativeEndCoordinates k).toContinuousLinearMap := by
  rw [append_negative, append_heightUnit_eq_block]
  rfl

def sumCoordinates (k n m : ℕ) : Vector ((k + m) + n) ≃L[ℝ] Vector ((k + n) + m) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + m) (m := n)).trans
    (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := m)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (Vector n))).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector m) (Vector n)).trans
          (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
            (ContinuousLinearEquiv.prodComm ℝ (Vector m) (Vector n))).trans
              ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector n) (Vector m)).symm.trans
                (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := n)).symm.prodCongr
                  (ContinuousLinearEquiv.refl ℝ (Vector m))).trans
                    EuclideanSpace.finAddEquivProd.symm)))))

theorem sumCoordinates_apply (k n m : ℕ) (w : Vector ((k + m) + n)) :
    sumCoordinates k n m w = EuclideanSpace.finAddEquivProd.symm
      (EuclideanSpace.finAddEquivProd.symm
        ((EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).1,
          (EuclideanSpace.finAddEquivProd w).2),
        (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd w).1).2) := rfl

theorem operatorSum_stabilized {N k n : ℕ} (m : ℕ)
    (B : Vector k →L[ℝ] Vector N) (D : Vector n →L[ℝ] Vector N) :
    OperatorSum.operator (Stiefel.BlockSum.operator m B) ((appendZeroMap N m).comp D) =
      (Stiefel.BlockSum.operator m (OperatorSum.operator B D)).comp
        (sumCoordinates k n m).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  change OperatorSum.operator (Stiefel.BlockSum.operator m B) ((appendZeroMap N m).comp D) w =
    Stiefel.BlockSum.operator m (OperatorSum.operator B D) (sumCoordinates k n m w)
  simp only [OperatorSum.operator_apply, Stiefel.BlockSum.operator_apply, sumCoordinates_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  change EuclideanSpace.finAddEquivProd.symm (_, _) +
    EuclideanSpace.finAddEquivProd.symm (_, (0 : Vector m)) =
      EuclideanSpace.finAddEquivProd.symm (_ + _, _)
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rfl

def sourceCoordinates {k n m r : ℕ} (L : Vector r ≃L[ℝ] Vector (k + m)) :
    Vector (r + n) ≃L[ℝ] Vector ((k + n) + m) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := r) (m := n)).trans
    ((L.prodCongr (ContinuousLinearEquiv.refl ℝ (Vector n))).trans
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k + m) (m := n)).symm.trans
        (sumCoordinates k n m)))

theorem sourceCoordinates_apply {k n m r : ℕ} (L : Vector r ≃L[ℝ] Vector (k + m))
    (w : Vector (r + n)) : sourceCoordinates (n := n) L w =
      sumCoordinates k n m (EuclideanSpace.finAddEquivProd.symm
        (L (EuclideanSpace.finAddEquivProd w).1, (EuclideanSpace.finAddEquivProd w).2)) := rfl

theorem operatorSum_stabilized_recoordinate {N k n m r : ℕ}
    (B : Vector k →L[ℝ] Vector N) (D : Vector n →L[ℝ] Vector N)
    (L : Vector r ≃L[ℝ] Vector (k + m)) :
    OperatorSum.operator ((Stiefel.BlockSum.operator m B).comp L.toContinuousLinearMap)
      ((appendZeroMap N m).comp D) =
      (Stiefel.BlockSum.operator m (OperatorSum.operator B D)).comp
        (sourceCoordinates (n := n) L).toContinuousLinearMap := by
  rw [← OperatorSum.operator_comp_block, operatorSum_stabilized]
  apply ContinuousLinearMap.ext
  intro w
  change Stiefel.BlockSum.operator m (OperatorSum.operator B D)
      (sumCoordinates k n m (Stiefel.BlockSum.operator n L.toContinuousLinearMap w)) =
    Stiefel.BlockSum.operator m (OperatorSum.operator B D) (sourceCoordinates (n := n) L w)
  have hi : Stiefel.BlockSum.operator n L.toContinuousLinearMap w =
      EuclideanSpace.finAddEquivProd.symm
        (L (EuclideanSpace.finAddEquivProd w).1, (EuclideanSpace.finAddEquivProd w).2) := rfl
  rw [sourceCoordinates_apply, hi]

end Wikipedia.HopfProblem.DegreeCollapse.FrameStabilization
