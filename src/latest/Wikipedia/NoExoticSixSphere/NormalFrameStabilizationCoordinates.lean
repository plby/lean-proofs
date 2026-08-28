import Wikipedia.NoExoticSixSphere.NormalFrameSourceCoordinates
import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockExtension
import Wikipedia.NoExoticSixSphere.FramedBlockAssociativity

/-!
# Fixed coordinate shuffles for adding normal axes to a sphere operator

The added axes belong to the normal block, before the original three
tangent columns. A fixed tail swap relates this operator to ordinary
block stabilization. A second fixed shuffle moves the added axes past
the graph and radial columns in the genuine source-twisted operator.
-/

noncomputable section

namespace NoExoticSixSphere.NormalFrameStabilization

open GLOrthonormalization Stiefel NormalFrameSourceCoordinates SpanningDiskFrameCoordinates

def tailSwap (k a b : ℕ) : Vector ((k + a) + b) ≃L[ℝ] Vector ((k + b) + a) :=
  EuclideanSpace.finAddEquivProd.trans
    ((EuclideanSpace.finAddEquivProd.prodCongr
      (ContinuousLinearEquiv.refl ℝ (Vector b))).trans
        ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector a) (Vector b)).trans
          (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr
            (ContinuousLinearEquiv.prodComm ℝ (Vector a) (Vector b))).trans
              ((ContinuousLinearEquiv.prodAssoc ℝ (Vector k) (Vector b) (Vector a)).symm.trans
                ((EuclideanSpace.finAddEquivProd.symm.prodCongr
                  (ContinuousLinearEquiv.refl ℝ (Vector a))).trans
                    EuclideanSpace.finAddEquivProd.symm)))))

theorem tailSwap_apply (k a b : ℕ) (v : Vector ((k + a) + b)) :
    tailSwap k a b v = EuclideanSpace.finAddEquivProd.symm
      (EuclideanSpace.finAddEquivProd.symm
        ((EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd v).1).1,
          (EuclideanSpace.finAddEquivProd v).2),
        (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd v).1).2) := rfl

variable {N k : ℕ}

def operator (d : ℕ) (A : Vector (k + 3) →L[ℝ] Vector N) :
    Vector ((k + d) + 3) →L[ℝ] Vector (N + d) :=
  (BlockSum.operator d A).comp (tailSwap k d 3).toContinuousLinearMap

theorem operator_apply (d : ℕ) (A : Vector (k + 3) →L[ℝ] Vector N)
    (v : Vector ((k + d) + 3)) : operator d A v = BlockSum.operator d A (tailSwap k d 3 v) := rfl

theorem operator_sum (d : ℕ) (A : Vector k →L[ℝ] Vector N)
    (T : Vector 3 →L[ℝ] Vector N) :
    operator d (OperatorSum.operator A T) =
      OperatorSum.operator (BlockSum.operator d A) ((appendZeroMap N d).comp T) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [operator_apply, tailSwap_apply, BlockSum.operator_apply, OperatorSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  change EuclideanSpace.finAddEquivProd.symm (_, _) =
    EuclideanSpace.finAddEquivProd.symm (_, _) + EuclideanSpace.finAddEquivProd.symm (_, 0)
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rfl

def map (d : ℕ) :
    C(Monomorphism.Space N (k + 3), Monomorphism.Space (N + d) ((k + d) + 3)) :=
  (Monomorphism.recoordinateHomeomorph
    (ContinuousLinearEquiv.refl ℝ (Vector (N + d))) (tailSwap k d 3) : C(_, _)).comp
      (Monomorphism.blockMap d)

theorem map_value (d : ℕ) (A : Monomorphism.Space N (k + 3)) :
    (map d A).val = operator d A.val := rfl

def twistedSource (k d : ℕ) :
    Vector (((k + d) + 5) + 4) ≃L[ℝ] Vector (((k + 5) + 4) + d) :=
  (block (tailSwap k d 5) 4).trans (tailSwap (k + 5) d 4)

theorem twistedSource_apply (k d : ℕ) (v : Vector (((k + d) + 5) + 4)) :
    twistedSource k d v = EuclideanSpace.finAddEquivProd.symm
      (EuclideanSpace.finAddEquivProd.symm
        (EuclideanSpace.finAddEquivProd.symm
          ((EuclideanSpace.finAddEquivProd
            (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd v).1).1).1,
            (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd v).1).2),
          (EuclideanSpace.finAddEquivProd v).2),
        (EuclideanSpace.finAddEquivProd
          (EuclideanSpace.finAddEquivProd (EuclideanSpace.finAddEquivProd v).1).1).2) := by
  simp only [twistedSource, ContinuousLinearEquiv.trans_apply, block_apply, tailSwap_apply,
    ContinuousLinearEquiv.apply_symm_apply]

theorem sourceTwist_stabilization (d : ℕ) (s : Sphere 3)
    (v : Vector (((k + d) + 5) + 4)) :
    tailSwap (k + 3) d 6 (block (tailSwap k d 3) 6 (sourceTwist (k + d) s v)) =
      block (sourceTwist k s) d (twistedSource k d v) := by
  simp only [sourceTwist_apply, sourceSphere_symm_apply, sourceShuffle_apply,
    tailSwap_apply, block_apply, twistedSource_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem block_tailSwap {n : ℕ} (a b : ℕ) (A : Vector n →L[ℝ] Vector N)
    (v : Vector ((n + a) + b)) :
    tailSwap N a b (BlockSum.operator b (BlockSum.operator a A) v) =
      BlockSum.operator a (BlockSum.operator b A) (tailSwap n a b v) := by
  simp only [tailSwap_apply, BlockSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply]

end NoExoticSixSphere.NormalFrameStabilization
