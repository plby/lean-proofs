import Wikipedia.NoExoticSixSphere.SpanningDiskSourceTwist
import Wikipedia.NoExoticSixSphere.InjectiveOperatorExtensionCoordinates

/-!
# Fixed normal-coordinate changes through the actual sphere-dependent source twist

Only the original normal block is changed. The derivative and all added
axes are fixed. The original source twist therefore intertwines two
explicit CONSTANT block equivalences. This transports exact disk
extensions in both directions without extending the source twist, or
assuming that the normal-coordinate change is orientation preserving.
-/

noncomputable section

namespace NoExoticSixSphere.NormalFrameSourceCoordinates

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates DiskBoundary

variable {k k' N : ℕ}

def block (Q : Vector k' ≃L[ℝ] Vector k) (d : ℕ) :
    Vector (k' + d) ≃L[ℝ] Vector (k + d) :=
  EuclideanSpace.finAddEquivProd.trans
    ((Q.prodCongr (ContinuousLinearEquiv.refl ℝ (Vector d))).trans
      EuclideanSpace.finAddEquivProd.symm)

theorem block_apply (Q : Vector k' ≃L[ℝ] Vector k) (d : ℕ) (v : Vector (k' + d)) :
    block Q d v = EuclideanSpace.finAddEquivProd.symm
      (Q (EuclideanSpace.finAddEquivProd v).1, (EuclideanSpace.finAddEquivProd v).2) := rfl

theorem operatorSum_comp_block (Q : Vector k' ≃L[ℝ] Vector k) {d : ℕ}
    (A : Vector k →L[ℝ] Vector N) (B : Vector d →L[ℝ] Vector N) :
    (OperatorSum.operator A B).comp (block Q d).toContinuousLinearMap =
      OperatorSum.operator (A.comp Q.toContinuousLinearMap) B := by
  apply ContinuousLinearMap.ext
  intro v
  change OperatorSum.operator A B (block Q d v) = _
  rw [block_apply, OperatorSum.operator_apply, ContinuousLinearEquiv.apply_symm_apply,
    OperatorSum.operator_apply]
  rfl

theorem blockSum_comp (Q : Vector k' ≃L[ℝ] Vector k) (d : ℕ)
    (A : Vector k →L[ℝ] Vector N) :
    BlockSum.operator d (A.comp Q.toContinuousLinearMap) =
      (BlockSum.operator d A).comp (block Q d).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change BlockSum.operator d (A.comp Q.toContinuousLinearMap) v =
    BlockSum.operator d A (block Q d v)
  rw [BlockSum.operator_apply, block_apply, BlockSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply]
  rfl

def twistedBlock (Q : Vector k' ≃L[ℝ] Vector k) :
    Vector ((k' + 5) + 4) ≃L[ℝ] Vector ((k + 5) + 4) := block (block Q 5) 4

theorem sourceTwist_block (Q : Vector k' ≃L[ℝ] Vector k) (s : Sphere 3)
    (v : Vector ((k' + 5) + 4)) :
    sourceTwist k s (twistedBlock Q v) = block (block Q 3) 6 (sourceTwist k' s v) := by
  simp only [twistedBlock, sourceTwist_apply, sourceSphere_symm_apply, sourceShuffle_apply,
    block_apply, ContinuousLinearEquiv.apply_symm_apply]

def sourceChange (Q : Vector k' ≃L[ℝ] Vector k) :
    C(Monomorphism.Space N (k + 3), Monomorphism.Space N (k' + 3)) :=
  Monomorphism.recoordinateHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector N)) (block Q 3)

theorem sourceChange_value (Q : Vector k' ≃L[ℝ] Vector k)
    (A : Monomorphism.Space N (k + 3)) :
    (sourceChange Q A).val = A.val.comp (block Q 3).toContinuousLinearMap := rfl

def twistedSourceChange (Q : Vector k' ≃L[ℝ] Vector k) :
    C(Monomorphism.Space (N + 6) ((k + 5) + 4),
      Monomorphism.Space (N + 6) ((k' + 5) + 4)) :=
  Monomorphism.recoordinateHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector (N + 6)))
    (twistedBlock Q)

theorem twistedSourceChange_value (Q : Vector k' ≃L[ℝ] Vector k)
    (A : Monomorphism.Space (N + 6) ((k + 5) + 4)) :
    (twistedSourceChange Q A).val = A.val.comp (twistedBlock Q).toContinuousLinearMap := rfl

theorem twistedOperator_sourceChange (Q : Vector k' ≃L[ℝ] Vector k)
    (A : Vector (k + 3) →L[ℝ] Vector N) (s : Sphere 3) :
    (targetCoordinates N).toContinuousLinearMap.comp
      ((BlockSum.operator 6 (A.comp (block Q 3).toContinuousLinearMap)).comp
        (sourceTwist k' s).toContinuousLinearMap) =
    ((targetCoordinates N).toContinuousLinearMap.comp
      ((BlockSum.operator 6 A).comp (sourceTwist k s).toContinuousLinearMap)).comp
        (twistedBlock Q).toContinuousLinearMap := by
  have hs : (block (block Q 3) 6).toContinuousLinearMap.comp
      (sourceTwist k' s).toContinuousLinearMap =
    (sourceTwist k s).toContinuousLinearMap.comp (twistedBlock Q).toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro v
    exact (sourceTwist_block Q s v).symm
  rw [blockSum_comp]
  simp only [ContinuousLinearMap.comp_assoc, hs]

theorem twistedBlockMap_sourceChange (Q : Vector k' ≃L[ℝ] Vector k)
    (F : C(Sphere 3, Monomorphism.Space N (k + 3))) :
    twistedBlockMap ((sourceChange Q).comp F) =
      (twistedSourceChange Q).comp (twistedBlockMap F) := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  simp only [twistedBlockMap_value, ContinuousMap.comp_apply, sourceChange_value,
    twistedSourceChange_value]
  exact twistedOperator_sourceChange Q (F s).val s

theorem extends_twisted_sourceChange_iff (Q : Vector k' ≃L[ℝ] Vector k)
    (F : C(Sphere 3, Monomorphism.Space N (k + 3))) :
    Extends (twistedBlockMap ((sourceChange Q).comp F)) ↔ Extends (twistedBlockMap F) := by
  rw [twistedBlockMap_sourceChange]
  exact Monomorphism.extends_recoordinate_iff
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector (N + 6))) (fun _ ↦ twistedBlock Q)
    continuous_const continuous_const continuous_const continuous_const
    (twistedBlockMap F) ((twistedSourceChange Q).comp (twistedBlockMap F)) (fun _ ↦ rfl)

end NoExoticSixSphere.NormalFrameSourceCoordinates
