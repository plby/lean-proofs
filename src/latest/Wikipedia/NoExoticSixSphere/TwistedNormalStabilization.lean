import Wikipedia.NoExoticSixSphere.NormalFrameStabilizationCoordinates

/-!
# Normal stabilization preserves the actual twisted disk-extension obstruction

Fixed source and target coordinate changes identify the twisted normal
stabilization with ordinary block stabilization of the original twisted
operator. These changes are constant over the disk. No extension of the
sphere-dependent source twist is assumed.
-/

noncomputable section

namespace NoExoticSixSphere.NormalFrameStabilization

open GLOrthonormalization Stiefel NormalFrameSourceCoordinates SpanningDiskFrameCoordinates
open DiskBoundary

variable {N k : ℕ}

theorem composed_operator_ext {a b c a' b' c' : ℕ}
    (U : Vector b ≃L[ℝ] Vector c) (A : Vector a →L[ℝ] Vector b)
    (V : Vector c' ≃L[ℝ] Vector a)
    (U' : Vector b' ≃L[ℝ] Vector c) (A' : Vector a' →L[ℝ] Vector b')
    (V' : Vector c' ≃L[ℝ] Vector a')
    (h : ∀ v, U (A (V v)) = U' (A' (V' v))) :
    U.toContinuousLinearMap.comp (A.comp V.toContinuousLinearMap) =
      U'.toContinuousLinearMap.comp (A'.comp V'.toContinuousLinearMap) :=
  ContinuousLinearMap.ext h

def twistedTarget (N d : ℕ) : Vector ((N + 6) + d) ≃L[ℝ] Vector ((N + d) + 6) :=
  (block (targetCoordinates N).symm d).trans
    ((tailSwap N d 6).symm.trans (targetCoordinates (N + d)))

theorem twistedTarget_apply (N d : ℕ) (v : Vector ((N + 6) + d)) :
    twistedTarget N d v = targetCoordinates (N + d)
      ((tailSwap N d 6).symm (block (targetCoordinates N).symm d v)) := by
  simp only [twistedTarget, ContinuousLinearEquiv.trans_apply]

theorem twistedOperator_stabilization_apply (d : ℕ)
    (A : Vector (k + 3) →L[ℝ] Vector N) (s : Sphere 3)
    (v : Vector (((k + d) + 5) + 4)) :
    targetCoordinates (N + d)
        (BlockSum.operator 6 (operator d A) (sourceTwist (k + d) s v)) =
      twistedTarget N d (BlockSum.operator d ((targetCoordinates N).toContinuousLinearMap.comp
        ((BlockSum.operator 6 A).comp (sourceTwist k s).toContinuousLinearMap))
          (twistedSource k d v)) := by
  have he : tailSwap N d 6
      (BlockSum.operator 6 (operator d A) (sourceTwist (k + d) s v)) =
        BlockSum.operator d (BlockSum.operator 6 A)
          (block (sourceTwist k s) d (twistedSource k d v)) := by
    rw [operator, blockSum_comp]
    change tailSwap N d 6 (BlockSum.operator 6 (BlockSum.operator d A)
      (block (tailSwap k d 3) 6 (sourceTwist (k + d) s v))) = _
    rw [block_tailSwap, sourceTwist_stabilization]
  rw [twistedTarget_apply]
  apply congrArg (targetCoordinates (N + d))
  apply (tailSwap N d 6).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, he]
  simp only [block_apply, BlockSum.operator_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem twistedOperator_stabilization (d : ℕ)
    (A : Vector (k + 3) →L[ℝ] Vector N) (s : Sphere 3) :
    (targetCoordinates (N + d)).toContinuousLinearMap.comp
        ((BlockSum.operator 6 (operator d A)).comp
          (sourceTwist (k + d) s).toContinuousLinearMap) =
      (twistedTarget N d).toContinuousLinearMap.comp
        ((BlockSum.operator d ((targetCoordinates N).toContinuousLinearMap.comp
          ((BlockSum.operator 6 A).comp (sourceTwist k s).toContinuousLinearMap))).comp
            (twistedSource k d).toContinuousLinearMap) := by
  apply composed_operator_ext
  exact twistedOperator_stabilization_apply d A s

theorem twistedMap_recoordinate (d : ℕ)
    (F : C(Sphere 3, Monomorphism.Space N (k + 3))) (s : Sphere 3) :
    twistedBlockMap ((map d).comp F) s =
      Monomorphism.recoordinate (twistedTarget N d) (twistedSource k d)
        (Monomorphism.blockMap d (twistedBlockMap F s)) := by
  apply Subtype.ext
  change (targetCoordinates (N + d)).toContinuousLinearMap.comp
      ((BlockSum.operator 6 (operator d (F s).val)).comp
        (sourceTwist (k + d) s).toContinuousLinearMap) =
    (twistedTarget N d).toContinuousLinearMap.comp
      ((BlockSum.operator d (twistedBlockMap F s).val).comp
        (twistedSource k d).toContinuousLinearMap)
  rw [twistedBlockMap_value]
  exact twistedOperator_stabilization d (F s).val s

theorem extends_twisted_stabilization_iff (hN : N = k + 6) (d : ℕ)
    (F : C(Sphere 3, Monomorphism.Space N (k + 3))) :
    Extends (twistedBlockMap ((map d).comp F)) ↔ Extends (twistedBlockMap F) := by
  have he := Monomorphism.extends_recoordinate_iff
    (fun _ ↦ twistedTarget N d) (fun _ ↦ twistedSource k d)
    continuous_const continuous_const continuous_const continuous_const
    ((Monomorphism.blockMap d).comp (twistedBlockMap F))
    (twistedBlockMap ((map d).comp F)) (twistedMap_recoordinate d F)
  exact he.trans (Monomorphism.extends_blockMap_iff (by omega) (by omega) d (twistedBlockMap F))

end NoExoticSixSphere.NormalFrameStabilization
