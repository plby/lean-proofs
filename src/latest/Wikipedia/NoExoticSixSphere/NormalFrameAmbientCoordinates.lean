import Wikipedia.NoExoticSixSphere.NormalFrameSourceCoordinates

/-!
# Fixed ambient coordinates preserve the original twisted extension condition

A fixed ambient equivalence extends by identity on the six added axes.
Conjugating by the actual target coordinates identifies the twisted maps.
The resulting coordinate change is constant on the disk, so exact disk
extensions are transported in both directions.
-/

noncomputable section

namespace NoExoticSixSphere.NormalFrameAmbientCoordinates

open GLOrthonormalization Stiefel NormalFrameSourceCoordinates SpanningDiskFrameCoordinates
open DiskBoundary

variable {N N' k : ℕ}

def targetChange (J : Vector N ≃L[ℝ] Vector N') :
    C(Monomorphism.Space N (k + 3), Monomorphism.Space N' (k + 3)) :=
  Monomorphism.recoordinateHomeomorph J (ContinuousLinearEquiv.refl ℝ (Vector (k + 3)))

theorem targetChange_value (J : Vector N ≃L[ℝ] Vector N')
    (A : Monomorphism.Space N (k + 3)) :
    (targetChange J A).val = J.toContinuousLinearMap.comp A.val := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem blockSum_targetChange (J : Vector N ≃L[ℝ] Vector N') {n : ℕ}
    (d : ℕ) (A : Vector n →L[ℝ] Vector N) :
    BlockSum.operator d (J.toContinuousLinearMap.comp A) =
      (block J d).toContinuousLinearMap.comp (BlockSum.operator d A) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [BlockSum.operator_apply, ContinuousLinearMap.comp_apply, block_apply,
    ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

def twistedTarget (J : Vector N ≃L[ℝ] Vector N') : Vector (N + 6) ≃L[ℝ] Vector (N' + 6) :=
  (targetCoordinates N).symm.trans ((block J 6).trans (targetCoordinates N'))

theorem twistedTarget_apply (J : Vector N ≃L[ℝ] Vector N') (v : Vector (N + 6)) :
    twistedTarget J v = targetCoordinates N' (block J 6 ((targetCoordinates N).symm v)) := by
  simp only [twistedTarget, ContinuousLinearEquiv.trans_apply]

theorem twistedMap_recoordinate (J : Vector N ≃L[ℝ] Vector N')
    (F : C(Sphere 3, Monomorphism.Space N (k + 3))) (s : Sphere 3) :
    twistedBlockMap ((targetChange J).comp F) s =
      Monomorphism.recoordinate (twistedTarget J)
        (ContinuousLinearEquiv.refl ℝ (Vector ((k + 5) + 4))) (twistedBlockMap F s) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  simp only [twistedBlockMap_value, ContinuousMap.comp_apply, targetChange_value,
    Monomorphism.recoordinate_apply, ContinuousLinearEquiv.refl_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, twistedTarget_apply,
    ContinuousLinearEquiv.symm_apply_apply, blockSum_targetChange]

theorem extends_twisted_targetChange_iff (J : Vector N ≃L[ℝ] Vector N')
    (F : C(Sphere 3, Monomorphism.Space N (k + 3))) :
    Extends (twistedBlockMap ((targetChange J).comp F)) ↔ Extends (twistedBlockMap F) :=
  Monomorphism.extends_recoordinate_iff (fun _ ↦ twistedTarget J)
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector ((k + 5) + 4)))
    continuous_const continuous_const continuous_const continuous_const
    (twistedBlockMap F) (twistedBlockMap ((targetChange J).comp F)) (twistedMap_recoordinate J F)

end NoExoticSixSphere.NormalFrameAmbientCoordinates
