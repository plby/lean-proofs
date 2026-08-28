import Wikipedia.NoExoticSixSphere.NormalFrameAmbientCoordinates

/-!
# Disk-extending ambient coordinates preserve the original twisted extension problem

The ambient coordinate change may vary with the sphere point, provided
it and its inverse are defined continuously over the actual whole disk.
The original source twist is retained; no extension of that twist is
assumed. This applies to globally defined compactification frame families.
-/

noncomputable section

namespace NoExoticSixSphere.NormalFrameAmbientCoordinates

open GLOrthonormalization Stiefel NormalFrameSourceCoordinates SpanningDiskFrameCoordinates
open DiskBoundary Wikipedia.HopfProblem.DegreeCollapse

variable {N N' k : ℕ}

theorem block_symm (J : Vector N ≃L[ℝ] Vector N') (d : ℕ) :
    (block J d).symm = block J.symm d := by
  apply ContinuousLinearEquiv.ext
  rfl

theorem twistedTarget_symm (J : Vector N ≃L[ℝ] Vector N') :
    (twistedTarget J).symm = twistedTarget J.symm := by
  apply ContinuousLinearEquiv.ext
  funext v
  simp only [twistedTarget, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_symm, block_symm]

theorem continuous_twistedTarget {X : Type*} [TopologicalSpace X]
    (J : X → (Vector N ≃L[ℝ] Vector N'))
    (hJ : Continuous (fun x ↦ (J x).toContinuousLinearMap)) :
    Continuous (fun x ↦ (twistedTarget (J x)).toContinuousLinearMap) := by
  apply continuous_clm_apply.mpr
  intro v
  change Continuous (fun x ↦ targetCoordinates N'
    (block (J x) 6 ((targetCoordinates N).symm v)))
  simp_rw [block_apply]
  exact (targetCoordinates N').continuous.comp
    (EuclideanSpace.finAddEquivProd.symm.continuous.comp
      ((hJ.clm_apply continuous_const).prodMk continuous_const))

theorem twistedMap_recoordinate_at (J : Vector N ≃L[ℝ] Vector N')
    (F : C(Sphere 3, Monomorphism.Space N (k + 3)))
    (G : C(Sphere 3, Monomorphism.Space N' (k + 3))) (s : Sphere 3)
    (h : (G s).val = J.toContinuousLinearMap.comp (F s).val) :
    twistedBlockMap G s = Monomorphism.recoordinate (twistedTarget J)
      (ContinuousLinearEquiv.refl ℝ (Vector ((k + 5) + 4))) (twistedBlockMap F s) := by
  have he : twistedBlockMap G s = twistedBlockMap ((targetChange J).comp F) s := by
    apply Subtype.ext
    simp only [twistedBlockMap_value, ContinuousMap.comp_apply, targetChange_value, h]
  exact he.trans (twistedMap_recoordinate J F s)

theorem extends_twisted_diskTarget_iff
    (J : DiskCylinder.Disk (E := Vector 4) → (Vector N ≃L[ℝ] Vector N'))
    (hJ : Continuous (fun x ↦ (J x).toContinuousLinearMap))
    (hJi : Continuous (fun x ↦ (J x).symm.toContinuousLinearMap))
    (F : C(Sphere 3, Monomorphism.Space N (k + 3)))
    (G : C(Sphere 3, Monomorphism.Space N' (k + 3)))
    (h : ∀ s, (G s).val =
      (J (DiskCylinder.boundaryToDisk s)).toContinuousLinearMap.comp (F s).val) :
    Extends (twistedBlockMap G) ↔ Extends (twistedBlockMap F) := by
  apply Monomorphism.extends_recoordinate_iff (fun x ↦ twistedTarget (J x))
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector ((k + 5) + 4)))
    (continuous_twistedTarget J hJ) ?_ continuous_const continuous_const
    (twistedBlockMap F) (twistedBlockMap G)
    (fun s ↦ twistedMap_recoordinate_at _ F G s (h s))
  simpa only [twistedTarget_symm] using continuous_twistedTarget (fun x ↦ (J x).symm) hJi

end NoExoticSixSphere.NormalFrameAmbientCoordinates
