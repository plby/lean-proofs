import Wikipedia.NoExoticSixSphere.SphereDiskExtension

/-!
# Disk extensions in different linear coordinate presentations

The source and target dimensions need not have definitionally identical
indices. Actual linear equivalences, varying continuously over the entire
disk together with their inverses, preserve exact boundary extension.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization DiskBoundary Topology
open Wikipedia.HopfProblem.DegreeCollapse

variable {N n N' n' : ℕ}

def recoordinate (U : Vector N ≃L[ℝ] Vector N') (V : Vector n' ≃L[ℝ] Vector n)
    (A : Space N n) : Space N' n' :=
  ⟨U.toContinuousLinearMap.comp (A.val.comp V.toContinuousLinearMap),
    U.injective.comp (A.property.comp V.injective)⟩

theorem recoordinate_apply (U : Vector N ≃L[ℝ] Vector N')
    (V : Vector n' ≃L[ℝ] Vector n) (A : Space N n) (w : Vector n') :
    (recoordinate U V A).val w = U (A.val (V w)) := rfl

theorem continuous_recoordinate (U : Vector N ≃L[ℝ] Vector N')
    (V : Vector n' ≃L[ℝ] Vector n) : Continuous (recoordinate U V) :=
  (continuous_const.clm_comp (continuous_subtype_val.clm_comp continuous_const)).subtype_mk _

def recoordinateHomeomorph (U : Vector N ≃L[ℝ] Vector N')
    (V : Vector n' ≃L[ℝ] Vector n) : Space N n ≃ₜ Space N' n' where
  toFun := recoordinate U V
  invFun := recoordinate U.symm V.symm
  left_inv A := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro w
    simp only [recoordinate_apply, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  right_inv A := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro w
    simp only [recoordinate_apply, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  continuous_toFun := continuous_recoordinate U V
  continuous_invFun := continuous_recoordinate U.symm V.symm

theorem extends_recoordinate_iff
    (U : DiskCylinder.Disk (E := Vector 4) → (Vector N ≃L[ℝ] Vector N'))
    (V : DiskCylinder.Disk (E := Vector 4) → (Vector n' ≃L[ℝ] Vector n))
    (hU : Continuous (fun x ↦ (U x).toContinuousLinearMap))
    (hUi : Continuous (fun x ↦ (U x).symm.toContinuousLinearMap))
    (hV : Continuous (fun x ↦ (V x).toContinuousLinearMap))
    (hVi : Continuous (fun x ↦ (V x).symm.toContinuousLinearMap))
    (f : C(Sphere 3, Space N n)) (g : C(Sphere 3, Space N' n'))
    (hfg : ∀ s, g s = recoordinate (U (DiskCylinder.boundaryToDisk s))
      (V (DiskCylinder.boundaryToDisk s)) (f s)) : Extends g ↔ Extends f := by
  apply extends_diskHomeomorph_iff (fun x ↦ recoordinateHomeomorph (U x) (V x))
    ?_ ?_ f g hfg
  · apply IsInducing.subtypeVal.continuous_iff.mpr
    exact (hU.comp continuous_fst).clm_comp
      ((continuous_subtype_val.comp continuous_snd).clm_comp (hV.comp continuous_fst))
  · apply IsInducing.subtypeVal.continuous_iff.mpr
    exact (hUi.comp continuous_fst).clm_comp
      ((continuous_subtype_val.comp continuous_snd).clm_comp (hVi.comp continuous_fst))

end NoExoticSixSphere.Stiefel.Monomorphism
