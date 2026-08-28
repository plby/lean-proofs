import Wikipedia.NoExoticSixSphere.CollaredDiskOperatorStabilization

/-!
# Actual target-coordinate changes of the stabilized collar operator

Apply a fixed equivalence to the ambient-plus-height factor while retaining
the five graph axes. This induces a genuine equivalence of the actual
combined target and transports any operator extension with exact values.
-/

noncomputable section

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization Stiefel StabilizedSpanningDisk
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {N k : ℕ}

def combinedTargetChange (L : (Vector N × ℝ) ≃L[ℝ] (Vector N × ℝ)) :
    Vector (N + 6) ≃L[ℝ] Vector (N + 6) :=
  (coordinates N 4).symm.trans
    ((L.prodCongr (ContinuousLinearEquiv.refl ℝ (ℝ × Vector 4))).trans (coordinates N 4))

theorem combinedTargetChange_apply (L : (Vector N × ℝ) ≃L[ℝ] (Vector N × ℝ))
    (v : Vector (N + 6)) :
    combinedTargetChange L v = coordinates N 4
      (L ((coordinates N 4).symm v).1, ((coordinates N 4).symm v).2) := rfl

theorem combinedTargetChange_comp (L : (Vector N × ℝ) ≃L[ℝ] (Vector N × ℝ))
    (A : Vector k →L[ℝ] (Vector N × ℝ)) (D : Vector 4 →L[ℝ] (Vector N × ℝ)) :
    (combinedTargetChange L).toContinuousLinearMap.comp (combined A D) =
      combined (L.toContinuousLinearMap.comp A) (L.toContinuousLinearMap.comp D) := by
  apply ContinuousLinearMap.ext
  intro v
  change combinedTargetChange L (combined A D v) = _
  simp only [combinedTargetChange_apply, combined_apply,
    ContinuousLinearEquiv.symm_apply_apply, map_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]

def combinedTargetMap (L : (Vector N × ℝ) ≃L[ℝ] (Vector N × ℝ)) :
    C(Monomorphism.Space (N + 6) ((k + 5) + 4),
      Monomorphism.Space (N + 6) ((k + 5) + 4)) :=
  Monomorphism.recoordinateHomeomorph (combinedTargetChange L)
    (ContinuousLinearEquiv.refl ℝ (Vector ((k + 5) + 4)))

theorem combinedTargetMap_operator (L : (Vector N × ℝ) ≃L[ℝ] (Vector N × ℝ))
    (F : Monomorphism.Space (N + 6) ((k + 5) + 4))
    (A : Vector k →L[ℝ] (Vector N × ℝ)) (D : Vector 4 →L[ℝ] (Vector N × ℝ))
    (hF : F.val = combined A D) :
    (combinedTargetMap L F).val =
      combined (L.toContinuousLinearMap.comp A) (L.toContinuousLinearMap.comp D) := by
  change (combinedTargetChange L).toContinuousLinearMap.comp
    (F.val.comp (ContinuousLinearMap.id ℝ _)) = _
  rw [ContinuousLinearMap.comp_id, hF, combinedTargetChange_comp]

end NoExoticSixSphere.CollaredDiskFrame
