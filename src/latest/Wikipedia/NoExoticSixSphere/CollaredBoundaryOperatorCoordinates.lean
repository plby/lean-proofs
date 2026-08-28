import Wikipedia.NoExoticSixSphere.CollaredDiskOperatorStabilization

/-!
# Exact collar coordinates preserve the original boundary extension obstruction

Transport both normal and derivative source coordinates, then append the
five fixed graph axes in the original ordered target coordinates. The
resulting combined operator has its literal prescribed columns. Native
block stabilization and actual coordinate homeomorphisms prove a two-sided
extension equivalence, not just transport of a given disk extension.
-/

noncomputable section

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization Stiefel DiskBoundary

variable {L N k k' : ℕ}

def collarSourceChange (Q : Vector k' ≃L[ℝ] Vector k)
    (R : Vector 4 ≃L[ℝ] Vector 4) : Vector (k' + 4) ≃L[ℝ] Vector (k + 4) :=
  EuclideanSpace.finAddEquivProd.trans ((Q.prodCongr R).trans
    EuclideanSpace.finAddEquivProd.symm)

theorem operator_comp_collarSourceChange (Q : Vector k' ≃L[ℝ] Vector k)
    (R : Vector 4 ≃L[ℝ] Vector 4)
    (A : Vector k →L[ℝ] Vector L) (D : Vector 4 →L[ℝ] Vector L) :
    (OperatorSum.operator A D).comp (collarSourceChange Q R).toContinuousLinearMap =
      OperatorSum.operator (A.comp Q.toContinuousLinearMap) (D.comp R.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  change OperatorSum.operator A D (collarSourceChange Q R v) = _
  simp only [collarSourceChange, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.prodCongr_apply, OperatorSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]

def stabilizationMapCoordinates (C : Vector L ≃L[ℝ] (Vector N × ℝ))
    (Q : Vector k' ≃L[ℝ] Vector k) (R : Vector 4 ≃L[ℝ] Vector 4) :
    C(Monomorphism.Space L (k + 4), Monomorphism.Space (N + 6) ((k' + 5) + 4)) :=
  (stabilizationMap C).comp
    (Monomorphism.recoordinateHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector L))
      (collarSourceChange Q R))

theorem stabilizationMapCoordinates_operator (C : Vector L ≃L[ℝ] (Vector N × ℝ))
    (Q : Vector k' ≃L[ℝ] Vector k) (R : Vector 4 ≃L[ℝ] Vector 4)
    (F : Monomorphism.Space L (k + 4)) (A : Vector k →L[ℝ] Vector L)
    (D : Vector 4 →L[ℝ] Vector L) (hF : F.val = OperatorSum.operator A D) :
    (stabilizationMapCoordinates C Q R F).val =
      combined (C.toContinuousLinearMap.comp (A.comp Q.toContinuousLinearMap))
        (C.toContinuousLinearMap.comp (D.comp R.toContinuousLinearMap)) := by
  apply stabilizationMap_operator C _ _ _
  change F.val.comp (collarSourceChange Q R).toContinuousLinearMap = _
  rw [hF, operator_comp_collarSourceChange]

theorem extends_stabilizationMap_iff (hL : L = 3 + (k + 4))
    (C : Vector L ≃L[ℝ] (Vector N × ℝ)) (F : C(Sphere 3, Monomorphism.Space L (k + 4))) :
    Extends ((stabilizationMap C).comp F) ↔ Extends F := by
  have h : Extends ((stabilizationMap C).comp F) ↔
      Extends ((Monomorphism.blockMap 5).comp F) :=
    Monomorphism.extends_recoordinate_iff (fun _ ↦ stabilizationTarget C)
      (fun _ ↦ stabilizationSource k) continuous_const continuous_const
      continuous_const continuous_const _ _ (fun _ ↦ rfl)
  exact h.trans (Monomorphism.extends_blockMap_iff (by omega) hL 5 F)

theorem extends_stabilizationMapCoordinates_iff (hL : L = 3 + (k + 4))
    (C : Vector L ≃L[ℝ] (Vector N × ℝ))
    (Q : Vector k' ≃L[ℝ] Vector k) (R : Vector 4 ≃L[ℝ] Vector 4)
    (F : C(Sphere 3, Monomorphism.Space L (k + 4))) :
    Extends ((stabilizationMapCoordinates C Q R).comp F) ↔ Extends F := by
  have hk : k' = k := by
    simpa only [finrank_euclideanSpace_fin] using Q.toLinearEquiv.finrank_eq
  let F' : C(Sphere 3, Monomorphism.Space L (k' + 4)) :=
    (Monomorphism.recoordinateHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector L))
      (collarSourceChange Q R) :
        C(Monomorphism.Space L (k + 4), Monomorphism.Space L (k' + 4))).comp F
  change Extends ((stabilizationMap C).comp F') ↔ Extends F
  rw [extends_stabilizationMap_iff (by simpa only [hk] using hL)]
  exact Monomorphism.extends_recoordinate_iff
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector L)) (fun _ ↦ collarSourceChange Q R)
    continuous_const continuous_const continuous_const continuous_const F F' (fun _ ↦ rfl)

end NoExoticSixSphere.CollaredDiskFrame
