import Wikipedia.NoExoticSixSphere.CollaredDiskFrameCoordinates
import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockExtension

/-!
# Stabilizing an actual extending disk operator in the collar coordinates

Append the five fixed graph axes and use the actual ordered source and
target equivalences. The resulting operator is exactly the combined
normal-plus-disk operator used by the existing collar homotopy.
This construction transports an operator extension, not an immersed disk.
-/

noncomputable section

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization Stiefel StabilizedSpanningDisk
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {L N k : ℕ}

def stabilizationTarget (C : Vector L ≃L[ℝ] (Vector N × ℝ)) :
    Vector (L + 5) ≃L[ℝ] Vector (N + 6) :=
  EuclideanSpace.finAddEquivProd.trans
    ((C.prodCongr (DiskGraph.extraCoordinates 4).symm).trans (coordinates N 4))

def stabilizationSource (k : ℕ) :
    Vector ((k + 5) + 4) ≃L[ℝ] Vector ((k + 4) + 5) :=
  (sourceCoordinates k).trans
    (((EuclideanSpace.finAddEquivProd (n := k) (m := 4)).symm.prodCongr
      (ContinuousLinearEquiv.refl ℝ (Vector 5))).trans EuclideanSpace.finAddEquivProd.symm)

theorem stabilizationTarget_apply (C : Vector L ≃L[ℝ] (Vector N × ℝ))
    (v : Vector (L + 5)) :
    stabilizationTarget C v = coordinates N 4
      (C (EuclideanSpace.finAddEquivProd v).1,
        (DiskGraph.extraCoordinates 4).symm (EuclideanSpace.finAddEquivProd v).2) := rfl

theorem stabilizationSource_apply (v : Vector ((k + 5) + 4)) :
    stabilizationSource k v = EuclideanSpace.finAddEquivProd.symm
      (EuclideanSpace.finAddEquivProd.symm (sourceCoordinates k v).1,
        (sourceCoordinates k v).2) := rfl

theorem stabilized_operator_eq_combined (C : Vector L ≃L[ℝ] (Vector N × ℝ))
    (A : Vector k →L[ℝ] Vector L) (D : Vector 4 →L[ℝ] Vector L) :
    (stabilizationTarget C).toContinuousLinearMap.comp
      ((BlockSum.operator 5 (OperatorSum.operator A D)).comp
        (stabilizationSource k).toContinuousLinearMap) =
      combined (C.toContinuousLinearMap.comp A) (C.toContinuousLinearMap.comp D) := by
  apply ContinuousLinearMap.ext
  intro v
  change stabilizationTarget C
    (BlockSum.operator 5 (OperatorSum.operator A D) (stabilizationSource k v)) = _
  simp only [stabilizationSource_apply, BlockSum.operator_apply, stabilizationTarget_apply,
    ContinuousLinearEquiv.apply_symm_apply, OperatorSum.operator_apply, combined_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, map_add]

def stabilizationMap (C : Vector L ≃L[ℝ] (Vector N × ℝ)) :
    C(Monomorphism.Space L (k + 4), Monomorphism.Space (N + 6) ((k + 5) + 4)) :=
  (Monomorphism.recoordinateHomeomorph (stabilizationTarget C) (stabilizationSource k) :
    C(Monomorphism.Space (L + 5) ((k + 4) + 5),
      Monomorphism.Space (N + 6) ((k + 5) + 4))).comp (Monomorphism.blockMap 5)

theorem stabilizationMap_value (C : Vector L ≃L[ℝ] (Vector N × ℝ))
    (F : Monomorphism.Space L (k + 4)) :
    (stabilizationMap C F).val = (stabilizationTarget C).toContinuousLinearMap.comp
      ((BlockSum.operator 5 F.val).comp (stabilizationSource k).toContinuousLinearMap) := rfl

theorem stabilizationMap_operator (C : Vector L ≃L[ℝ] (Vector N × ℝ))
    (F : Monomorphism.Space L (k + 4)) (A : Vector k →L[ℝ] Vector L)
    (D : Vector 4 →L[ℝ] Vector L) (hF : F.val = OperatorSum.operator A D) :
    (stabilizationMap C F).val =
      combined (C.toContinuousLinearMap.comp A) (C.toContinuousLinearMap.comp D) := by
  rw [stabilizationMap_value, hF, stabilized_operator_eq_combined]

theorem exists_combined_extension (C : Vector L ≃L[ℝ] (Vector N × ℝ))
    (G : C(Disk (E := Vector 4), Monomorphism.Space L (k + 4)))
    (A : Sphere 3 → Vector k →L[ℝ] Vector L) (D : Sphere 3 → Vector 4 →L[ℝ] Vector L)
    (hG : ∀ s, (G (boundaryToDisk s)).val = OperatorSum.operator (A s) (D s)) :
    ∃ H : C(Disk (E := Vector 4), Monomorphism.Space (N + 6) ((k + 5) + 4)),
      ∀ s, (H (boundaryToDisk s)).val =
        combined (C.toContinuousLinearMap.comp (A s)) (C.toContinuousLinearMap.comp (D s)) :=
  ⟨(stabilizationMap C).comp G, fun s ↦ stabilizationMap_operator C _ (A s) (D s) (hG s)⟩

def normalSourceChange {k' : ℕ} (Q : Vector k' ≃L[ℝ] Vector k) :
    Vector (k' + 4) ≃L[ℝ] Vector (k + 4) :=
  EuclideanSpace.finAddEquivProd.trans
    ((Q.prodCongr (ContinuousLinearEquiv.refl ℝ (Vector 4))).trans
      EuclideanSpace.finAddEquivProd.symm)

theorem normalSourceChange_toContinuousLinearMap {k' : ℕ}
    (Q : Vector k' ≃L[ℝ] Vector k) :
    (normalSourceChange Q).toContinuousLinearMap = BlockSum.operator 4 Q.toContinuousLinearMap :=
  rfl

theorem exists_combined_extension_normal_coordinates {k' : ℕ}
    (C : Vector L ≃L[ℝ] (Vector N × ℝ)) (Q : Vector k' ≃L[ℝ] Vector k)
    (G : C(Disk (E := Vector 4), Monomorphism.Space L (k + 4)))
    (A : Sphere 3 → Vector k →L[ℝ] Vector L) (D : Sphere 3 → Vector 4 →L[ℝ] Vector L)
    (hG : ∀ s, (G (boundaryToDisk s)).val = OperatorSum.operator (A s) (D s)) :
    ∃ H : C(Disk (E := Vector 4), Monomorphism.Space (N + 6) ((k' + 5) + 4)),
      ∀ s, (H (boundaryToDisk s)).val =
        combined (C.toContinuousLinearMap.comp ((A s).comp Q.toContinuousLinearMap))
          (C.toContinuousLinearMap.comp (D s)) := by
  let G' : C(Disk (E := Vector 4), Monomorphism.Space L (k' + 4)) :=
    (Monomorphism.recoordinateHomeomorph (ContinuousLinearEquiv.refl ℝ (Vector L))
      (normalSourceChange Q) :
        C(Monomorphism.Space L (k + 4), Monomorphism.Space L (k' + 4))).comp G
  have hG' : ∀ s, (G' (boundaryToDisk s)).val =
      OperatorSum.operator ((A s).comp Q.toContinuousLinearMap) (D s) := by
    intro s
    change (G (boundaryToDisk s)).val.comp (normalSourceChange Q).toContinuousLinearMap = _
    rw [hG, normalSourceChange_toContinuousLinearMap, OperatorSum.operator_comp_block]
  exact exists_combined_extension C G' (fun s ↦ (A s).comp Q.toContinuousLinearMap) D hG'

end NoExoticSixSphere.CollaredDiskFrame
