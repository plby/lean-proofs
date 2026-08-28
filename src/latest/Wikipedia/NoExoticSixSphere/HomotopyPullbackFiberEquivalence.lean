import Wikipedia.NoExoticSixSphere.HomotopyPullbackFiberTransport

/-!
# The projection fiber is equivalent to the original map's homotopy fiber

After the explicit transport, the first endpoint is the fixed basepoint
and its outer path is constant. Reversing the remaining inner path gives
the original homotopy fiber. Both inverse homotopies come from the same
transport, including its restriction to the fixed-endpoint subspace.
-/

noncomputable section

open scoped unitInterval ContinuousMap
open Wikipedia.HopfProblem OrbitPair

namespace NoExoticSixSphere.HomotopyPullbackDiagonal

def reversePathMap (Y : Type) [TopologicalSpace Y] : C(C(I, Y), C(I, Y)) :=
  (⟨fun p : C(I, Y) × I ↦ p.1 (unitInterval.symm p.2),
    continuous_eval.comp (continuous_fst.prodMk
      (unitInterval.continuous_symm.comp continuous_snd))⟩ : C(C(I, Y) × I, Y)).curry

theorem reversePathMap_reverse (Y : Type) [TopologicalSpace Y] (p : C(I, Y)) :
    reversePathMap Y (reversePathMap Y p) = p := by
  apply ContinuousMap.ext
  intro t
  change p (unitInterval.symm (unitInterval.symm t)) = p t
  rw [unitInterval.symm_symm]

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (F : C(X, Y)) (x : X)

def fiberInclusion : C(HomotopyFiber.Space F (F x), ProjectionFiber F x) where
  toFun q := ⟨(⟨((x, q.val.1), reversePathMap Y q.val.2),
    (congrArg q.val.2 unitInterval.symm_zero).trans q.property.2,
    (congrArg q.val.2 unitInterval.symm_one).trans q.property.1⟩,
      ContinuousMap.const I x), rfl, rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact ((continuous_const.prodMk (continuous_fst.comp continuous_subtype_val)).prodMk
        ((reversePathMap Y).continuous.comp (continuous_snd.comp continuous_subtype_val)))
    · exact continuous_const

def fiberRetraction : C(ProjectionFiber F x, HomotopyFiber.Space F (F x)) where
  toFun q := ⟨(secondPoint F x q, reversePathMap Y (transportedPaths F x (1, q))),
    (congrArg (transportedPaths F x (1, q)) unitInterval.symm_zero).trans
      ((PathFamilyTransport.family_target F _ _ _ 1 q).trans q.val.1.property.2),
    (congrArg (transportedPaths F x (1, q)) unitInterval.symm_one).trans
      ((PathFamilyTransport.family_source F _ _ _ 1 q).trans (congrArg F q.property.2))⟩
  continuous_toFun := ((secondPoint F x).continuous.prodMk
    ((reversePathMap Y).continuous.comp ((transportedPaths F x).continuous.comp
      (continuous_const.prodMk continuous_id)))).subtype_mk _

theorem fiberInclusion_retraction (q : ProjectionFiber F x) :
    fiberInclusion F x (fiberRetraction F x q) = fiberDeformation F x (1, q) := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext (Prod.ext q.property.2.symm rfl)
      (reversePathMap_reverse Y (transportedPaths F x (1, q)))
  · exact (fiberDeformation_one_basePath F x q).symm

def fiberRetractionHomotopy : (ContinuousMap.id (ProjectionFiber F x)).Homotopy
    ((fiberInclusion F x).comp (fiberRetraction F x)) where
  toContinuousMap := fiberDeformation F x
  map_zero_left := fiberDeformation_zero F x
  map_one_left q := (fiberInclusion_retraction F x q).symm

def restrictedFiberFamily :
    C(I × HomotopyFiber.Space F (F x), HomotopyFiber.Space F (F x)) where
  toFun q := ⟨(q.2.val.1,
    reversePathMap Y (transportedPaths F x (q.1, fiberInclusion F x q.2))), by
      change transportedPaths F x (q.1, fiberInclusion F x q.2) (unitInterval.symm 0) = _
      rw [unitInterval.symm_zero]
      exact (PathFamilyTransport.family_target F _ _ _ q.1 (fiberInclusion F x q.2)).trans
        (fiberInclusion F x q.2).val.1.property.2, by
      change transportedPaths F x (q.1, fiberInclusion F x q.2) (unitInterval.symm 1) = _
      rw [unitInterval.symm_one]
      exact PathFamilyTransport.family_source F _ _ _ q.1 (fiberInclusion F x q.2)⟩
  continuous_toFun := ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
    ((reversePathMap Y).continuous.comp ((transportedPaths F x).continuous.comp
      (continuous_fst.prodMk ((fiberInclusion F x).continuous.comp continuous_snd))))).subtype_mk _

theorem restrictedFiberFamily_zero (q : HomotopyFiber.Space F (F x)) :
    restrictedFiberFamily F x (0, q) = q := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change reversePathMap Y (transportedPaths F x (0, fiberInclusion F x q)) = q.val.2
    have h : transportedPaths F x (0, fiberInclusion F x q) =
        innerPath F x (fiberInclusion F x q) :=
      PathFamilyTransport.family_initial F _ _ _ (fiberInclusion F x q)
    rw [h]
    exact reversePathMap_reverse Y q.val.2

theorem restrictedFiberFamily_one (q : HomotopyFiber.Space F (F x)) :
    restrictedFiberFamily F x (1, q) = fiberRetraction F x (fiberInclusion F x q) := rfl

def restrictedFiberHomotopy : (ContinuousMap.id (HomotopyFiber.Space F (F x))).Homotopy
    ((fiberRetraction F x).comp (fiberInclusion F x)) where
  toContinuousMap := restrictedFiberFamily F x
  map_zero_left := restrictedFiberFamily_zero F x
  map_one_left := restrictedFiberFamily_one F x

def projectionFiberEquiv : ProjectionFiber F x ≃ₕ HomotopyFiber.Space F (F x) where
  toFun := fiberRetraction F x
  invFun := fiberInclusion F x
  left_inv := ⟨(fiberRetractionHomotopy F x).symm⟩
  right_inv := ⟨(restrictedFiberHomotopy F x).symm⟩

theorem fiberRetraction_basepoint :
    fiberRetraction F x (HomotopyFiber.basepoint (left F) (diagonal F x)) =
      HomotopyFiber.basepoint F x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    change (if 2 * (unitInterval.symm t : ℝ) ≤ (1 : ℝ) then F x else F x) = F x
    simp only [ite_self]

end NoExoticSixSphere.HomotopyPullbackDiagonal
