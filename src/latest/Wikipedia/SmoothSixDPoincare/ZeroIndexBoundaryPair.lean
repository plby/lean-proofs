import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

/-!
# The actual boundary of a zero-index surgery gains one disjoint sphere

The old attaching piece is empty and its exterior covers the entire old
boundary. The new piece is the belt sphere itself. The resulting sum
homeomorphism retains both original closed-piece maps.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

open PuncturedHandle

variable {E F R X Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] [Subsingleton E]
  (d : SurgeryBoundaryPair E F R X Y)

theorem zeroIndex_oldExterior_surjective : Surjective d.oldExterior := by
  intro x
  have h : x ∈ range d.oldExterior ∪ range d.oldPiece := d.old_cover ▸ mem_univ x
  rcases h with h | ⟨p, _⟩
  · exact h
  · exact isEmptyElim p.1

def zeroIndexOldExterior : R ≃ₜ X :=
  (Equiv.ofBijective d.oldExterior
    ⟨d.oldExterior_closed.injective,
      d.zeroIndex_oldExterior_surjective⟩).toHomeomorphOfContinuousClosed
      d.oldExterior_closed.continuous d.oldExterior_closed.isClosedMap

def zeroIndexNewCoordinates : (UnitBall E × UnitSphere F) ≃ₜ UnitSphere F where
  toFun := Prod.snd
  invFun := fun v => (ballZero, v)
  left_inv := fun _ => Prod.ext (Subsingleton.elim _ _) rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_snd
  continuous_invFun := continuous_const.prodMk continuous_id

theorem zeroIndex_belt_closed : IsClosedEmbedding d.beltSphere :=
  d.newPiece_closed.comp (zeroIndexNewCoordinates (E := E) (F := F)).symm.isClosedEmbedding

def zeroIndexSumMap : X ⊕ UnitSphere F → Y :=
  Sum.elim (d.newExterior ∘ d.zeroIndexOldExterior.symm) d.beltSphere

theorem zeroIndexSumMap_injective : Injective d.zeroIndexSumMap := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact congrArg Sum.inl (d.zeroIndexOldExterior.symm.injective
            (d.newExterior_closed.injective h))
      | inr y => exact False.elim (d.newExterior_avoids (d.zeroIndexOldExterior.symm x) ⟨y, h.symm⟩)
  | inr x =>
      cases y with
      | inl y => exact False.elim (d.newExterior_avoids (d.zeroIndexOldExterior.symm y) ⟨x, h⟩)
      | inr y => exact congrArg Sum.inr (d.zeroIndex_belt_closed.injective h)

theorem zeroIndexSumMap_surjective : Surjective d.zeroIndexSumMap := by
  intro y
  have h : y ∈ range d.newExterior ∪ range d.newPiece := d.new_cover ▸ mem_univ y
  rcases h with ⟨r, rfl⟩ | ⟨p, rfl⟩
  · refine ⟨Sum.inl (d.oldExterior r), ?_⟩
    change d.newExterior (d.zeroIndexOldExterior.symm (d.zeroIndexOldExterior r)) = _
    rw [Homeomorph.symm_apply_apply]
  · refine ⟨Sum.inr p.2, ?_⟩
    exact congrArg d.newPiece (Prod.ext (Subsingleton.elim _ _) rfl)

theorem zeroIndexSumMap_closed : IsClosedEmbedding d.zeroIndexSumMap :=
  (d.newExterior_closed.comp d.zeroIndexOldExterior.symm.isClosedEmbedding).sumElim
    d.zeroIndex_belt_closed d.zeroIndexSumMap_injective

def zeroIndexBoundaryHomeomorph : (X ⊕ UnitSphere F) ≃ₜ Y :=
  (Equiv.ofBijective d.zeroIndexSumMap
    ⟨d.zeroIndexSumMap_injective, d.zeroIndexSumMap_surjective⟩).toHomeomorphOfContinuousClosed
      d.zeroIndexSumMap_closed.continuous d.zeroIndexSumMap_closed.isClosedMap

theorem zeroIndexBoundaryHomeomorph_old (r : R) :
    d.zeroIndexBoundaryHomeomorph (Sum.inl (d.oldExterior r)) = d.newExterior r := by
  change d.newExterior (d.zeroIndexOldExterior.symm (d.zeroIndexOldExterior r)) = _
  rw [Homeomorph.symm_apply_apply]

theorem zeroIndexBoundaryHomeomorph_belt (v : UnitSphere F) :
    d.zeroIndexBoundaryHomeomorph (Sum.inr v) = d.beltSphere v := rfl

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
