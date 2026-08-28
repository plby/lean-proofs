import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyCharts

/-!
# The actual three-piece intersection of the regular-family cover

The intersection of the upper and lower family opens is partitioned into
the three existing overlap opens, ordered as middle, left, right. Each
partition member is homeomorphic to its original overlap by removing a
nested subtype. The maps to the two cover members commute literally with
these homeomorphisms and the original overlap inclusions.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SpecialPeriods.Triangle

variable (D : Data ℂ TriangleRegularPoint)

/-- The literal intersection of the two opens in the actual regular family. -/
def familyIntersection : TopologicalSpace.Opens D.Space := upperFamily D ⊓ lowerFamily D

@[simp] theorem mem_familyIntersection (x : D.Space) :
    x ∈ familyIntersection D ↔ x ∈ upperFamily D ∧ x ∈ lowerFamily D := Iff.rfl

/-- Reorder the overlap strips as middle, left, right. -/
def intersectionIndex : Fin 3 → Fin 3 := Equiv.swap 0 1

@[simp] theorem intersectionIndex_zero : intersectionIndex 0 = 1 := by decide

@[simp] theorem intersectionIndex_one : intersectionIndex 1 = 0 := by decide

@[simp] theorem intersectionIndex_two : intersectionIndex 2 = 2 := by decide

theorem intersectionIndex_injective : Function.Injective intersectionIndex :=
  (Equiv.swap (0 : Fin 3) 1).injective

theorem intersectionIndex_surjective : Function.Surjective intersectionIndex :=
  (Equiv.swap (0 : Fin 3) 1).surjective

/-- The actual preimage of an overlap open inside the family intersection. -/
def intersectionPiece (i : Fin 3) : TopologicalSpace.Opens (familyIntersection D) :=
  ⟨Subtype.val ⁻¹' (overlapFamily D (intersectionIndex i) : Set D.Space),
    (overlapFamily D (intersectionIndex i)).isOpen.preimage continuous_subtype_val⟩

@[simp] theorem mem_intersectionPiece (i : Fin 3) (x : familyIntersection D) :
    x ∈ intersectionPiece D i ↔ x.val ∈ overlapFamily D (intersectionIndex i) := Iff.rfl

/-- The three open pieces of the actual intersection are pairwise disjoint. -/
theorem intersectionPiece_pairwise_disjoint :
    Pairwise fun i j : Fin 3 => Disjoint
      (intersectionPiece D i : Set (familyIntersection D)) (intersectionPiece D j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  exact Set.disjoint_left.mp
    (overlapFamily_pairwise_disjoint D (fun h => hij (intersectionIndex_injective h))) hi hj

/-- These three actual open pieces cover the entire family intersection. -/
theorem intersectionPiece_iUnion :
    (⋃ i : Fin 3, (intersectionPiece D i : Set (familyIntersection D))) = univ := by
  apply eq_univ_of_forall
  intro x
  have hx : x.val ∈ ⋃ j : Fin 3, (overlapFamily D j : Set D.Space) := by
    rw [overlapFamily_iUnion]
    exact x.property
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  obtain ⟨i, hi⟩ := intersectionIndex_surjective j
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  change x.val ∈ overlapFamily D (intersectionIndex i)
  rw [hi]
  exact hj

/-- Removing the nested subtype identifies a partition piece with its original overlap. -/
def intersectionPieceHomeomorph (i : Fin 3) :
    intersectionPiece D i ≃ₜ overlapFamily D (intersectionIndex i) where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, overlapFamily_subset D (intersectionIndex i) x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem intersectionPieceHomeomorph_apply_coe (i : Fin 3)
    (x : intersectionPiece D i) :
    (intersectionPieceHomeomorph D i x : D.Space) = x.val.val := rfl

@[simp] theorem intersectionPieceHomeomorph_symm_apply_coe (i : Fin 3)
    (x : overlapFamily D (intersectionIndex i)) :
    (((intersectionPieceHomeomorph D i).symm x).val : D.Space) = x.val := rfl

/-- The literal inclusion from the actual intersection into the upper family open. -/
def intersectionToUpper : C(familyIntersection D, upperFamily D) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, by fun_prop⟩

/-- The literal inclusion from the actual intersection into the lower family open. -/
def intersectionToLower : C(familyIntersection D, lowerFamily D) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, by fun_prop⟩

@[simp] theorem intersectionToUpper_apply_coe (x : familyIntersection D) :
    (intersectionToUpper D x : D.Space) = x.val := rfl

@[simp] theorem intersectionToLower_apply_coe (x : familyIntersection D) :
    (intersectionToLower D x : D.Space) = x.val := rfl

/-- The upper inclusion on a partition piece is the original overlap inclusion. -/
theorem intersectionToUpper_comp_piece (i : Fin 3) :
    (intersectionToUpper D).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(intersectionPiece D i, familyIntersection D)) =
      (overlapFamilyToUpper D (intersectionIndex i)).comp
        (intersectionPieceHomeomorph D i : C(_, _)) := rfl

/-- The lower inclusion on a partition piece is the original overlap inclusion. -/
theorem intersectionToLower_comp_piece (i : Fin 3) :
    (intersectionToLower D).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(intersectionPiece D i, familyIntersection D)) =
      (overlapFamilyToLower D (intersectionIndex i)).comp
        (intersectionPieceHomeomorph D i : C(_, _)) := rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
