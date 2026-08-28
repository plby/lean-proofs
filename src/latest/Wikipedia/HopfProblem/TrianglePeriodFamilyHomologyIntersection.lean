import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyIntersectionTopology
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyPieces
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyPartition

/-!
# Actual homology of the three-component family intersection

The components are ordered middle, left, right. The partition equivalence
and the actual torus markings give the intersection homology in every
degree. The upper inclusion is the sum of these coordinates; the lower
inclusion applies the two actual deck actions on the left and right.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

variable (D : Data ℂ TriangleRegularPoint) (b : SlitBaseLift)

/-- Remove the nested component subtype and use its actual upper-chart torus marking. -/
def intersectionPieceHomologyEquiv (i : Fin 3) (n : ℕ) :
    SingularHomology (intersectionPiece D i) n ≃ₗ[ℤ] SingularHomology RealTorus₄ n :=
  (homeomorphHomologyEquiv (intersectionPieceHomeomorph D i) n).trans
    (overlapHomologyEquiv D b (intersectionIndex i) n)

@[simp] theorem intersectionPieceHomologyEquiv_apply (i : Fin 3) (n : ℕ)
    (a : SingularHomology (intersectionPiece D i) n) :
    intersectionPieceHomologyEquiv D b i n a =
      overlapHomologyEquiv D b (intersectionIndex i) n
        (singularHomologyMap (intersectionPieceHomeomorph D i) n a) := rfl

/-- Actual homology of the disjoint internal open partition, before fibre marking. -/
abbrev intersectionPartitionHomologyEquiv (n : ℕ) :
    SingularHomology (familyIntersection D) n ≃ₗ[ℤ]
      (SingularHomology (intersectionPiece D 0) n ×
        (SingularHomology (intersectionPiece D 1) n ×
          SingularHomology (intersectionPiece D 2) n)) :=
  openPartitionHomologyEquiv (intersectionPiece D)
    (intersectionPiece_pairwise_disjoint D) (intersectionPiece_iUnion D) n

/-- Actual intersection homology, ordered middle, left, right and marked in the torus. -/
def intersectionHomologyEquiv (n : ℕ) :
    SingularHomology (familyIntersection D) n ≃ₗ[ℤ]
      (SingularHomology RealTorus₄ n ×
        (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n)) :=
  (intersectionPartitionHomologyEquiv D n).trans
    (((intersectionPieceHomologyEquiv D b 0 n).toAddEquiv.prodCongr
      ((intersectionPieceHomologyEquiv D b 1 n).toAddEquiv.prodCongr
        (intersectionPieceHomologyEquiv D b 2 n).toAddEquiv)).toIntLinearEquiv)

@[simp] theorem intersectionHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (familyIntersection D) n) :
    intersectionHomologyEquiv D b n a =
      (intersectionPieceHomologyEquiv D b 0 n (intersectionPartitionHomologyEquiv D n a).1,
        (intersectionPieceHomologyEquiv D b 1 n (intersectionPartitionHomologyEquiv D n a).2.1,
          intersectionPieceHomologyEquiv D b 2 n
            (intersectionPartitionHomologyEquiv D n a).2.2)) := rfl

/-- The inverse marking is the sum of the three actual component inclusions. -/
theorem intersectionHomologyEquiv_symm_apply (n : ℕ)
    (a : SingularHomology RealTorus₄ n ×
      (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n)) :
    (intersectionHomologyEquiv D b n).symm a =
      singularHomologyMap (openPartitionInclusion (intersectionPiece D) 0) n
          ((intersectionPieceHomologyEquiv D b 0 n).symm a.1) +
        (singularHomologyMap (openPartitionInclusion (intersectionPiece D) 1) n
            ((intersectionPieceHomologyEquiv D b 1 n).symm a.2.1) +
          singularHomologyMap (openPartitionInclusion (intersectionPiece D) 2) n
            ((intersectionPieceHomologyEquiv D b 2 n).symm a.2.2)) :=
  openPartitionHomologyEquiv_symm_apply (intersectionPiece D)
    (intersectionPiece_pairwise_disjoint D) (intersectionPiece_iUnion D) n
    ((intersectionPieceHomologyEquiv D b 0 n).symm a.1,
      ((intersectionPieceHomologyEquiv D b 1 n).symm a.2.1,
        (intersectionPieceHomologyEquiv D b 2 n).symm a.2.2))

@[simp] theorem intersectionHomologyEquiv_inclusion_middle (n : ℕ)
    (a : SingularHomology (intersectionPiece D 0) n) :
    intersectionHomologyEquiv D b n
        (singularHomologyMap (openPartitionInclusion (intersectionPiece D) 0) n a) =
      (intersectionPieceHomologyEquiv D b 0 n a, (0, 0)) := by
  simp only [intersectionHomologyEquiv_apply, intersectionPartitionHomologyEquiv,
    openPartitionHomologyEquiv_inclusion_zero, map_zero]

@[simp] theorem intersectionHomologyEquiv_inclusion_left (n : ℕ)
    (a : SingularHomology (intersectionPiece D 1) n) :
    intersectionHomologyEquiv D b n
        (singularHomologyMap (openPartitionInclusion (intersectionPiece D) 1) n a) =
      (0, (intersectionPieceHomologyEquiv D b 1 n a, 0)) := by
  simp only [intersectionHomologyEquiv_apply, intersectionPartitionHomologyEquiv,
    openPartitionHomologyEquiv_inclusion_one, map_zero]

@[simp] theorem intersectionHomologyEquiv_inclusion_right (n : ℕ)
    (a : SingularHomology (intersectionPiece D 2) n) :
    intersectionHomologyEquiv D b n
        (singularHomologyMap (openPartitionInclusion (intersectionPiece D) 2) n a) =
      (0, (0, intersectionPieceHomologyEquiv D b 2 n a)) := by
  simp only [intersectionHomologyEquiv_apply, intersectionPartitionHomologyEquiv,
    openPartitionHomologyEquiv_inclusion_two, map_zero]

/-- Every component enters the upper member by its unchanged torus marking. -/
theorem upperHomologyEquiv_intersectionPiece (i : Fin 3) (n : ℕ)
    (a : SingularHomology (intersectionPiece D i) n) :
    upperHomologyEquiv D b n
        (singularHomologyMap
          ((intersectionToUpper D).comp (openPartitionInclusion (intersectionPiece D) i)) n a) =
      intersectionPieceHomologyEquiv D b i n a := by
  rw [openPartitionInclusion, intersectionToUpper_comp_piece, singularHomologyMap_comp]
  exact upperHomologyEquiv_overlap D b (intersectionIndex i) n _

/-- Each lower component inclusion has its actual constant deck action. -/
theorem lowerHomologyEquiv_intersectionPiece (i : Fin 3) (n : ℕ)
    (a : SingularHomology (intersectionPiece D i) n) :
    lowerHomologyEquiv D b n
        (singularHomologyMap
          ((intersectionToLower D).comp (openPartitionInclusion (intersectionPiece D) i)) n a) =
      singularHomologyMap
        (triangleTorusHomeomorph (overlapTransition b (intersectionIndex i)) :
          C(RealTorus₄, RealTorus₄)) n (intersectionPieceHomologyEquiv D b i n a) := by
  rw [openPartitionInclusion, intersectionToLower_comp_piece, singularHomologyMap_comp]
  exact lowerHomologyEquiv_overlap D b (intersectionIndex i) n _

/-- The actual upper intersection inclusion is the sum of the three marked coordinates. -/
theorem upperHomologyEquiv_intersection (n : ℕ)
    (a : SingularHomology (familyIntersection D) n) :
    upperHomologyEquiv D b n (singularHomologyMap (intersectionToUpper D) n a) =
      (intersectionHomologyEquiv D b n a).1 +
        (intersectionHomologyEquiv D b n a).2.1 +
          (intersectionHomologyEquiv D b n a).2.2 := by
  have h := congrArg (upperHomologyEquiv D b n)
    (openPartitionHomologyEquiv_map_out (intersectionPiece D)
      (intersectionPiece_pairwise_disjoint D) (intersectionPiece_iUnion D)
      (intersectionToUpper D) n a)
  simp only [map_add, upperHomologyEquiv_intersectionPiece] at h
  simpa only [intersectionHomologyEquiv_apply, ← add_assoc] using h

/-- The middle component has identity transition; the other two retain their actual deck maps. -/
theorem lowerHomologyEquiv_intersection (n : ℕ)
    (a : SingularHomology (familyIntersection D) n) :
    lowerHomologyEquiv D b n (singularHomologyMap (intersectionToLower D) n a) =
      (intersectionHomologyEquiv D b n a).1 +
        singularHomologyMap
          (triangleTorusHomeomorph (overlapTransition b 0) : C(RealTorus₄, RealTorus₄)) n
          (intersectionHomologyEquiv D b n a).2.1 +
        singularHomologyMap
          (triangleTorusHomeomorph (overlapTransition b 2) : C(RealTorus₄, RealTorus₄)) n
          (intersectionHomologyEquiv D b n a).2.2 := by
  have hidentity :
      singularHomologyMap (Homeomorph.refl RealTorus₄ : C(RealTorus₄, RealTorus₄)) n =
        LinearMap.id := by
    change singularHomologyMap (ContinuousMap.id RealTorus₄) n = _
    exact singularHomologyMap_id RealTorus₄ n
  have h := congrArg (lowerHomologyEquiv D b n)
    (openPartitionHomologyEquiv_map_out (intersectionPiece D)
      (intersectionPiece_pairwise_disjoint D) (intersectionPiece_iUnion D)
      (intersectionToLower D) n a)
  simp only [map_add, lowerHomologyEquiv_intersectionPiece,
    intersectionIndex_zero, intersectionIndex_one, intersectionIndex_two,
    overlapTransition_middle, triangleTorusHomeomorph_one,
    hidentity, LinearMap.id_apply] at h
  simpa only [intersectionHomologyEquiv_apply, ← add_assoc] using h

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
