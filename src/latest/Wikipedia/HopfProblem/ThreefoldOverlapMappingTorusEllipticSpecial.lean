import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusElliptic
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusGlobal
import Wikipedia.HopfProblem.EllipticEquivariantCentralTopology
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFilling

/-!
# The actual special-period elliptic overlaps are affine mapping tori

The selected native small fillings have precisely the real quotient
topologies used by the preceding construction.  This gives an
unconditional homotopy equivalence for each literal punctured original
piece, with the genuine affine boundary inclusion and its base formula.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic

open SpecialPeriods SpecialPeriods.Threefold SpecialPeriods.EllipticFilling
open Wikipedia.HopfProblem.Elliptic

/-- The exact noncentral condition in the actual special small piece. -/
theorem specialPiece_regular_iff (j : Kind) (x : SpecialEllipticPiece j) :
    localProjectionToBase (some (some j)) x ∈ regularPatch ↔
      (specialFullFillingProjection j x.val : ℂ) ≠ 0 :=
  pieceProjectionToBase_mem_regular_iff specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j x

/-- The original punctured small piece has its native real affine quotient topology. -/
def specialPuncturedHomeomorph (j : Kind) :
    PuncturedPiece (some j) ≃ₜ
      PuncturedFilling j j.twist (mainTwist_admissible j) (specialBaseCover.radius (some j)) where
  toFun x := ⟨(specialLocalData j).fillingHomeomorph j.twist (mainTwist_admissible j)
      ((x.val : SpecialEllipticPiece j).val),
    (specialPiece_regular_iff j x.val).mp x.property,
    (x.val : SpecialEllipticPiece j).property⟩
  invFun y := ⟨(⟨((specialLocalData j).fillingHomeomorph j.twist
      (mainTwist_admissible j)).symm y.val, y.property.2⟩ : SpecialEllipticPiece j),
    (specialPiece_regular_iff j _).mpr y.property.1⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((specialLocalData j).fillingHomeomorph j.twist
      (mainTwist_admissible j)).symm_apply_apply _
  right_inv y := by
    apply Subtype.ext
    exact ((specialLocalData j).fillingHomeomorph j.twist
      (mainTwist_admissible j)).apply_symm_apply _
  continuous_toFun := (((specialLocalData j).fillingHomeomorph j.twist
    (mainTwist_admissible j)).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun := ((((specialLocalData j).fillingHomeomorph j.twist
    (mainTwist_admissible j)).symm.continuous.comp
      continuous_subtype_val).subtype_mk _).subtype_mk _

/-- A proved positive root radius inside the actual selected base patch. -/
def specialRootRadius (j : Kind) : Radius j.order (specialBaseCover.radius (some j)) :=
  Classical.choice (radius_nonempty j.order j.order_pos (specialBaseCover.radius (some j))
    (specialBaseCover.radius_pos (some j)))

/-- The actual boundary mapping torus of the original rank-four affine action. -/
abbrev SpecialBoundary (j : Kind) := Boundary j j.twist

/-- Both genuine punctured small elliptic pieces have the stated boundary type. -/
def specialMappingTorusHomotopyEquiv (j : Kind) :
    PuncturedPiece (some j) ≃ₕ SpecialBoundary j :=
  (specialPuncturedHomeomorph j).toHomotopyEquiv.trans
    (puncturedMappingTorusHomotopyEquiv j j.twist (mainTwist_admissible j)
      (specialBaseCover.radius (some j)) (specialRootRadius j))

/-- The concrete inverse includes the boundary in the original punctured piece. -/
def specialBoundaryInclusion (j : Kind) : C(SpecialBoundary j, PuncturedPiece (some j)) :=
  ⟨(specialMappingTorusHomotopyEquiv j).symm, (specialMappingTorusHomotopyEquiv j).symm.continuous⟩

/-- The same map with its original, unpunctured small-filling codomain. -/
def specialBoundaryToPiece (j : Kind) : C(SpecialBoundary j, SpecialEllipticPiece j) :=
  (puncturedPieceInclusion (some j)).comp (specialBoundaryInclusion j)

/-- Every boundary point is the original varying-period family quotient. -/
theorem specialBoundaryInclusion_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    ((specialBoundaryInclusion j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x))).val :
      SpecialEllipticPiece j).val =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (root j.order (specialBaseCover.radius (some j)) (specialRootRadius j)
          ((t / j.order : ℝ) : Circle), x) := by
  change (((specialPuncturedHomeomorph j).symm
    (boundaryInclusion j j.twist (mainTwist_admissible j)
      (specialBaseCover.radius (some j)) (specialRootRadius j)
      (MappingTorus.mk _ (t, x)))).val : SpecialEllipticPiece j).val = _
  rw [boundaryInclusion_mk]
  rfl

/-- The actual boundary cylinder, with values in the original small piece. -/
def specialBoundaryCylinder (j : Kind) : C(ℝ × RealTorus₄, SpecialEllipticPiece j) :=
  (specialBoundaryToPiece j).comp
    ⟨MappingTorus.mk (flatTorusAffine j j.twist), MappingTorus.mk_continuous _⟩

theorem specialBoundaryCylinder_endpoint (j : Kind) (t : ℝ) (x : RealTorus₄) :
    specialBoundaryCylinder j (t + 1, x) =
      specialBoundaryCylinder j (t, flatTorusAffine j j.twist x) :=
  congrArg (specialBoundaryToPiece j) (MappingTorus.mk_add_one _ t x)

/-- The exact power coordinate of the actual native boundary cylinder. -/
theorem specialBoundaryCylinder_parameter (j : Kind) (t : ℝ) (x : RealTorus₄) :
    (specialFullFillingProjection j (specialBoundaryCylinder j (t, x)).val : ℂ) =
      (((specialRootRadius j : ℝ) : ℂ) ^ j.order) * CuspUniformization.exponential (t : ℂ) :=
  boundaryCylinder_base j j.twist (mainTwist_admissible j)
    (specialBaseCover.radius (some j)) (specialRootRadius j) t x

/-- The original compact-base point is the genuine inverse elliptic quotient chart. -/
theorem specialBoundaryCylinder_base (j : Kind) (t : ℝ) (x : RealTorus₄) :
    specialEllipticPieceProjectionToBase j (specialBoundaryCylinder j (t, x)) =
      (punctureChart (some j)).symm
        ((((specialRootRadius j : ℝ) : ℂ) ^ j.order) * CuspUniformization.exponential (t : ℂ)) := by
  change (punctureChart (some j)).symm
    (specialFullFillingProjection j (specialBoundaryCylinder j (t, x)).val : ℂ) = _
  rw [specialBoundaryCylinder_parameter]

/-- The literal fibre of the boundary maps into the original piece. -/
def specialFibreToPiece (j : Kind) : C(RealTorus₄, SpecialEllipticPiece j) :=
  (specialBoundaryToPiece j).comp
    (MappingTorus.HomologyCover.fibreInclusion (flatTorusAffine j j.twist))

theorem specialFibreToPiece_val (j : Kind) (x : RealTorus₄) :
    (specialFibreToPiece j x).val =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (root j.order (specialBaseCover.radius (some j)) (specialRootRadius j) 0, x) := by
  have h := specialBoundaryInclusion_mk j 0 x
  change ((specialBoundaryInclusion j
    (MappingTorus.mk (flatTorusAffine j j.twist) (0, x))).val : SpecialEllipticPiece j).val = _
  simpa only [zero_div, AddCircle.coe_zero] using h

end Wikipedia.HopfProblem.ThreefoldOverlapMappingTorus.Elliptic
