import Wikipedia.HopfProblem.CuspCircleNormalTrivializationStandardBoundaryProduct

/-!
# The actual boundary framing in standard sphere-product coordinates

The literal product of the standard unit two-sphere and unit three-sphere
parametrizes the genuine frontier of the closed normal neighborhood.
This is exactly the restriction of the original standard closed-disk
map. It preserves the original circle action. In the normalized boundary
comparison the positive radius cancels, leaving precisely the explicit
real/imaginary inverse of the standard unit normal vector.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

/-- Standard sphere-product coordinates on the actual topological frontier in the threefold. -/
def standardBoundaryHomeomorph :
    StandardNormalBoundary ≃ₜ frontier closedDiskNeighborhood :=
  standardBoundaryProductHomeomorph.trans closedBoundaryHomeomorph

/-- This boundary homeomorphism is the restriction of the same standard closed-disk map. -/
@[simp] theorem standardBoundaryHomeomorph_coe (p : StandardNormalBoundary) :
    (standardBoundaryHomeomorph p : Threefold.Space) =
      standardClosedDiskMap (standardBoundaryIntoClosedDisk p) := rfl

/-- The unchanged standard closed-disk embedding restricted to the literal unit sphere. -/
def standardBoundaryMap (p : StandardNormalBoundary) : Threefold.Space :=
  standardClosedDiskMap (standardBoundaryIntoClosedDisk p)

@[simp] theorem standardBoundaryMap_eq_closedProductMap (p : StandardNormalBoundary) :
    standardBoundaryMap p =
      closedProductMap (standardClosedProductHomeomorph (standardBoundaryIntoClosedDisk p)) := rfl

theorem standardBoundaryMap_mem_frontier (p : StandardNormalBoundary) :
    standardBoundaryMap p ∈ frontier closedDiskNeighborhood :=
  (standardBoundaryHomeomorph p).property

/-- Its image is the literal ambient frontier, not a separately chosen boundary subset. -/
@[simp] theorem standardBoundaryMap_range :
    range standardBoundaryMap = frontier closedDiskNeighborhood :=
  standardBoundaryHomeomorph.surjective.range_comp
    (Subtype.val : frontier closedDiskNeighborhood → Threefold.Space)
    |>.trans Subtype.range_val

theorem standardBoundaryMap_isClosedEmbedding : IsClosedEmbedding standardBoundaryMap :=
  isClosed_frontier.isClosedEmbedding_subtypeVal.comp standardBoundaryHomeomorph.isClosedEmbedding

/-- The standard two-block real rotation gives exactly the unchanged frontier action. -/
theorem standardBoundaryHomeomorph_circleAction (t : Circle) (p : StandardNormalBoundary) :
    standardBoundaryHomeomorph (standardBoundaryCircleAction t p) =
      closedBoundaryCircleAction t (standardBoundaryHomeomorph p) := by
  change closedBoundaryHomeomorph
    (standardBoundaryProductHomeomorph (standardBoundaryCircleAction t p)) = _
  rw [standardBoundaryProductHomeomorph_circleAction]
  exact (closedBoundaryHomeomorph_circleAction t (standardBoundaryProductHomeomorph p)).symm

theorem standardBoundaryHomeomorph_symm_circleAction (t : Circle)
    (x : frontier closedDiskNeighborhood) :
    standardBoundaryHomeomorph.symm (closedBoundaryCircleAction t x) =
      standardBoundaryCircleAction t (standardBoundaryHomeomorph.symm x) := by
  apply standardBoundaryHomeomorph.injective
  simpa only [Homeomorph.apply_symm_apply] using
    (standardBoundaryHomeomorph_circleAction t (standardBoundaryHomeomorph.symm x)).symm

/-- The action on the actual image is the original global threefold action. -/
theorem standardBoundaryMap_circleAction (t : Circle) (p : StandardNormalBoundary) :
    DeltaSweep.actionMap (t, standardBoundaryMap p) =
      standardBoundaryMap (standardBoundaryCircleAction t p) := by
  have h := congrArg (fun x : frontier closedDiskNeighborhood => (x : Threefold.Space))
    (standardBoundaryHomeomorph_circleAction t p)
  exact h.symm

/-- The original normalized boundary comparison in literal standard product coordinates. -/
def standardBoundaryNormalizedHomeomorph :
    StandardNormalBoundary ≃ₜ ConifoldStandardBoundary.SmoothingBoundary 2 :=
  standardBoundaryHomeomorph.trans closedBoundaryNormalizedHomeomorph

/-- The actual inverse normal coordinates of a parametrized frontier point. -/
theorem closedBoundaryHomeomorph_symm_standardBoundaryHomeomorph
    (p : StandardNormalBoundary) :
    closedBoundaryHomeomorph.symm (standardBoundaryHomeomorph p) =
      standardBoundaryProductHomeomorph p :=
  closedBoundaryHomeomorph.symm_apply_apply _

/-- The radius cancels: the marking retains precisely the original unit normal coordinate. -/
@[simp] theorem standardBoundaryNormalizedHomeomorph_apply_val (p : StandardNormalBoundary) :
    (standardBoundaryNormalizedHomeomorph p).val =
      ConifoldStandardBoundary.forward 2 ((2 : ℂ) • Conifold.productMap
        (RealSphere.sphereDiffeomorph.symm p.1,
          RealFour.coordinateEquiv.symm (p.2 : RealFour.Space))) := by
  change (closedBoundaryNormalizedHomeomorph (standardBoundaryHomeomorph p)).val = _
  rw [closedBoundaryNormalizedHomeomorph_unitDirection,
    closedBoundaryHomeomorph_symm_standardBoundaryHomeomorph,
    standardBoundaryProductHomeomorph_unitDirection]
  rfl

/-- The standard sphere-product marking intertwines the literal smoothing circle action. -/
theorem standardBoundaryNormalizedHomeomorph_circleAction (t : Circle)
    (p : StandardNormalBoundary) :
    standardBoundaryNormalizedHomeomorph (standardBoundaryCircleAction t p) =
      ConifoldStandardBoundary.smoothingCircle (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t)
        (standardBoundaryNormalizedHomeomorph p) := by
  change closedBoundaryNormalizedHomeomorph
    (standardBoundaryHomeomorph (standardBoundaryCircleAction t p)) = _
  rw [standardBoundaryHomeomorph_circleAction]
  exact closedBoundaryNormalizedHomeomorph_circleAction t (standardBoundaryHomeomorph p)

theorem standardBoundaryNormalizedHomeomorph_symm_circleAction (t : Circle)
    (M : ConifoldStandardBoundary.SmoothingBoundary 2) :
    standardBoundaryNormalizedHomeomorph.symm
        (ConifoldStandardBoundary.smoothingCircle (DeltaSweep.circleParameter t : ℂ)
          (FixedCoordinates.CircleOrbit.circleParameter_norm t) M) =
      standardBoundaryCircleAction t (standardBoundaryNormalizedHomeomorph.symm M) := by
  apply standardBoundaryNormalizedHomeomorph.injective
  simpa only [Homeomorph.apply_symm_apply] using
    (standardBoundaryNormalizedHomeomorph_circleAction t
      (standardBoundaryNormalizedHomeomorph.symm M)).symm

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
