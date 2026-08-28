import Wikipedia.HopfProblem.CuspCircleNormalTrivializationBoundaryFrontier
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationBoundaryComparison

/-!
# The actual closed-neighborhood frontier and its boundary comparisons

The source below is the literal topological frontier of the compact
normal disk image in the original threefold. Its comparisons with the
native toric level, conifold matrix level, and normalized smoothing
level preserve the actual original circle action. In the normalized
formula the unit normal direction is the original normal vector divided
by the proved positive closed radius. No assertion about the global
complement or a global gluing classification is used here.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold
open SpecialPeriods.Threefold.VerticalAction SpecialPeriods.Threefold.Homology

local notation "Circle" => AddCircle (1 : ℝ)

/-- The proved equality between the actual frontier and the actual radius image. -/
def closedBoundaryImageHomeomorph :
    frontier closedDiskNeighborhood ≃ₜ
      boundaryImage closedRadius closedRadius_pos closedRadius_lt_injectiveRadius :=
  Homeomorph.setCongr frontier_closedDiskNeighborhood

@[simp] theorem closedBoundaryImageHomeomorph_coe (x : frontier closedDiskNeighborhood) :
    (closedBoundaryImageHomeomorph x : Threefold.Space) = x := rfl

theorem closedBoundaryImageHomeomorph_circleAction (t : Circle)
    (x : frontier closedDiskNeighborhood) :
    closedBoundaryImageHomeomorph (closedBoundaryCircleAction t x) =
      boundaryImageCircleAction closedRadius closedRadius_pos closedRadius_lt_injectiveRadius
        t (closedBoundaryImageHomeomorph x) := rfl

/-- The genuine frontier is homeomorphic to the native toric radius level. -/
def closedBoundaryToricHomeomorph :
    frontier closedDiskNeighborhood ≃ₜ Conifold.ToricBoundary closedRadius :=
  closedBoundaryImageHomeomorph.trans
    (boundaryToricHomeomorph closedRadius closedRadius_pos closedRadius_lt_injectiveRadius)

@[simp] theorem closedBoundaryToricHomeomorph_apply_val
    (x : frontier closedDiskNeighborhood) :
    (closedBoundaryToricHomeomorph x).val =
      toricNeighborhoodDiffeomorph (closedBoundaryHomeomorph.symm x).val := rfl

@[simp] theorem closedBoundaryToricHomeomorph_symm_coe (y : Conifold.ToricBoundary closedRadius) :
    (closedBoundaryToricHomeomorph.symm y : Threefold.Space) =
      boundaryMap closedRadius closedRadius_pos closedRadius_lt_injectiveRadius
        ((Conifold.productToricBoundaryHomeomorph closedRadius).symm y) := rfl

theorem closedBoundaryToricHomeomorph_circleAction (t : Circle)
    (x : frontier closedDiskNeighborhood) :
    closedBoundaryToricHomeomorph (closedBoundaryCircleAction t x) =
      Conifold.toricBoundaryCircle (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t)
        (closedBoundaryToricHomeomorph x) := by
  change boundaryToricHomeomorph _ _ _
    (closedBoundaryImageHomeomorph (closedBoundaryCircleAction t x)) = _
  rw [closedBoundaryImageHomeomorph_circleAction]
  exact boundaryToricHomeomorph_circleAction _ _ _ t _

/-- The genuine frontier is homeomorphic to the original conifold matrix radius level. -/
def closedBoundaryConifoldHomeomorph :
    frontier closedDiskNeighborhood ≃ₜ ConifoldStandardBoundary.ConifoldBoundary closedRadius :=
  closedBoundaryImageHomeomorph.trans
    (boundaryConifoldHomeomorph closedRadius closedRadius_pos closedRadius_lt_injectiveRadius)

@[simp] theorem closedBoundaryConifoldHomeomorph_apply_val
    (x : frontier closedDiskNeighborhood) :
    (closedBoundaryConifoldHomeomorph x).val =
      Conifold.productMap (closedBoundaryHomeomorph.symm x).val := rfl

@[simp] theorem closedBoundaryConifoldHomeomorph_symm_coe
    (M : ConifoldStandardBoundary.ConifoldBoundary closedRadius) :
    (closedBoundaryConifoldHomeomorph.symm M : Threefold.Space) =
      boundaryMap closedRadius closedRadius_pos closedRadius_lt_injectiveRadius
        ((Conifold.productBoundaryHomeomorph (ne_of_gt closedRadius_pos)).symm M) := rfl

theorem closedBoundaryConifoldHomeomorph_circleAction (t : Circle)
    (x : frontier closedDiskNeighborhood) :
    closedBoundaryConifoldHomeomorph (closedBoundaryCircleAction t x) =
      ConifoldStandardBoundary.conifoldCircle (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t)
        (closedBoundaryConifoldHomeomorph x) := by
  change boundaryConifoldHomeomorph _ _ _
    (closedBoundaryImageHomeomorph (closedBoundaryCircleAction t x)) = _
  rw [closedBoundaryImageHomeomorph_circleAction]
  exact boundaryConifoldHomeomorph_circleAction _ _ _ t _

/-- The actual frontier has the explicitly normalized smoothing-boundary model. -/
def closedBoundaryNormalizedHomeomorph :
    frontier closedDiskNeighborhood ≃ₜ ConifoldStandardBoundary.SmoothingBoundary 2 :=
  closedBoundaryImageHomeomorph.trans
    (boundaryNormalizedHomeomorph closedRadius closedRadius_pos closedRadius_lt_injectiveRadius)

@[simp] theorem closedBoundaryNormalizedHomeomorph_apply_val
    (x : frontier closedDiskNeighborhood) :
    (closedBoundaryNormalizedHomeomorph x).val =
      ConifoldStandardBoundary.forward 2
        (ConifoldStandardBoundary.rescaleMatrix closedRadius 2
          (Conifold.productMap (closedBoundaryHomeomorph.symm x).val)) := rfl

/-- The final boundary comparison explicitly retains the actual normal direction `F/r`. -/
theorem closedBoundaryNormalizedHomeomorph_unitDirection
    (x : frontier closedDiskNeighborhood) :
    (closedBoundaryNormalizedHomeomorph x).val =
      ConifoldStandardBoundary.forward 2 ((2 : ℂ) • Conifold.productMap
        ((closedBoundaryHomeomorph.symm x).val.1,
          (closedRadius⁻¹ : ℝ) • (closedBoundaryHomeomorph.symm x).val.2)) :=
  boundaryNormalizedHomeomorph_unitDirection _ _ _ (closedBoundaryImageHomeomorph x)

/-- The original circle action becomes the literal smoothing action under the actual comparison. -/
theorem closedBoundaryNormalizedHomeomorph_circleAction (t : Circle)
    (x : frontier closedDiskNeighborhood) :
    closedBoundaryNormalizedHomeomorph (closedBoundaryCircleAction t x) =
      ConifoldStandardBoundary.smoothingCircle (DeltaSweep.circleParameter t : ℂ)
        (FixedCoordinates.CircleOrbit.circleParameter_norm t)
        (closedBoundaryNormalizedHomeomorph x) := by
  change boundaryNormalizedHomeomorph _ _ _
    (closedBoundaryImageHomeomorph (closedBoundaryCircleAction t x)) = _
  rw [closedBoundaryImageHomeomorph_circleAction]
  exact boundaryNormalizedHomeomorph_circleAction _ _ _ t _

theorem closedBoundaryNormalizedHomeomorph_symm_circleAction (t : Circle)
    (M : ConifoldStandardBoundary.SmoothingBoundary 2) :
    closedBoundaryNormalizedHomeomorph.symm
        (ConifoldStandardBoundary.smoothingCircle (DeltaSweep.circleParameter t : ℂ)
          (FixedCoordinates.CircleOrbit.circleParameter_norm t) M) =
      closedBoundaryCircleAction t (closedBoundaryNormalizedHomeomorph.symm M) := by
  apply closedBoundaryNormalizedHomeomorph.injective
  simpa only [Homeomorph.apply_symm_apply] using
    (closedBoundaryNormalizedHomeomorph_circleAction t
      (closedBoundaryNormalizedHomeomorph.symm M)).symm

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
