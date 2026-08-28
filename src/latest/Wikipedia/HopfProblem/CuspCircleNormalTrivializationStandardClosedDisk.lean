import Wikipedia.HopfProblem.CuspCircleNormalTrivializationClosedDisk
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealFour
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealSphere
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRadial

/-!
# The literal standard sphere times closed four-disk in the original threefold

The base identification is the genuine native real-analytic Riemann-sphere
diffeomorphism. The normal identification is the explicit real/imaginary
coordinate map followed by positive radial scaling. Thus the actual compact
normal neighborhood has the standard `S² × D⁴` product model, with the
original curve retained as its zero section.
-/

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

open SpecialPeriods SpecialPeriods.Threefold

/-- The standard closed unit disk in Euclidean real four-space. -/
abbrev UnitClosedFourDisk := closedBall (0 : RealFour.Space) 1

/-- The literal standard two-sphere times the standard closed four-disk. -/
abbrev StandardClosedNormalProduct := RealSphere.UnitTwoSphere × UnitClosedFourDisk

/-- Standard coordinates on the actual compact normal product. -/
def standardClosedProductHomeomorph : StandardClosedNormalProduct ≃ₜ ClosedNormalProduct :=
  RealSphere.sphereDiffeomorph.symm.toHomeomorph.prodCongr
    ((Radial.closedBallHomeomorph (E := RealFour.Space) closedRadius closedRadius_pos).trans
      (RealFour.closedBallHomeomorph closedRadius closedRadius_pos.le).symm)

@[simp] theorem standardClosedProductHomeomorph_fst (p : StandardClosedNormalProduct) :
    (standardClosedProductHomeomorph p).1 = RealSphere.sphereDiffeomorph.symm p.1 := rfl

@[simp] theorem standardClosedProductHomeomorph_snd_coe (p : StandardClosedNormalProduct) :
    ((standardClosedProductHomeomorph p).2 : Fibre) =
      RealFour.coordinateEquiv.symm (closedRadius • (p.2 : RealFour.Space)) := rfl

/-- The genuine compact neighborhood is homeomorphic to the literal standard product. -/
def standardClosedDiskNeighborhoodHomeomorph :
    StandardClosedNormalProduct ≃ₜ closedDiskNeighborhood :=
  standardClosedProductHomeomorph.trans closedDiskNeighborhoodHomeomorph

@[simp] theorem standardClosedDiskNeighborhoodHomeomorph_coe (p : StandardClosedNormalProduct) :
    (standardClosedDiskNeighborhoodHomeomorph p : Threefold.Space) =
      closedProductMap (standardClosedProductHomeomorph p) := rfl

/-- The original embedding written on the standard sphere and closed unit disk. -/
def standardClosedDiskMap (p : StandardClosedNormalProduct) : Threefold.Space :=
  standardClosedDiskNeighborhoodHomeomorph p

theorem standardClosedDiskMap_isClosedEmbedding : IsClosedEmbedding standardClosedDiskMap :=
  closedProductMap_isClosedEmbedding.comp standardClosedProductHomeomorph.isClosedEmbedding

@[simp] theorem standardClosedDiskMap_range :
    range standardClosedDiskMap = closedDiskNeighborhood :=
  standardClosedDiskNeighborhoodHomeomorph.surjective.range_comp
    (Subtype.val : closedDiskNeighborhood → Threefold.Space) |>.trans Subtype.range_val

/-- The zero vector of the literal standard closed unit disk. -/
def standardClosedZero : UnitClosedFourDisk := ⟨0, by simp⟩

theorem standardClosedProductHomeomorph_zeroSection (p : RealSphere.UnitTwoSphere) :
    standardClosedProductHomeomorph (p, standardClosedZero) =
      (RealSphere.sphereDiffeomorph.symm p, closedZero) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change RealFour.coordinateEquiv.symm (closedRadius • (0 : RealFour.Space)) = (0 : Fibre)
    rw [smul_zero]
    exact RealFour.coordinateEquiv.symm.map_zero

/-- The standard-product zero section maps to the exact preexisting fixed curve. -/
theorem standardClosedDiskMap_zeroSection (p : RealSphere.UnitTwoSphere) :
    standardClosedDiskMap (p, standardClosedZero) =
      CuspGeometry.doubleCurveParametrization 1 (RealSphere.sphereDiffeomorph.symm p) := by
  change closedProductMap (standardClosedProductHomeomorph (p, standardClosedZero)) = _
  rw [standardClosedProductHomeomorph_zeroSection, closedProductMap_zeroSection]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
