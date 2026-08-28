import Wikipedia.HopfProblem.CuspNegationExponential
import Wikipedia.HopfProblem.CuspNegationBoundary
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusSpaces

/-!
# Negation on the original full special cusp cap and its attaching map

The map acts on the original fixed-radius cap, not a smaller substitute.
The real period equivalence is linear, so its logarithmic-cover formula
gives literal covariance with the native boundary mapping torus.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspNegation

open SpecialPeriods SpecialPeriods.Threefold CuspUniformization
open ThreefoldOverlapMappingTorus

theorem quotientNegation_boundaryCylinder (D : CuspFamily.Data) (h : Cusp.Height D.radius)
    (t : ℝ) (x : RealTorus₄) :
    quotientNegation D.correction D.radius (Cusp.boundaryCylinder D h (t, x)).val =
      (Cusp.boundaryCylinder D h (t, -x)).val := by
  obtain ⟨v, rfl⟩ := standardLattice.mkQ_surjective x
  have hneg : -standardLattice.mkQ v = standardLattice.mkQ (-v) := (map_neg _ _).symm
  rw [hneg, Cusp.boundaryCylinder_realCoordinates, Cusp.boundaryCylinder_realCoordinates,
    quotientNegation_puncturedCuspCover]
  apply congrArg (fun p : LogCover D.radius => (puncturedCuspCover D.correction D.radius p).val)
  apply Subtype.ext
  change ((Cusp.logPoint D.radius D.radius_pos t h : ℂ),
      -D.periods.periodEquiv (Cusp.logPoint D.radius D.radius_pos t h) v) =
    ((Cusp.logPoint D.radius D.radius_pos t h : ℂ),
      D.periods.periodEquiv (Cusp.logPoint D.radius D.radius_pos t h) (-v))
  rw [map_neg]

theorem quotientNegation_boundaryInclusion (D : CuspFamily.Data) (h : Cusp.Height D.radius)
    (x : Cusp.Boundary) :
    quotientNegation D.correction D.radius (Cusp.boundaryInclusion D h x).val =
      (Cusp.boundaryInclusion D h (boundaryNeg x)).val := by
  obtain ⟨⟨t, y⟩, rfl⟩ := MappingTorus.mk_surjective Cusp.monodromy x
  rw [boundaryNeg_mk]
  exact quotientNegation_boundaryCylinder D h t y

/-- The actual involutive homeomorphism of the full original cusp cap. -/
def specialCapHomeomorph : SpecialCuspPiece ≃ₜ SpecialCuspPiece :=
  quotientHomeomorph specialCuspData.correction (specialBaseCover.radius none)

def specialCapMap : C(SpecialCuspPiece, SpecialCuspPiece) :=
  ⟨specialCapHomeomorph, specialCapHomeomorph.continuous⟩

@[simp] theorem specialCapMap_apply (x : SpecialCuspPiece) :
    specialCapMap x = quotientNegation specialCuspData.correction
      (specialBaseCover.radius none) x := rfl

theorem specialCapMap_involutive : Function.Involutive specialCapMap :=
  quotientNegation_involutive specialCuspData.correction (specialBaseCover.radius none)

@[simp] theorem specialCapMap_projection (x : SpecialCuspPiece) :
    specialCuspPieceProjectionToBase (specialCapMap x) = specialCuspPieceProjectionToBase x := by
  change (punctureChart none).symm
      (CuspQuotient.projection specialCuspData.correction (specialBaseCover.radius none)
        (quotientNegation specialCuspData.correction (specialBaseCover.radius none) x)) =
    (punctureChart none).symm
      (CuspQuotient.projection specialCuspData.correction (specialBaseCover.radius none) x)
  rw [projection_quotientNegation]

theorem specialCapMap_specialBoundaryToPiece (x : Cusp.Boundary) :
    specialCapMap (Cusp.specialBoundaryToPiece x) =
      Cusp.specialBoundaryToPiece (boundaryNeg x) := by
  change quotientNegation Cusp.specialData.correction Cusp.specialData.radius
      (Cusp.boundaryInclusion Cusp.specialData Cusp.specialHeight x).val =
    (Cusp.boundaryInclusion Cusp.specialData Cusp.specialHeight (boundaryNeg x)).val
  exact quotientNegation_boundaryInclusion Cusp.specialData Cusp.specialHeight x

/-- Literal covariance of the original full-cap attaching map with the
native boundary involution. No homology action is assumed. -/
theorem boundaryToFilling_neg :
    (boundaryToFilling none).comp boundaryNeg = specialCapMap.comp (boundaryToFilling none) := by
  rw [boundaryToFilling_cusp]
  apply ContinuousMap.ext
  intro x
  exact (specialCapMap_specialBoundaryToPiece x).symm

end Wikipedia.HopfProblem.CuspNegation
