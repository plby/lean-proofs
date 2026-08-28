import Wikipedia.HopfProblem.CuspCoinvariantExtensionExistence
import Wikipedia.HopfProblem.CuspCoinvariantExtensionPuncturedSpecial
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepAction

/-!
# The collar-adjusted map on the actual cusp piece of the threefold

The construction is specialized to the already chosen original cusp
correction and filling radius.  The outer formula is the original regular
gamma map through the actual gluing overlap.  The symmetry statement uses
the original global additive-circle action and actual cusp inclusion.
These are continuous marked maps only; no submersion or product claim is
made about the modified inner region.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open SpecialPeriods SpecialPeriods.Threefold CuspUniformization
open TrianglePeriodFamily.GammaZero ThreefoldHomologyFinitenessCusp

attribute [local instance] triangleCompactifiedChartedSpace
  triangleRegularQuotientChartedSpace specialRegularFamilyChartedSpace
  specialCuspPieceChartedSpace

/-- A proved extension on the original chosen cusp filling, at any
prescribed positive outer-collar bound. -/
def specialCollarExtension (bound : ℝ) (hbound : 0 < bound) :
    CollarExtension CuspAttaching.data bound :=
  collarExtension CuspAttaching.data bound hbound

/-- The domain is literally the actual cusp piece in the original gluing. -/
def specialCapGamma (bound : ℝ) (hbound : 0 < bound) :
    C(SpecialCuspPiece, AddCircle (1 : ℝ)) :=
  (specialCollarExtension bound hbound).map

/-- The genuine native delta flow, with the unchanged real parameter. -/
theorem specialCapGamma_realFlow (bound : ℝ) (hbound : 0 < bound)
    (t : ℝ) (x : SpecialCuspPiece) :
    specialCapGamma bound hbound (VerticalAction.Cusp.specialFlow (t : ℂ) x) =
      specialCapGamma bound hbound x :=
  (specialCollarExtension bound hbound).realFlow t x

/-- Exact agreement with the original regular-family gamma throughout
the whole outer region of the original cusp overlap. -/
theorem specialCapGamma_outer_regular (bound : ℝ) (hbound : 0 < bound)
    (x : PuncturedQuotient CuspAttaching.data.correction CuspAttaching.data.radius)
    (hx : (specialCollarExtension bound hbound).innerRadius ≤
      parameterNorm CuspAttaching.data x.val) :
    specialCapGamma bound hbound x.val =
      familyGamma CuspAttaching.regularData (specialCuspOverlap x.val) :=
  ((specialCollarExtension bound hbound).outer x hx).trans
    (familyGamma_specialCuspOverlap x).symm

/-- The comparison uses the actual equality of original gluing
representatives, not a map into a replacement filling. -/
theorem specialCapGamma_outer_inclusion (bound : ℝ) (hbound : 0 < bound)
    (x : PuncturedQuotient CuspAttaching.data.correction CuspAttaching.data.radius)
    (y : SpecialRegularFamily)
    (hx : (specialCollarExtension bound hbound).innerRadius ≤
      parameterNorm CuspAttaching.data x.val)
    (h : inclusion (some none) x.val = inclusion none y) :
    specialCapGamma bound hbound x.val = familyGamma CuspAttaching.regularData y :=
  ((specialCollarExtension bound hbound).outer x hx).trans
    (familyGamma_eq_puncturedGamma_of_inclusion_eq x y h).symm

/-- The original global circle orbits, restricted to the actual cusp
piece, are fibres of the constructed continuous circle map. -/
theorem specialCapGamma_eq_of_globalCircle_related (bound : ℝ) (hbound : 0 < bound)
    (t : AddCircle (1 : ℝ)) (x y : SpecialCuspPiece)
    (h : Homology.DeltaSweep.actionMap (t, CuspGeometry.inclusion x) =
      CuspGeometry.inclusion y) :
    specialCapGamma bound hbound x = specialCapGamma bound hbound y := by
  induction t using QuotientAddGroup.induction_on with
  | H t =>
    rw [Homology.DeltaSweep.actionMap_real, VerticalAction.flow_cusp] at h
    have hy : VerticalAction.Cusp.specialFlow (t : ℂ) x = y :=
      CuspGeometry.inclusion_injective h
    exact (specialCapGamma_realFlow bound hbound t x).symm.trans
      (congrArg (specialCapGamma bound hbound) hy)

/-- The outer comparison holds on an actual open annulus in the native cap. -/
theorem specialCapGamma_outerCollar_isOpen (bound : ℝ) (hbound : 0 < bound) :
    IsOpen {x : SpecialCuspPiece |
      (specialCollarExtension bound hbound).innerRadius < ‖CuspGeometry.parameter x‖} :=
  CollarExtension.outerCollar_isOpen CuspAttaching.data bound
    (specialCollarExtension bound hbound)

end Wikipedia.HopfProblem.CuspCoinvariantExtension
