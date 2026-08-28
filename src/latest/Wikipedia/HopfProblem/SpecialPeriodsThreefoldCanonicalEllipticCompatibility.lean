import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticPullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticRestriction

/-!
# Compatibility of the two native elliptic canonical comparisons

The actual full-filling parametrization agrees with the actual global
patch inclusion after restricting to the chosen small open piece.  The
manifold chain rule therefore identifies their canonical pullbacks, with
restriction defined through the genuine open-submanifold differential.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  Threefold.chartedSpace

local instance fullCompatibilityManifold (j : Kind) :
    IsManifold IF ω (SpecialFullFilling j) := (specialFullFilling_construction j).2.2.1

local instance pieceCompatibilityManifold (j : Kind) :
    IsManifold IF ω (SpecialEllipticPiece j) := specialEllipticPiece_isManifold j

local instance globalCompatibilityManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

theorem piece_mem_fullParametrization_source (j : Kind) (x : SpecialEllipticPiece j) :
    x.val ∈ (EllipticGeometry.fullParametrization j).source := by
  rw [EllipticGeometry.fullParametrization_source]
  exact x.property

/-- This is equality of the actual maps, not a separately imposed
compatibility of canonical-bundle coordinates. -/
theorem fullParametrization_comp_pieceInclusion (j : Kind) :
    (EllipticGeometry.fullParametrization j : SpecialFullFilling j → Threefold.Space) ∘
      pieceInclusion j = EllipticGeometry.inclusion j := by
  funext x
  exact EllipticGeometry.fullParametrization_apply j x

/-- Canonical pullback along the full parametrization, followed by native
open-subset restriction, is exactly pullback along the global patch inclusion. -/
theorem restriction_fullPatchPullback (j : Kind) (x : SpecialEllipticPiece j)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.inclusion j x)) :
    restriction j x
        (fullPatchPullback j x.val (piece_mem_fullParametrization_source j x) v) =
      patchPullback j x v := by
  have hf := (pieceInclusion_isLocalDiffeomorph j x).mdifferentiableAt (by simp)
  have hg := (EllipticGeometry.fullParametrization_isLocalDiffeomorphAt j
    (piece_mem_fullParametrization_source j x)).mdifferentiableAt (by simp)
  have hc := Pullback.pullbackLinear_comp hf hg
  change Pullback.pullbackLinear (pieceInclusion j) x
    (Pullback.pullbackLinear (EllipticGeometry.fullParametrization j) x.val v) =
      Pullback.pullbackLinear (EllipticGeometry.inclusion j) x v
  calc
    Pullback.pullbackLinear (pieceInclusion j) x
        (Pullback.pullbackLinear (EllipticGeometry.fullParametrization j) x.val v) =
      Pullback.pullbackLinear
        ((EllipticGeometry.fullParametrization j : SpecialFullFilling j → Threefold.Space) ∘
          pieceInclusion j) x v := (congrArg (fun A => A v) hc).symm
    _ = Pullback.pullbackLinear (EllipticGeometry.inclusion j) x v :=
      congrArg (fun f : SpecialEllipticPiece j → Threefold.Space =>
        id (α := ℂ) (Pullback.pullbackLinear f x v))
          (fullParametrization_comp_pieceInclusion j)

/-- The corresponding equality of genuine fibrewise continuous linear
equivalences. -/
theorem patchPullback_factorization (j : Kind) (x : SpecialEllipticPiece j) :
    patchPullback j x =
      (fullPatchPullback j x.val (piece_mem_fullParametrization_source j x)).trans
        (restriction j x) := by
  apply ContinuousLinearEquiv.ext
  funext v
  exact (restriction_fullPatchPullback j x v).symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic
