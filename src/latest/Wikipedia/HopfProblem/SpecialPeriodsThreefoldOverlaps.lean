import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspOverlap
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticOverlaps

/-!
# Actual gluing data for the four constructed threefold pieces

The three genuine filling-to-regular partial biholomorphisms have exactly
the full base-overlap source and target.  Since the three selected filling
patches are pairwise disjoint, the proved star construction supplies every
transition, inverse identity, and cocycle identity.  Thus the actual
`ThreefoldGluing.Data` has no assumed transition or compatibility fields.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] triangleCompactifiedChartedSpace localPieceChartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The three actual partial biholomorphisms from fillings to the regular piece. -/
def localOverlap : (i : Puncture) →
    PartialDiffeomorph IF IF (localPiece (some i)) (localPiece none) ω
  | none => specialCuspOverlap
  | some j => specialEllipticOverlap j

theorem localOverlap_source (i : Puncture) :
    (localOverlap i).source = localBaseMap (some i) ⁻¹'
      (specialBaseCover.patch none : Set TriangleCompactifiedOrbitSpace) := by
  cases i with
  | none => exact specialCuspOverlap_source
  | some j => exact specialEllipticOverlap_source j

theorem localOverlap_target (i : Puncture) :
    (localOverlap i).target = localBaseMap none ⁻¹'
      (specialBaseCover.patch (some i) : Set TriangleCompactifiedOrbitSpace) := by
  cases i with
  | none => exact specialCuspOverlap_target
  | some j => exact specialEllipticOverlap_target j

theorem localOverlap_base (i : Puncture) (x : localPiece (some i))
    (hx : x ∈ (localOverlap i).source) :
    localBaseMap none (localOverlap i x) = localBaseMap (some i) x := by
  cases i with
  | none => exact specialCuspOverlap_base x hx
  | some j => exact specialEllipticOverlap_base j x hx

/-- The actual four pieces and their verified full overlaps instantiate
the star input without any unproved gluing or overlap assumptions. -/
abbrev gluingStar : Star.Input TriangleCompactifiedOrbitSpace Puncture where
  patch := specialBaseCover.patch
  cover := specialBaseCover.isOpenCover
  disjoint := specialBaseCover.pairwise_disjoint
  piece := localPiece
  toBase := localBaseMap
  toBase_mem := localProjectionToBase_mem
  overlap i := (localOverlap i).toOpenPartialHomeomorph
  source_eq := localOverlap_source
  target_eq := localOverlap_target
  preserves_base := localOverlap_base

/-- The actual complete gluing data, including all derived cocycle and
inverse laws, rather than a space assumed to have these local models. -/
abbrev gluingData : ThreefoldGluing.Data TriangleCompactifiedOrbitSpace :=
  gluingStar.toData

/-- Every transition of these actual data is holomorphic on its full source. -/
theorem gluingData_transition_holomorphic (i j : Index) :
    ContMDiffOn IF IF ω (gluingData.transition i j) (gluingData.transition i j).source :=
  gluingStar.toData_transition_holomorphic
    (fun i => (localOverlap i).contMDiffOn)
    (fun i => (localOverlap i).symm.contMDiffOn) i j

/-- The local projection in the gluing data is the already constructed
proper projection, with no change of its target patch. -/
theorem gluingData_localProjection_eq (i : Index) :
    (gluingData.localProjection i : localPiece i → specialBaseCover.patch i) =
      localProjection i := rfl

theorem gluingData_localProjection_proper (i : Index) :
    IsProperMap (gluingData.localProjection i) := localProjection_proper i

theorem gluingData_localProjection_surjective (i : Index) :
    Function.Surjective (gluingData.localProjection i) := localProjection_surjective i

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
