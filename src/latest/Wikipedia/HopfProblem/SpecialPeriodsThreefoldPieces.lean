import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticPieces
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspPiece
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldStarHolomorphic

/-!
# The four actual local threefold pieces

The regular quotient family, the full toric cusp quotient, and the two
main twisted elliptic fillings are assembled over the chosen actual
four-patch cover.  Every local projection is proper, surjective, and
holomorphic.  The common coordinate model is obtained from the native
cusp model by the proved complex-linear coordinate change.

All spaces, atlases, maps, and local geometric properties are constructed
here without parameters or assumed filling data.  The actual overlap
maps are supplied by the subsequent assembly stage.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] triangleCompactifiedChartedSpace

/-- The proved cap relating the chosen cusp patch to the actual analytic
radius of the global periods. -/
theorem specialCuspRadius_le : specialBaseCover.radius none ≤ specialCuspData.radius :=
  specialBaseCover_cusp_radius_bounds.2.1.le

/-- The full genuine cusp piece, including its central fibre. -/
abbrev SpecialCuspPiece := CuspPiece.Space specialCuspData specialBaseCover

@[instance_reducible] def specialCuspPieceChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) SpecialCuspPiece :=
  CuspPiece.commonChartedSpace specialCuspData specialBaseCover specialCuspRadius_le

def specialCuspPieceProjection : SpecialCuspPiece → specialBaseCover.fillingPatch none :=
  CuspPiece.projection specialCuspData specialBaseCover

def specialCuspPieceProjectionToBase : SpecialCuspPiece → TriangleCompactifiedOrbitSpace :=
  CuspPiece.projectionToBase specialCuspData specialBaseCover

theorem specialCuspPieceProjection_proper : IsProperMap specialCuspPieceProjection :=
  CuspPiece.projection_proper specialCuspData specialBaseCover specialCuspRadius_le

theorem specialCuspPieceProjection_surjective : Function.Surjective specialCuspPieceProjection :=
  CuspPiece.projection_surjective specialCuspData specialBaseCover

theorem specialCuspPieceProjectionToBase_holomorphic :
    letI := specialCuspPieceChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
      specialCuspPieceProjectionToBase :=
  CuspPiece.projectionToBase_common_holomorphic specialCuspData specialBaseCover
    specialCuspRadius_le

theorem specialCuspPiece_t2Space : T2Space SpecialCuspPiece :=
  CuspPiece.space_t2Space specialCuspData specialBaseCover specialCuspRadius_le

theorem specialCuspPiece_secondCountable : SecondCountableTopology SpecialCuspPiece :=
  CuspPiece.space_secondCountable specialCuspData specialBaseCover specialCuspRadius_le

theorem specialCuspPiece_isManifold :
    letI := specialCuspPieceChartedSpace
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω SpecialCuspPiece :=
  CuspPiece.common_isManifold specialCuspData specialBaseCover specialCuspRadius_le

theorem specialCuspPiece_nonempty : Nonempty SpecialCuspPiece :=
  CuspPiece.space_nonempty specialCuspData specialBaseCover

/-- The actual topological pieces over the four members of the fixed cover. -/
def localPiece : Index → TopCat
  | none => TopCat.of SpecialRegularFamily
  | some none => TopCat.of SpecialCuspPiece
  | some (some j) => TopCat.of (SpecialEllipticPiece j)

/-- The common analytic model keeps each of the native intrinsic complex
structures; the cusp grouping is the proved analytic model change. -/
@[instance_reducible] def localPieceChartedSpace (i : Index) :
    ChartedSpace (ℂ × ComplexPlane₂) (localPiece i) := by
  cases i with
  | none => exact specialRegularFamilyChartedSpace
  | some i =>
      cases i with
      | none => exact specialCuspPieceChartedSpace
      | some j => exact specialEllipticPieceChartedSpace j

attribute [local instance] localPieceChartedSpace

theorem localPiece_nonempty (i : Index) : Nonempty (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_nonempty
  | some i =>
      cases i with
      | none => exact specialCuspPiece_nonempty
      | some j => exact specialEllipticPiece_nonempty j

theorem localPiece_t2Space (i : Index) : T2Space (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_t2Space
  | some i =>
      cases i with
      | none => exact specialCuspPiece_t2Space
      | some j => exact specialEllipticPiece_t2Space j

theorem localPiece_secondCountable (i : Index) : SecondCountableTopology (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_secondCountable
  | some i =>
      cases i with
      | none => exact specialCuspPiece_secondCountable
      | some j => exact specialEllipticPiece_secondCountable j

theorem localPiece_isManifold (i : Index) :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (localPiece i) := by
  cases i with
  | none => exact specialRegularFamily_isManifold
  | some i =>
      cases i with
      | none => exact specialCuspPiece_isManifold
      | some j => exact specialEllipticPiece_isManifold j

/-- Each local projection has precisely its own actual patch as codomain. -/
def localProjection : (i : Index) → localPiece i → specialBaseCover.patch i
  | none => specialRegularFamilyProjection
  | some none => specialCuspPieceProjection
  | some (some j) => specialEllipticPieceProjection j

theorem localProjection_proper (i : Index) : IsProperMap (localProjection i) := by
  cases i with
  | none => exact specialRegularFamilyProjection_proper
  | some i =>
      cases i with
      | none => exact specialCuspPieceProjection_proper
      | some j => exact specialEllipticPieceProjection_proper j

theorem localProjection_surjective (i : Index) : Function.Surjective (localProjection i) := by
  cases i with
  | none => exact specialRegularFamilyProjection_surjective
  | some i =>
      cases i with
      | none => exact specialCuspPieceProjection_surjective
      | some j => exact specialEllipticPieceProjection_surjective j

/-- The same local projections to the whole actual compactified curve. -/
def localProjectionToBase (i : Index) (x : localPiece i) : TriangleCompactifiedOrbitSpace :=
  localProjection i x

theorem localProjectionToBase_mem (i : Index) (x : localPiece i) :
    localProjectionToBase i x ∈ specialBaseCover.patch i := (localProjection i x).property

theorem localProjectionToBase_continuous (i : Index) : Continuous (localProjectionToBase i) :=
  continuous_subtype_val.comp (localProjection_proper i).continuous

theorem localProjectionToBase_holomorphic (i : Index) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
      (localProjectionToBase i) := by
  cases i with
  | none => exact specialRegularFamilyProjectionToBase_holomorphic
  | some i =>
      cases i with
      | none => exact specialCuspPieceProjectionToBase_holomorphic
      | some j => exact specialEllipticPieceProjectionToBase_holomorphic j

/-- Bundled actual projections for the topological gluing constructor. -/
def localBaseMap (i : Index) : C(localPiece i, TriangleCompactifiedOrbitSpace) :=
  ⟨localProjectionToBase i, localProjectionToBase_continuous i⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
