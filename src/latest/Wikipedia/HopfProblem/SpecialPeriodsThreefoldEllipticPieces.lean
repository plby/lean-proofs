import Wikipedia.HopfProblem.SpecialPeriodsThreefoldChosenBase
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingPieces

/-!
# The two unconditional small elliptic pieces

The actual admissible period map and the chosen disjoint base discs
instantiate the genuine logarithmically twisted elliptic fillings.  Their
projections are proper, surjective, and holomorphic over the exact selected
patches in the compact triangle base.  The two main source twists are built
into the filling construction; no local filling or geometric property is
assumed here.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] triangleCompactifiedChartedSpace

/-- The actual small elliptic piece for the source's indicated main twist. -/
abbrev SpecialEllipticPiece (j : Elliptic.Kind) :=
  EllipticFilling.Piece specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
    specialBaseCover j

@[instance_reducible] def specialEllipticPieceChartedSpace (j : Elliptic.Kind) :
    ChartedSpace (ℂ × ComplexPlane₂) (SpecialEllipticPiece j) :=
  EllipticFilling.pieceChartedSpace specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

def specialEllipticPieceProjection (j : Elliptic.Kind) :
    SpecialEllipticPiece j → specialBaseCover.fillingPatch (some j) :=
  EllipticFilling.pieceProjection specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

def specialEllipticPieceProjectionToBase (j : Elliptic.Kind) :
    SpecialEllipticPiece j → TriangleCompactifiedOrbitSpace :=
  EllipticFilling.pieceProjectionToBase specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

@[simp] theorem specialEllipticPieceProjectionToBase_eq (j : Elliptic.Kind)
    (x : SpecialEllipticPiece j) :
    specialEllipticPieceProjectionToBase j x =
      (specialEllipticPieceProjection j x : TriangleCompactifiedOrbitSpace) := rfl

theorem specialEllipticPieceProjectionToBase_mem (j : Elliptic.Kind)
    (x : SpecialEllipticPiece j) :
    specialEllipticPieceProjectionToBase j x ∈ specialBaseCover.fillingPatch (some j) :=
  (specialEllipticPieceProjection j x).property

theorem specialEllipticPieceProjection_proper (j : Elliptic.Kind) :
    IsProperMap (specialEllipticPieceProjection j) :=
  EllipticFilling.pieceProjection_proper specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

theorem specialEllipticPieceProjection_surjective (j : Elliptic.Kind) :
    Function.Surjective (specialEllipticPieceProjection j) :=
  EllipticFilling.pieceProjection_surjective specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

theorem specialEllipticPieceProjectionToBase_continuous (j : Elliptic.Kind) :
    Continuous (specialEllipticPieceProjectionToBase j) :=
  continuous_subtype_val.comp (EllipticFilling.pieceProjection_continuous specialPeriodMap
    specialPeriodMap_generator₁ specialPeriodMap_generator₂ specialBaseCover j)

theorem specialEllipticPieceProjectionToBase_holomorphic (j : Elliptic.Kind) :
    letI := specialEllipticPieceChartedSpace j
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) 𝓘(ℂ) ω
      (specialEllipticPieceProjectionToBase j) :=
  EllipticFilling.pieceProjectionToBase_holomorphic specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

theorem specialEllipticPiece_t2Space (j : Elliptic.Kind) :
    T2Space (SpecialEllipticPiece j) :=
  EllipticFilling.piece_t2Space specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

theorem specialEllipticPiece_secondCountable (j : Elliptic.Kind) :
    SecondCountableTopology (SpecialEllipticPiece j) :=
  EllipticFilling.piece_secondCountable specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

theorem specialEllipticPiece_isManifold (j : Elliptic.Kind) :
    letI := specialEllipticPieceChartedSpace j
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (SpecialEllipticPiece j) :=
  EllipticFilling.piece_isManifold specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j

/-- A point in each full piece exists over its actual central base point. -/
theorem specialEllipticPiece_nonempty (j : Elliptic.Kind) :
    Nonempty (SpecialEllipticPiece j) := by
  obtain ⟨x, _⟩ := specialEllipticPieceProjection_surjective j
    ⟨puncturePoint (some j), specialBaseCover.point_mem_fillingPatch (some j)⟩
  exact ⟨x⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
