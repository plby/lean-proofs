import Wikipedia.HopfProblem.SpecialPeriodsThreefoldPieces
import Wikipedia.HopfProblem.EllipticEquivariantCentralTopology
import Wikipedia.HopfProblem.CuspFibreTori
import Wikipedia.HopfProblem.FibreTopology

/-!
# Connected fibres of all four actual local pieces

The regular fibres are the original period tori. The cusp fibres are
the actual toric-quotient fibres, and the elliptic fibres retain the
literal varying-period quotient topology. Restricting radii and changing
the base coordinates preserve these fibres homeomorphically.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open FibreTopology

attribute [local instance] triangleRegularQuotientChartedSpace
  triangleOrbitChartedSpace triangleCompactifiedChartedSpace

theorem specialRegularFamilyProjection_fibre_isConnected (b : regularPatch) :
    IsConnected (specialRegularFamilyProjection ⁻¹' {b}) := by
  let D := regularFamilyData specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂
  have hf (q : TriangleRegularQuotient) : IsConnected (D.projection ⁻¹' {q}) := by
    obtain ⟨z, rfl⟩ := (TrianglePeriodFamily.regularCovering specialPeriodMap
      specialPeriodMap_generator₁ specialPeriodMap_generator₂).surjective q
    apply isConnected_iff_connectedSpace.mpr
    exact (D.fibreHomeomorph (TrianglePeriodFamily.regularCovering specialPeriodMap
      specialPeriodMap_generator₁ specialPeriodMap_generator₂) z).connectedSpace_iff.mp
        inferInstance
  change IsConnected ((regularBiholomorph.toHomeomorph ∘ D.projection) ⁻¹' {b})
  exact fibre_isConnected_comp_homeomorph D.projection regularBiholomorph.toHomeomorph b
    (hf (regularBiholomorph.symm b))

theorem specialCuspPieceCoordinate_fibre_isConnected
    (b : coordinateBall (specialBaseCover.radius none)) :
    IsConnected (CuspPiece.coordinate specialCuspData specialBaseCover ⁻¹' {b}) := by
  let D := CuspPiece.restrictedData specialCuspData specialBaseCover specialCuspRadius_le
  have he : CuspPiece.coordinate specialCuspData specialBaseCover ⁻¹' {b} =
      CuspQuotient.projection specialCuspData.correction (specialBaseCover.radius none) ⁻¹'
        {(b : ℂ)} := by
    ext x
    exact Subtype.ext_iff
  rw [he]
  exact CuspUniformization.fibre_connected specialCuspData.correction
    (specialBaseCover.radius none) (specialBaseCover.radius_pos none) D.radius_lt_one
    D.holomorphic D.smallDrift b

theorem specialCuspPieceProjection_fibre_isConnected
    (b : specialBaseCover.fillingPatch none) :
    IsConnected (specialCuspPieceProjection ⁻¹' {b}) := by
  change IsConnected ((((specialBaseCover.fillingChart none).symm.toHomeomorph) ∘
    CuspPiece.coordinate specialCuspData specialBaseCover) ⁻¹' {b})
  exact fibre_isConnected_comp_homeomorph
    (CuspPiece.coordinate specialCuspData specialBaseCover)
    (specialBaseCover.fillingChart none).symm.toHomeomorph b
    (specialCuspPieceCoordinate_fibre_isConnected (specialBaseCover.fillingChart none b))

theorem specialEllipticPieceCoordinate_fibre_isConnected (j : Elliptic.Kind)
    (b : coordinateBall (specialBaseCover.radius (some j))) :
    IsConnected (EllipticFilling.pieceCoordinate specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j ⁻¹' {b}) := by
  let f := EllipticFilling.fillingProjection specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ j
  let S : Set Disc := EllipticFilling.smallDisc (specialBaseCover.radius (some j))
  let e := EllipticFilling.smallDiscHomeomorph (specialBaseCover.radius (some j))
    (specialBaseCover.radius_lt_chart (some j))
  have hf (q : Disc) : IsConnected (f ⁻¹' {q}) :=
    (EllipticFilling.localData specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ j).projection_fibre_isConnected j.twist
        (Elliptic.mainTwist_admissible j) q
  change IsConnected ((e ∘ S.restrictPreimage f) ⁻¹' {b})
  exact fibre_isConnected_comp_homeomorph (S.restrictPreimage f) e b
    (restrictPreimage_fibre_isConnected f S (e.symm b) (hf (e.symm b).val))

theorem specialEllipticPieceProjection_fibre_isConnected (j : Elliptic.Kind)
    (b : specialBaseCover.fillingPatch (some j)) :
    IsConnected (specialEllipticPieceProjection j ⁻¹' {b}) := by
  change IsConnected ((((specialBaseCover.fillingChart (some j)).symm.toHomeomorph) ∘
    EllipticFilling.pieceCoordinate specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j) ⁻¹' {b})
  exact fibre_isConnected_comp_homeomorph
    (EllipticFilling.pieceCoordinate specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ specialBaseCover j)
    (specialBaseCover.fillingChart (some j)).symm.toHomeomorph b
    (specialEllipticPieceCoordinate_fibre_isConnected j
      (specialBaseCover.fillingChart (some j) b))

/-- Each fibre of each one of the four constructed pieces is genuinely connected. -/
theorem localProjection_fibre_isConnected (i : Index) (b : specialBaseCover.patch i) :
    IsConnected (localProjection i ⁻¹' {b}) := by
  cases i with
  | none => exact specialRegularFamilyProjection_fibre_isConnected b
  | some i =>
      cases i with
      | none => exact specialCuspPieceProjection_fibre_isConnected b
      | some j => exact specialEllipticPieceProjection_fibre_isConnected j b

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
