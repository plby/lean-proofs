/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalWindowRatio

/-!
# Capped coordinate-mass lift of the physical shell comparison

This is the normalization adapter used by the cofinal stopped-product
interface.  Its hypotheses are deterministic support facts: the honest base
window removes the saturated at/above-level part of the raw deficit label,
contains both complete physical rows, and both rows lie inside the finite cap.
-/

open scoped BigOperators

namespace Erdos1165.HLOZPositiveInterfacePhysicalCoordinateRatio

open FiniteDominoProductLaw
open HLOZPositiveInterfacePhysicalWindows
open HLOZPositiveInterfacePhysicalWindowRatio
open ScreeningInstantiation SmallWindow TilingAwayNegativeBinomial
open TilingCappedMarginalization TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Transfer the source-correct physical adjacent-shell estimate to the
literal capped away-coordinate law. -/
theorem tilingAway_coordinateMass_physicalAdjacentWindowRatio
    {retainedCount cap m width shell : ℕ}
    (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x retainedCount) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D) (base : Finset ℕ)
    (hiPos : 0 < Fintype.card (TilingCoordinatesAt t x r b.1))
    (hwidth : 4 ≤ width)
    (hfit : (shell + 2) * width ≤ m)
    (hi : Fintype.card (TilingCoordinatesAt t x r b.1) ≤
      m - (shell + 2) * width + 1)
    (hendpoint :
      15 * (m - shell * width -
        Fintype.card (TilingCoordinatesAt t x r b.1)) + 1 ≤
          Fintype.card (TilingCoordinatesAt t x r b.1))
    (hbaseBelow : base ⊆ Finset.range
      (m - Fintype.card (TilingCoordinatesAt t x r b.1)))
    (hupperBase : acceptedPhysicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1) ⊆ base)
    (hlowerBase : acceptedPhysicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t x r b.1)) shell ⊆ base)
    (hupperUpper : ∀ v ∈ acceptedPhysicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1),
        v < upper b)
    (hlowerUpper : ∀ v ∈ acceptedPhysicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t x r b.1)) shell,
        v < upper b)
    (hupperCap : ∀ v ∈ acceptedPhysicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1),
        v ≤ cap)
    (hlowerCap : ∀ v ∈ acceptedPhysicalDeficitFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t x r b.1)) shell,
        v ≤ cap) :
    (∑ v : Fin (upper b),
      if (v : ℕ) ∈ physicalDeficitFailureWindow m width
            (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1) ∧
          (v : ℕ) ∈ base then
        coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
          upper b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin (upper b),
          if (v : ℕ) ∈ physicalDeficitFailureWindow m width
                (Fintype.card (TilingCoordinatesAt t x r b.1)) shell ∧
              (v : ℕ) ∈ base then
            coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
              upper b v else 0 := by
  classical
  let i := Fintype.card (TilingCoordinatesAt t x r b.1)
  let upperWindow := acceptedPhysicalDeficitFailureWindow m width i (shell + 1)
  let lowerWindow := acceptedPhysicalDeficitFailureWindow m width i shell
  have hupperEq :
      physicalDeficitFailureWindow m width i (shell + 1) ∩ base =
        upperWindow :=
    physical_inter_base_eq_accepted hbaseBelow hupperBase
  have hlowerEq :
      physicalDeficitFailureWindow m width i shell ∩ base = lowerWindow :=
    physical_inter_base_eq_accepted hbaseBelow hlowerBase
  have hmass : windowMass i upperWindow ≤
      (4 / 3 : ℝ) * windowMass i lowerWindow :=
    acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_endpoint
      hiPos hwidth hfit hi hendpoint
  have hcoordinate := tilingAway_coordinateMass_window_ratio
    (cap := cap) t x r D upper b upperWindow lowerWindow
      hupperUpper hlowerUpper hupperCap hlowerCap hiPos hmass
  simpa only [i, upperWindow, lowerWindow, ← Finset.mem_inter,
    hupperEq, hlowerEq] using hcoordinate

end

end Erdos1165.HLOZPositiveInterfacePhysicalCoordinateRatio
