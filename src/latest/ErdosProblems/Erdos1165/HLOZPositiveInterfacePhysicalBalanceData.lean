/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalCoordinateRatio
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalScreenedEvent
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalBaseWindow
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalRowContainment

/-!
# Deterministic balance data for the physical positive-interface screen

The physical adjacent-shell comparison is valid precisely when the honest
same-rank base window contains both complete below-level shell rows and the
rows lie on the increasing side of the negative-binomial mass.  This module
packages those deterministic facts and turns them into the cofinal stopped
product used by the positive-interface recurrence.

There is deliberately no probability or event-tail field here.  A later
path-space payment must prove that the complement of these balance facts is
summable.
-/

open Set

namespace Erdos1165.HLOZPositiveInterfacePhysicalBalanceData

open FiniteDominoProductLaw
open HLOZAllCreationCofinalConditionalSharpWindow
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceLocalWindowData
open HLOZPositiveInterfacePhysicalCoordinateRatio
open HLOZPositiveInterfacePhysicalBaseWindow
open HLOZPositiveInterfacePhysicalRowContainment
open HLOZPositiveInterfacePhysicalScreenedEvent
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfacePhysicalWindows
open HLOZProposition48Candidates
open LazyDecomposition
open TilingCappedMarginalization
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedInsertedLocalTime
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A complete first physical row fits below a domino boundary cutoff only
if that boundary is no larger than the endpoint count indexing the row.
Together with the automatic reverse inequality (the domino maximum dominates
the oriented endpoint), this forces equality.  Thus shell zero exposes a
genuine dominance requirement; its failure cannot be declared a rare
large-deviation event without a separate argument. -/
theorem shellZero_complete_row_forces_boundary_le
    {m width i boundary : ℕ} (hwidth : 2 ≤ width) (hi : i < m)
    (hrow : acceptedPhysicalDeficitFailureWindow m width i 0 ⊆
      Finset.range (m - boundary)) :
    boundary ≤ i := by
  let v := m - i - 1
  have hvsum : i + v = m - 1 := by
    dsimp only [v]
    omega
  have hv : v ∈ acceptedPhysicalDeficitFailureWindow m width i 0 := by
    rw [mem_acceptedPhysicalDeficitFailureWindow, hvsum]
    constructor
    · omega
    · have hone : m - (m - 1) = 1 := by omega
      rw [hone]
      exact Nat.div_eq_of_lt (by omega)
  have hvcut := Finset.mem_range.mp (hrow hv)
  dsimp only [v] at hvcut
  omega

/-- Coordinatewise eligibility for the physical adjacent-shell comparison.
This is a retained-trace property: it depends on the exact creation atom and
away domino, but not on the inserted total selected inside the coordinate. -/
def positiveInterfacePhysicalCoordinateEligible
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold : ℕ}
    (width shell : ℕ)
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)) : Prop :=
  4 ≤ width ∧
    (shell + 2) * width ≤ m ∧
    Fintype.card (TilingCoordinatesAt t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) b.1) ≤
        m - (shell + 2) * width + 1 ∧
    15 * (m - shell * width -
      Fintype.card (TilingCoordinatesAt t
        ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap) b.1)) + 1 ≤
      Fintype.card (TilingCoordinatesAt t
        ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap) b.1) ∧
    prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (positiveInterfaceTerminal eta) b.1 <
      Fintype.card (TilingCoordinatesAt t
          ((PositiveInterfaceFiber eta).start cap)
          ((PositiveInterfaceFiber eta).retained cap) b.1) +
        max 1 (shell * width)

/-- The exact deterministic conditions under which every coordinate of a
positive-interface atom admits the physical adjacent-shell `4/3` comparison.

The first three numeric conditions identify two nonempty adjacent rows on the
increasing side of the negative-binomial law.  The last condition is the
exact fixed-boundary margin which retains both rows inside the honest
accepted-creation base.  The base's containment below the retained-count
cutoff is automatic. -/
structure PhysicalInterfaceBalanceData
    (t : DominoTiling) (o : Orientation) (m k externalThreshold width shell : ℕ)
    : Prop where
  width_ge_four : 4 ≤ width
  shells_fit : (shell + 2) * width ≤ m
  coordinate_fit : ∀
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)),
    Fintype.card (TilingCoordinatesAt t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) b.1) ≤
        m - (shell + 2) * width + 1
  below_mode : ∀
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)),
    15 * (m - shell * width -
      Fintype.card (TilingCoordinatesAt t
        ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap) b.1)) + 1 ≤
      Fintype.card (TilingCoordinatesAt t
        ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap) b.1)
  boundary_lt : ∀
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)),
    prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
        eta.1.1.external.start eta.1.1.external.retained
        (positiveInterfaceTerminal eta) b.1 <
      Fintype.card (TilingCoordinatesAt t
          ((PositiveInterfaceFiber eta).start cap)
          ((PositiveInterfaceFiber eta).retained cap) b.1) +
        max 1 (shell * width)

namespace PhysicalInterfaceBalanceData

/-- The coordinatewise eligibility predicate is sufficient for the exact
normalized local ratio, independently of all other coordinates in the atom. -/
theorem window_ratio_inter_base_of_eligible
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (hexternal : 0 < externalThreshold)
    (hm : 1 < m) (hk : 0 < k)
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap))
    (heligible : positiveInterfacePhysicalCoordinateEligible
      width shell eta cap b) :
    (∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
      if (v : ℕ) ∈ physicalDeficitFailureWindow m width
            (Fintype.card (TilingCoordinatesAt t
              ((PositiveInterfaceFiber eta).start cap)
              ((PositiveInterfaceFiber eta).retained cap) b.1)) (shell + 1) ∧
          (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
        coordinateMass
          (tilingAwayPointMass
            (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap)
            ((PositiveInterfaceFiber eta).distinguished cap))
          ((PositiveInterfaceFiber eta).upper cap) b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
          if (v : ℕ) ∈ physicalDeficitFailureWindow m width
                (Fintype.card (TilingCoordinatesAt t
                  ((PositiveInterfaceFiber eta).start cap)
                  ((PositiveInterfaceFiber eta).retained cap) b.1)) shell ∧
              (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
            coordinateMass
              (tilingAwayPointMass
                (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap)
                ((PositiveInterfaceFiber eta).distinguished cap))
              ((PositiveInterfaceFiber eta).upper cap) b v else 0 := by
  rcases heligible with
    ⟨hwidth, hfit, hcoordinate, hmode, hboundary⟩
  let fiber := PositiveInterfaceFiber eta
  let i := Fintype.card (TilingCoordinatesAt t
    (fiber.start cap) (fiber.retained cap) b.1)
  have hiPos : 0 < i := hexternal.trans_le
    (positiveInterfaceCoordinateCount_ge_externalThreshold eta cap b)
  have hupperUpper : ∀ v ∈ acceptedPhysicalDeficitFailureWindow
      m width i (shell + 1), v < fiber.upper cap b := by
    intro v hv
    have hvlt := (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
    change v < max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + 1
    omega
  have hlowerUpper : ∀ v ∈ acceptedPhysicalDeficitFailureWindow
      m width i shell, v < fiber.upper cap b := by
    intro v hv
    have hvlt := (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
    change v < max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + 1
    omega
  have hupperCap : ∀ v ∈ acceptedPhysicalDeficitFailureWindow
      m width i (shell + 1), v ≤ fiber.coordinateCap cap := by
    intro v hv
    have hvlt := (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
    change v ≤ max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + cap
    omega
  have hlowerCap : ∀ v ∈ acceptedPhysicalDeficitFailureWindow
      m width i shell, v ≤ fiber.coordinateCap cap := by
    intro v hv
    have hvlt := (mem_acceptedPhysicalDeficitFailureWindow.mp hv).1
    change v ≤ max eta.1.1.external.retainedCount
      (m + shellWidth48 m) + cap
    omega
  have hwidthPos : 0 < width := lt_of_lt_of_le (by omega) hwidth
  have hrows :=
    acceptedPhysicalAdjacentFailureWindows_subset_baseWindow_of_boundary_lt
      eta cap b hwidthPos hboundary
  exact tilingAway_coordinateMass_physicalAdjacentWindowRatio
    t (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap)
      (fiber.upper cap) b (positiveInterfaceBaseWindow eta cap b)
      hiPos hwidth hfit hcoordinate hmode
      (positiveInterfaceBaseWindow_subset_coordinateRange eta hm hk cap b)
      hrows.1 hrows.2 hupperUpper hlowerUpper hupperCap hlowerCap

/-- The deterministic balance certificate supplies exactly the normalized
coordinate inequality required by the physical cofinal product.  Finiteness
of the two rows inside the concrete cap is automatic from their strict
below-level membership and the concrete all-creation cap. -/
theorem window_ratio_inter_base
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (data : PhysicalInterfaceBalanceData t o m k externalThreshold width shell)
    (hexternal : 0 < externalThreshold)
    (hm : 1 < m) (hk : 0 < k)
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap)) :
    (∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
      if (v : ℕ) ∈ physicalDeficitFailureWindow m width
            (Fintype.card (TilingCoordinatesAt t
              ((PositiveInterfaceFiber eta).start cap)
              ((PositiveInterfaceFiber eta).retained cap) b.1)) (shell + 1) ∧
          (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
        coordinateMass
          (tilingAwayPointMass
            (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap)
            ((PositiveInterfaceFiber eta).distinguished cap))
          ((PositiveInterfaceFiber eta).upper cap) b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
          if (v : ℕ) ∈ physicalDeficitFailureWindow m width
                (Fintype.card (TilingCoordinatesAt t
                  ((PositiveInterfaceFiber eta).start cap)
                  ((PositiveInterfaceFiber eta).retained cap) b.1)) shell ∧
              (v : ℕ) ∈ positiveInterfaceBaseWindow eta cap b then
            coordinateMass
              (tilingAwayPointMass
                (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap)
                ((PositiveInterfaceFiber eta).distinguished cap))
      ((PositiveInterfaceFiber eta).upper cap) b v else 0 := by
  apply window_ratio_inter_base_of_eligible hexternal hm hk eta cap b
  exact ⟨data.width_ge_four, data.shells_fit,
    data.coordinate_fit eta cap b, data.below_mode eta cap b,
    data.boundary_lt eta cap b⟩

/-- A balance certificate gives the honest physical cofinal product with no
probability or product-bound premise. -/
noncomputable def physicalScreenedProductData
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (data : PhysicalInterfaceBalanceData t o m k externalThreshold width shell)
    (hexternal : 0 < externalThreshold) (hm : 1 < m) (hk : 0 < k)
    (threshold : ℕ → ℕ) (bound : ℕ) :
    OrientedAllCreationCofinalSharpWindowInterfaceProductData
      t o m k
      (positiveInterfacePhysicalScreenedEvent t o m k externalThreshold hm hk
        threshold width shell bound)
      threshold shell bound :=
  positiveInterfacePhysicalScreenedProductData t o m k externalThreshold
    hm hk threshold width shell bound
      (fun eta cap b ↦ data.window_ratio_inter_base hexternal hm hk eta cap b)

end PhysicalInterfaceBalanceData

end

end Erdos1165.HLOZPositiveInterfacePhysicalBalanceData
