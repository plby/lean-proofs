/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalBalanceData

/-!
# Boundary-free physical interface coordinate ratio

The same-rank positive-interface base is truncated by the larger fixed
boundary local time of the two endpoints of an away domino.  When the
oriented endpoint is not dominant, that truncation can remove the lower
comparison row even though the upper row is nonempty.  Such a coordinate
cannot be normalized inside one stopped rank.

The negative-binomial comparison itself does not need this truncation.  This
module records the boundary-free coordinate estimate between the two honest
below-level physical rows.  Its lower row may subsequently be partitioned by
the actual endpoint-count increment and stopped at rank `k + delta`; no
same-rank accepted-base claim is made here.
-/

open scoped BigOperators

namespace Erdos1165.HLOZPositiveInterfaceActualDeltaCoordinateRatio

open FiniteDominoProductLaw
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceLocalWindowData
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfacePhysicalWindows
open HLOZPositiveInterfaceSupportSelector
open HLOZProposition48Candidates
open LazyDecomposition ScreeningInstantiation SmallWindow
open TilingAwayNegativeBinomial TilingCappedMarginalization
open TilingOrientedSupportAwayCoordinates TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The literal capped away-coordinate law inherits the checked adjacent
physical-row comparison without intersecting either row with a same-rank
accepted base.  All premises merely say that the two finite rows occur in the
chosen truncation and cap. -/
theorem tilingAway_coordinateMass_acceptedPhysicalAdjacentWindowRatio
    {retainedCount cap m width shell : ℕ}
    (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x retainedCount) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D)
    (hiPos : 0 < Fintype.card (TilingCoordinatesAt t x r b.1))
    (hwidth : 4 ≤ width)
    (hfit : (shell + 2) * width ≤ m)
    (hi : Fintype.card (TilingCoordinatesAt t x r b.1) ≤
      m - (shell + 2) * width + 1)
    (hendpoint :
      15 * (m - shell * width -
        Fintype.card (TilingCoordinatesAt t x r b.1)) + 1 ≤
          Fintype.card (TilingCoordinatesAt t x r b.1))
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
      if (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1) then
        coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
          upper b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin (upper b),
          if (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t x r b.1)) shell then
            coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
              upper b v else 0 := by
  let i := Fintype.card (TilingCoordinatesAt t x r b.1)
  have hmass : windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i (shell + 1)) ≤
      (4 / 3 : ℝ) * windowMass i
        (acceptedPhysicalDeficitFailureWindow m width i shell) :=
    acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_endpoint
      hiPos hwidth hfit hi hendpoint
  exact tilingAway_coordinateMass_window_ratio
    (cap := cap) t x r D upper b
      (acceptedPhysicalDeficitFailureWindow m width i (shell + 1))
      (acceptedPhysicalDeficitFailureWindow m width i shell)
      hupperUpper hlowerUpper hupperCap hlowerCap hiPos hmass

/-- On the concrete positive-interface stopped fibre, the truncation and cap
contain both honest below-level rows automatically.  Consequently only the
fit and rising-mode conditions remain; notably there is no endpoint-boundary
dominance premise. -/
theorem positiveInterface_coordinateMass_acceptedPhysicalAdjacentWindowRatio
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (hexternal : 0 < externalThreshold)
    (hwidth : 4 ≤ width) (hfit : (shell + 2) * width ≤ m)
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap))
    (hi : Fintype.card (TilingCoordinatesAt t
      ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap) b.1) ≤
        m - (shell + 2) * width + 1)
    (hendpoint :
      15 * (m - shell * width -
        Fintype.card (TilingCoordinatesAt t
          ((PositiveInterfaceFiber eta).start cap)
          ((PositiveInterfaceFiber eta).retained cap) b.1)) + 1 ≤
      Fintype.card (TilingCoordinatesAt t
        ((PositiveInterfaceFiber eta).start cap)
        ((PositiveInterfaceFiber eta).retained cap) b.1)) :
    (∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
      if (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1)) (shell + 1)
      then
        coordinateMass
          (tilingAwayPointMass
            (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap)
            ((PositiveInterfaceFiber eta).distinguished cap))
          ((PositiveInterfaceFiber eta).upper cap) b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin ((PositiveInterfaceFiber eta).upper cap b),
          if (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap) b.1)) shell
          then
            coordinateMass
              (tilingAwayPointMass
                (cap := (PositiveInterfaceFiber eta).coordinateCap cap) t
                ((PositiveInterfaceFiber eta).start cap)
                ((PositiveInterfaceFiber eta).retained cap)
                ((PositiveInterfaceFiber eta).distinguished cap))
              ((PositiveInterfaceFiber eta).upper cap) b v else 0 := by
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
  exact tilingAway_coordinateMass_acceptedPhysicalAdjacentWindowRatio
    t (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap)
      (fiber.upper cap) b hiPos hwidth hfit hi hendpoint
      hupperUpper hlowerUpper hupperCap hlowerCap

end

end Erdos1165.HLOZPositiveInterfaceActualDeltaCoordinateRatio
