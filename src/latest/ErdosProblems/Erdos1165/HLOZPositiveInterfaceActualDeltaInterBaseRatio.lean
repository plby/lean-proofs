/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfaceActualDeltaCoordinateRatio

/-!
# Accepted-source to actual-delta physical-row ratio

The physical source event still carries its honest same-rank base predicate:
at the source vector both endpoints of every exposed domino are below level
`m`.  Only the comparison row must be allowed to leave that base and change
the stopping rank.  This module combines monotonicity of the nonnegative
coordinate law with the boundary-free adjacent-row estimate, producing the
exact one-sided inequality needed by an actual-delta replacement product.
-/

open scoped BigOperators

namespace Erdos1165.HLOZPositiveInterfaceActualDeltaInterBaseRatio

open FiniteDominoProductLaw
open HLOZAllSixExactCoordinateProductClosure
open HLOZPositiveInterfaceActualDeltaCoordinateRatio
open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfaceLocalWindowData
open HLOZPositiveInterfacePhysicalWindowRatio
open HLOZPositiveInterfacePhysicalWindows
open HLOZProposition48Candidates
open LazyDecomposition ScreeningInstantiation
open SmallWindow
open TilingCappedMarginalization TilingConditionalCappedMarginalization
open TilingAwayNegativeBinomial
open TilingOrientedSupportAwayCoordinates
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Intersecting the physical upper source row with any additional base
screen can only reduce its mass.  This form accepts the exact raw adjacent
window comparison, so callers may establish it either by monotonicity or by
the local central-limit estimate. -/
theorem
    tilingAway_coordinateMass_physicalUpperInterBase_le_acceptedLower_of_windowRatio
    {retainedCount cap m width shell : ℕ} {C : ℝ}
    (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x retainedCount) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D) (base : Finset ℕ)
    (hiPos : 0 < Fintype.card (TilingCoordinatesAt t x r b.1))
    (hwindowRatio : windowMass
        (Fintype.card (TilingCoordinatesAt t x r b.1))
        (acceptedPhysicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1)) ≤
      C * windowMass
        (Fintype.card (TilingCoordinatesAt t x r b.1))
        (acceptedPhysicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t x r b.1)) shell))
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
            (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1) ∧
          (v : ℕ) ∈ base then
        coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
          upper b v else 0) ≤
      C *
        ∑ v : Fin (upper b),
          if (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t x r b.1)) shell then
            coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
              upper b v else 0 := by
  have hmono :
      (∑ v : Fin (upper b),
        if (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1) ∧
            (v : ℕ) ∈ base then
          coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
            upper b v else 0) ≤
        ∑ v : Fin (upper b),
          if (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1)
          then
            coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
              upper b v else 0 := by
    apply Finset.sum_le_sum
    intro v _hv
    by_cases hu : (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
        (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1)
    · by_cases hb : (v : ℕ) ∈ base
      · simp only [hu, hb, and_self, if_true]
        exact le_rfl
      · simp only [hu, hb, and_false, if_false]
        exact coordinateMass_nonneg_of_pointMass_nonneg _ _
          (fun b' ell ↦ tilingAwayExactTotalMass_nonneg t x r D b' ell) b v
    · simp only [hu, false_and, if_false, le_refl]
  exact hmono.trans (tilingAway_coordinateMass_window_ratio
    (cap := cap) t x r D upper b
      (acceptedPhysicalDeficitFailureWindow m width
        (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1))
      (acceptedPhysicalDeficitFailureWindow m width
        (Fintype.card (TilingCoordinatesAt t x r b.1)) shell)
      hupperUpper hlowerUpper hupperCap hlowerCap hiPos hwindowRatio)

/-- Monotone-side specialization of the exact-window adapter. -/
theorem tilingAway_coordinateMass_physicalUpperInterBase_le_acceptedLower
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
            (Fintype.card (TilingCoordinatesAt t x r b.1)) (shell + 1) ∧
          (v : ℕ) ∈ base then
        coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
          upper b v else 0) ≤
      (4 / 3 : ℝ) *
        ∑ v : Fin (upper b),
          if (v : ℕ) ∈ acceptedPhysicalDeficitFailureWindow m width
              (Fintype.card (TilingCoordinatesAt t x r b.1)) shell then
            coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
              upper b v else 0 := by
  apply
    tilingAway_coordinateMass_physicalUpperInterBase_le_acceptedLower_of_windowRatio
      t x r D upper b base hiPos
  · exact acceptedPhysicalAdjacentWindowMass_le_four_thirds_of_endpoint
      hiPos hwidth hfit hi hendpoint
  · exact hupperUpper
  · exact hlowerUpper
  · exact hupperCap
  · exact hlowerCap

/-- Concrete positive-interface specialization.  Source upper-row mass is
intersected with the prefix-correct accepted base, while the replacement row
is deliberately not intersected with it. -/
theorem positiveInterface_coordinateMass_physicalUpperInterBase_le_acceptedLower
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
  exact tilingAway_coordinateMass_physicalUpperInterBase_le_acceptedLower
    t (fiber.start cap) (fiber.retained cap) (fiber.distinguished cap)
      (fiber.upper cap) b (positiveInterfaceBaseWindow eta cap b)
      hiPos hwidth hfit hi hendpoint hupperUpper hlowerUpper
      hupperCap hlowerCap

end

end Erdos1165.HLOZPositiveInterfaceActualDeltaInterBaseRatio
