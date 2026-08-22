/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalBaseWindow
import ErdosProblems.Erdos1165.HLOZPositiveInterfacePhysicalWindowRatio

/-!
# Boundary-crowding criterion for complete physical shell rows

The accepted physical shell `j` has positive deficit at least
`max 1 (j * width)`.  Hence its whole coordinate row remains inside the
prefix-correct base window whenever the excess of the larger fixed domino
endpoint boundary over the retained multiplicity is smaller than that
minimum deficit.  The same condition automatically contains the more distant
shell `j + 1`.
-/

namespace Erdos1165.HLOZPositiveInterfacePhysicalRowContainment

open HLOZPositiveInterfaceAggregateRecovery
open HLOZPositiveInterfacePhysicalWindowRatio
open LazyDecomposition
open TilingCappedMarginalization
open TilingOrientedSupportAwayCoordinates
open TilingPrefixedInsertedLocalTime
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- A fixed-boundary gap smaller than the minimum positive deficit of a
physical shell forces the complete accepted row into the honest base window. -/
theorem acceptedPhysicalDeficitFailureWindow_subset_baseWindow_of_boundary_lt
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap))
    (hwidth : 0 < width)
    (hboundary :
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta) b.1 <
        Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1) +
          max 1 (shell * width)) :
    acceptedPhysicalDeficitFailureWindow m width
        (Fintype.card (TilingCoordinatesAt t
          ((PositiveInterfaceFiber eta).start cap)
          ((PositiveInterfaceFiber eta).retained cap) b.1)) shell ⊆
      positiveInterfaceBaseWindow eta cap b := by
  intro v hv
  rw [mem_acceptedPhysicalDeficitFailureWindow] at hv
  unfold positiveInterfaceBaseWindow
  rw [Finset.mem_range]
  by_cases hshell : shell = 0
  · subst shell
    simp only [zero_mul, max_eq_left (Nat.zero_le 1)] at hboundary
    omega
  · have hshellPos : 0 < shell := Nat.pos_of_ne_zero hshell
    have hprodPos : 0 < shell * width := Nat.mul_pos hshellPos hwidth
    have hmax : max 1 (shell * width) = shell * width :=
      max_eq_right (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hprodPos))
    rw [hmax] at hboundary
    have hdeficit : shell * width ≤ m -
        (Fintype.card (TilingCoordinatesAt t
          ((PositiveInterfaceFiber eta).start cap)
          ((PositiveInterfaceFiber eta).retained cap) b.1) + v) := by
      rw [← Nat.le_div_iff_mul_le hwidth, hv.2]
    omega

/-- One boundary-crowding inequality contains both adjacent accepted rows. -/
theorem acceptedPhysicalAdjacentFailureWindows_subset_baseWindow_of_boundary_lt
    {t : DominoTiling} {o : Orientation}
    {m k externalThreshold width shell : ℕ}
    (eta : PositiveInterfaceSupportedIndex t o m k externalThreshold)
    (cap : ℕ)
    (b : TilingAwayDomino t ((PositiveInterfaceFiber eta).start cap)
      ((PositiveInterfaceFiber eta).retained cap)
      ((PositiveInterfaceFiber eta).distinguished cap))
    (hwidth : 0 < width)
    (hboundary :
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta) b.1 <
        Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1) +
          max 1 (shell * width)) :
    acceptedPhysicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1)) (shell + 1) ⊆
        positiveInterfaceBaseWindow eta cap b ∧
      acceptedPhysicalDeficitFailureWindow m width
          (Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1)) shell ⊆
        positiveInterfaceBaseWindow eta cap b := by
  have hmul : shell * width ≤ (shell + 1) * width := by
    exact Nat.mul_le_mul_right width (Nat.le_succ shell)
  have hmax : max 1 (shell * width) ≤ max 1 ((shell + 1) * width) :=
    max_le_max le_rfl hmul
  have hboundaryUpper :
      prefixedTilingFixedBoundaryDominoMax eta.1.1.external.initial.1
          eta.1.1.external.start eta.1.1.external.retained
          (positiveInterfaceTerminal eta) b.1 <
        Fintype.card (TilingCoordinatesAt t
            ((PositiveInterfaceFiber eta).start cap)
            ((PositiveInterfaceFiber eta).retained cap) b.1) +
          max 1 ((shell + 1) * width) :=
    hboundary.trans_le (Nat.add_le_add_left hmax _)
  exact ⟨
    acceptedPhysicalDeficitFailureWindow_subset_baseWindow_of_boundary_lt
      eta cap b hwidth hboundaryUpper,
    acceptedPhysicalDeficitFailureWindow_subset_baseWindow_of_boundary_lt
      eta cap b hwidth hboundary⟩

end

end Erdos1165.HLOZPositiveInterfacePhysicalRowContainment
