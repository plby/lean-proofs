/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZPrefixedTilingConditionalCoordinateReconstruction
import ErdosProblems.Erdos1165.HLOZShellZeroEndpointIncrementPartition

/-!
# Actual endpoint increment on a prefixed tiling product screen

The increment is computed from the physical-prefix fixed boundary local
times plus the inserted domino total.  Source-window coordinates contribute
zero under the source dominance law; every coordinate contributes at most
two.
-/

open scoped BigOperators

namespace Erdos1165.TilingShellZeroEndpointIncrementScreen

open FiniteDominoProductLaw
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open HLOZShellZeroEndpointIncrementPartition
open HLOZShellZeroReplacementWindows
open LazyDecomposition TilingLazyDecomposition
open TilingShellZeroActualDeltaPartition
open TilingCappedMarginalization TilingPrefixedInsertedLocalTime
open TilingShellZeroFactoredCapScreen TilingShellZeroSourcePartition
open TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- Number of newly thresholded endpoints contributed by one away domino. -/
def prefixedShellZeroEndpointContribution
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m : ℕ) (b : TilingAwayDomino t x r D) (v : Fin (upper b)) : ℕ :=
  (if m ≤ prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 + v
    then 1 else 0) +
  (if m ≤ prefixedTilingFixedBoundaryLocalTime initial x r terminal
      (tilingPartner t b.1.1) + v then 1 else 0)

theorem prefixedShellZeroEndpointContribution_le_two
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m : ℕ) (b : TilingAwayDomino t x r D) (v : Fin (upper b)) :
    prefixedShellZeroEndpointContribution initial t x r terminal D upper
      m b v ≤ 2 := by
  unfold prefixedShellZeroEndpointContribution
  split_ifs <;> omega

/-- A source-window coordinate creates no new threshold endpoint.  The
base boundary count is the retained-coordinate multiplicity and the source
dominance law puts the partner boundary below it. -/
theorem prefixedShellZeroEndpointContribution_eq_zero_of_source
    (initial : List Direction) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (hbase : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial x r terminal
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1)
    (b : TilingAwayDomino t x r D) (v : Fin (upper b))
    (hv : tilingShellZeroSourceCoordinate (cap := cap) (m := m) (w := w)
      t x r D upper b v) :
    prefixedShellZeroEndpointContribution initial t x r terminal D upper
      m b v = 0 := by
  have hsource : Fintype.card (TilingCoordinatesAt t x r b.1) + (v : ℕ) < m := by
    simp only [tilingShellZeroSourceCoordinate,
      mem_shellZeroSourceFailureWindow, mem_shellZeroSourceTotalWindow] at hv
    omega
  have hbaseLt : prefixedTilingFixedBoundaryLocalTime initial x r terminal
      b.1.1 + (v : ℕ) < m := by
    rw [hbase b]
    exact hsource
  have hpartnerLt : prefixedTilingFixedBoundaryLocalTime initial x r terminal
      (tilingPartner t b.1.1) + (v : ℕ) < m := by
    exact lt_of_le_of_lt
      (Nat.add_le_add_right (hdominance b) (v : ℕ)) hbaseLt
  unfold prefixedShellZeroEndpointContribution
  rw [if_neg (Nat.not_le.mpr hbaseLt),
    if_neg (Nat.not_le.mpr hpartnerLt)]

/-- The exact-central product screen refined by the actual endpoint count. -/
def prefixedShellZeroReplacementScreenAtIncrement
    (initial : List Direction) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (central delta : ℕ) (ell : TruncatedTotals upper) : Prop :=
  exactSourceSubsetVectorAtIncrement
    (fun b v ↦ tilingShellZeroSourceCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b v)
    (fun b v ↦ tilingShellZeroReplacementCoordinate
      (cap := cap) (m := m) (w := w) t x r D upper b v)
    (prefixedShellZeroEndpointContribution initial t x r terminal D upper m)
    central delta ell

/-- Exact finite-product partition of the fixed-central replacement screen
by the actual endpoint increment. -/
theorem sum_screenMass_prefixedShellZeroReplacementScreenAtIncrement_eq
    (initial : List Direction) {i cap m w : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (terminal : Option Point) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (central : ℕ)
    (hbase : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 =
        Fintype.card (TilingCoordinatesAt t x r b.1))
    (hdominance : ∀ b : TilingAwayDomino t x r D,
      prefixedTilingFixedBoundaryLocalTime initial x r terminal
          (tilingPartner t b.1.1) ≤
        prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1) :
    (∑ delta : ReplacementEndpointIncrement
        (Fintype.card (TilingAwayDomino t x r D)) central,
      @screenMass (TilingAwayDomino t x r D) inferInstance inferInstance
        (tilingAwayPointMass (cap := cap) t x r D) upper
        (prefixedShellZeroReplacementScreenAtIncrement
          (cap := cap) (m := m) (w := w) initial t x r terminal
          D upper central delta)
        (Classical.decPred _)) =
      @screenMass (TilingAwayDomino t x r D) inferInstance inferInstance
        (tilingAwayPointMass (cap := cap) t x r D) upper
        (exactSourceSubsetVector
          (fun b v ↦ tilingShellZeroSourceCoordinate
            (cap := cap) (m := m) (w := w) t x r D upper b v)
          (fun b v ↦ tilingShellZeroReplacementCoordinate
            (cap := cap) (m := m) (w := w) t x r D upper b v)
          central)
        (Classical.decPred _) := by
  apply sum_screenMass_exactSourceSubsetVectorAtIncrement_eq
  · intro b v hv
    exact prefixedShellZeroEndpointContribution_eq_zero_of_source
      initial t x r terminal D upper hbase hdominance b v hv
  · exact prefixedShellZeroEndpointContribution_le_two
      initial t x r terminal D upper m

end

end Erdos1165.TilingShellZeroEndpointIncrementScreen
