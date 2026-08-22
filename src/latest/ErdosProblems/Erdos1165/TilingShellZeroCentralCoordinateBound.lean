/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroSourcePartition
import ErdosProblems.Erdos1165.HLOZShellZeroCentralCount

/-! # Literal all-six fixed-central shell-zero coordinate bound -/

open scoped BigOperators

namespace Erdos1165.TilingShellZeroSourcePartition

open HLOZShellZeroCentralCount HLOZShellZeroReplacementWindows
open HLOZProposition48Candidates
open TilingLazyDecomposition TilingSpatialInsertionFiber
open TilingCappedMarginalization FiniteDominoProductLaw

noncomputable section

/-- Normalized `I₁` mass on one away domino.  The coordinate value is the
inserted lazy count; `card (TilingCoordinatesAt ...)` is the retained
external count at the base site, so the translated sum is the single-site
base local time used by `tilingVTwoAt`. -/
def tilingShellZeroSourceCoordinateMass
    {i cap m w : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D) : ℝ :=
  ∑ v : Fin (upper b),
    if (v : ℕ) ∈ shellZeroSourceFailureWindow m w
        (Fintype.card (TilingCoordinatesAt t x r b.1)) then
      coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
        upper b v
    else 0

/-- Normalized artificial `I₀` mass on one away domino. -/
def tilingShellZeroReplacementCoordinateMass
    {i cap m w : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D) : ℝ :=
  ∑ v : Fin (upper b),
    if (v : ℕ) ∈ shellZeroReplacementFailureWindow m w
        (Fintype.card (TilingCoordinatesAt t x r b.1)) then
      coordinateMass (tilingAwayPointMass (cap := cap) t x r D)
        upper b v
    else 0

theorem tilingShellZeroSourceCoordinateMass_nonneg
    {i cap m w : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D) :
    0 ≤ tilingShellZeroSourceCoordinateMass (cap := cap) (m := m)
      (w := w) t x r D upper b := by
  classical
  unfold tilingShellZeroSourceCoordinateMass
  apply Finset.sum_nonneg
  intro v _
  split
  · rw [coordinateMass, if_pos v.isLt]
    exact div_nonneg
      (tilingAwayExactTotalMass_nonneg t x r D b v)
      (Finset.sum_nonneg fun j _ ↦
        tilingAwayExactTotalMass_nonneg t x r D b j)
  · exact le_rfl

/-- The deterministic window facts needed on one stopped all-six fibre.
Bundling them prevents the literal fixed-count theorem below from exposing
an enormous dependent telescope, while retaining every source-window and
replacement-window requirement. -/
structure TilingShellZeroCoordinateWindowData
    {i cap m total : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) where
  card : Fintype.card (TilingAwayDomino t x r D) = total
  thick : ∀ b : TilingAwayDomino t x r D,
      m / 2 ≤ Fintype.card (TilingCoordinatesAt t x r b.1)
  translate : ∀ b : TilingAwayDomino t x r D,
      Fintype.card (TilingCoordinatesAt t x r b.1) ≤
        m - shellWidth48 m + 1
  center : ∀ b : TilingAwayDomino t x r D,
      |(m : ℝ) - (16 / 15 : ℝ) *
        (Fintype.card (TilingCoordinatesAt t x r b.1) : ℝ)| ≤
          shellZeroCenterRadius m
  sourceUpper : ∀ (b : TilingAwayDomino t x r D) (v : ℕ),
      v ∈ shellZeroSourceFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t x r b.1)) →
        v < upper b
  replacementUpper : ∀ (b : TilingAwayDomino t x r D) (v : ℕ),
      v ∈ shellZeroReplacementFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t x r b.1)) →
        v < upper b
  sourceCap : ∀ (b : TilingAwayDomino t x r D) (v : ℕ),
      v ∈ shellZeroSourceFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t x r b.1)) →
        v ≤ cap
  replacementCap : ∀ (b : TilingAwayDomino t x r D) (v : ℕ),
      v ∈ shellZeroReplacementFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t x r b.1)) →
        v ≤ cap

/-- Product mass of the exact all-`I₁` coordinate slice. -/
noncomputable def tilingShellZeroAllSourceProductMass
    {i cap m : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) : ℝ :=
  allUpperProductMass
    (tilingShellZeroSourceCoordinateMass (cap := cap) (m := m)
      (w := shellWidth48 m) t x r D upper)

/-- Product mass of the single central replacement slice. -/
noncomputable def tilingShellZeroCentralReplacementProductMass
    {i cap m : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (central : ℕ) : ℝ :=
  exactUpperCountProductMass
    (tilingShellZeroSourceCoordinateMass (cap := cap) (m := m)
      (w := shellWidth48 m) t x r D upper)
    (tilingShellZeroReplacementCoordinateMass (cap := cap) (m := m)
      (w := shellWidth48 m) t x r D upper) central

/-- Named proposition for the exact all-source to one-central-count
comparison.  Naming the proposition keeps downstream stopped-fibre
constructors from repeatedly unfolding the large dependent coordinate
types during elaboration. -/
def TilingShellZeroCentralProductBound
    {i cap m : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ) (total : ℕ) : Prop :=
  tilingShellZeroAllSourceProductMass (cap := cap) (m := m)
      t x r D upper ≤
    centralReplacementRatio shellZeroLocalRatioConstant total *
      tilingShellZeroCentralReplacementProductMass (cap := cap) (m := m)
        t x r D upper
        (centralReplacementUpperCount shellZeroLocalRatioConstant total)

/-- The literal one-coordinate `I₁`/`I₀` comparison, stated in the
named coordinate-mass language used by the central-count product theorem. -/
theorem tilingShellZeroSourceCoordinateMass_le
    {i cap m total : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : TilingShellZeroCoordinateWindowData
      (cap := cap) (m := m) (total := total) t x r D upper)
    (b : TilingAwayDomino t x r D) :
    tilingShellZeroSourceCoordinateMass (cap := cap) (m := m)
        (w := shellWidth48 m) t x r D upper b ≤
      shellZeroLocalRatioConstant *
        tilingShellZeroReplacementCoordinateMass (cap := cap) (m := m)
          (w := shellWidth48 m) t x r D upper b := by
  unfold tilingShellZeroSourceCoordinateMass
    tilingShellZeroReplacementCoordinateMass
  exact @tilingAway_coordinateMass_shellZeroSource_le i cap m t x r D upper b
    harithmetic (data.thick b) (data.translate b) (data.center b)
      (data.sourceUpper b) (data.replacementUpper b)
      (data.sourceCap b) (data.replacementCap b)

/-- The literal all-six fixed-central-count coordinate bound.  This is the
`coordinate_bound` input for one exact-`r` stopped replacement family. -/
theorem tilingAllSourceProductMass_le_centralReplacement
    {i cap m total : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (data : TilingShellZeroCoordinateWindowData
      (cap := cap) (m := m) (total := total) t x r D upper) :
    TilingShellZeroCentralProductBound (cap := cap) (m := m)
      t x r D upper total := by
  classical
  unfold TilingShellZeroCentralProductBound
    tilingShellZeroAllSourceProductMass
    tilingShellZeroCentralReplacementProductMass
  apply @allUpperProductMass_le_centralReplacementRatio_mul
    (TilingAwayDomino t x r D) inferInstance inferInstance
    (tilingShellZeroSourceCoordinateMass (cap := cap) (m := m)
      (w := shellWidth48 m) t x r D upper)
    (tilingShellZeroReplacementCoordinateMass (cap := cap) (m := m)
      (w := shellWidth48 m) t x r D upper)
    (fun b ↦ tilingShellZeroSourceCoordinateMass_nonneg t x r D upper b)
    shellZeroLocalRatioConstant
    shellZeroLocalRatioConstant_pos.le
    (r := total)
  · intro b
    exact tilingShellZeroSourceCoordinateMass_le t x r D upper harithmetic data b
  · exact data.card

end

end Erdos1165.TilingShellZeroSourcePartition
