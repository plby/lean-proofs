/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.TilingShellZeroEndpointIncrementScreen
import ErdosProblems.Erdos1165.TilingPrefixedRaisedRankAcceptedCreation

/-!
# Cardinal meaning of the shell-zero endpoint increment

This file identifies the numerical product-screen increment with the actual
number of thresholded endpoints among the represented away dominoes.  The
two endpoint images are injective and disjoint because the tiling partner is
a fixed-point-free involution and every represented domino is stored by its
canonical base.
-/

open scoped BigOperators

namespace Erdos1165.TilingShellZeroEndpointIncrementCard

open FiniteDominoProductLaw HLOZShellZeroEndpointIncrementPartition
open LazyDecomposition TilingCappedMarginalization
open TilingLazyDecomposition TilingPrefixedInsertedLocalTime
open TilingShellZeroEndpointIncrementScreen TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The away endpoints that are at level `m` after inserting totals `ell`. -/
def prefixedShellZeroThresholdedAwayEndpoints
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m : ℕ) (ell : TruncatedTotals upper) : Finset Point :=
  ((Finset.univ.filter fun b : TilingAwayDomino t x r D ↦
      m ≤ prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 +
        (ell b : ℕ)).image fun b ↦ b.1.1) ∪
    ((Finset.univ.filter fun b : TilingAwayDomino t x r D ↦
      m ≤ prefixedTilingFixedBoundaryLocalTime initial x r terminal
        (tilingPartner t b.1.1) + (ell b : ℕ)).image fun b ↦
          tilingPartner t b.1.1)

private theorem awayBase_injective
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) :
    Function.Injective (fun b : TilingAwayDomino t x r D ↦ b.1.1) := by
  intro b c h
  apply Subtype.ext
  apply Subtype.ext
  exact h

private theorem awayPartner_injective
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) :
    Function.Injective
      (fun b : TilingAwayDomino t x r D ↦ tilingPartner t b.1.1) := by
  intro b c h
  apply awayBase_injective t x r D
  simpa only [tilingPartner_partner] using congrArg (tilingPartner t) h

private theorem awayBaseImage_disjoint_awayPartnerImage
    {i : ℕ} (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (D : Finset Point) (A B : Finset (TilingAwayDomino t x r D)) :
    Disjoint (A.image fun b ↦ b.1.1)
      (B.image fun b ↦ tilingPartner t b.1.1) := by
  rw [Finset.disjoint_left]
  intro y hyA hyB
  rcases Finset.mem_image.mp hyA with ⟨a, _, ha⟩
  rcases Finset.mem_image.mp hyB with ⟨b, _, hb⟩
  have hbase := congrArg (tilingBase t) (ha.trans hb.symm)
  rw [tilingExternalDomino_is_base t x r a.1,
    tilingPartner_ofExternalDomino_has_base t x r b.1] at hbase
  have hab : a.1.1 = b.1.1 := hbase
  have hfixed : b.1.1 = tilingPartner t b.1.1 := by
    exact hab.symm.trans (ha.trans hb.symm)
  exact (tilingPartner_ne t b.1.1) hfixed.symm

/-- The endpoint Finset has exactly the cardinal prescribed by the numerical
endpoint-increment sum. -/
theorem card_prefixedShellZeroThresholdedAwayEndpoints
    (initial : List Direction) {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (terminal : Option Point)
    (D : Finset Point) (upper : TilingAwayDomino t x r D → ℕ)
    (m : ℕ) (ell : TruncatedTotals upper) :
    (prefixedShellZeroThresholdedAwayEndpoints initial t x r terminal D
      upper m ell).card =
      endpointIncrementOfVector
        (prefixedShellZeroEndpointContribution initial t x r terminal D
          upper m) ell := by
  let A := Finset.univ.filter fun b : TilingAwayDomino t x r D ↦
    m ≤ prefixedTilingFixedBoundaryLocalTime initial x r terminal b.1.1 +
      (ell b : ℕ)
  let B := Finset.univ.filter fun b : TilingAwayDomino t x r D ↦
    m ≤ prefixedTilingFixedBoundaryLocalTime initial x r terminal
      (tilingPartner t b.1.1) + (ell b : ℕ)
  have hdisj : Disjoint (A.image fun b ↦ b.1.1)
      (B.image fun b ↦ tilingPartner t b.1.1) :=
    awayBaseImage_disjoint_awayPartnerImage t x r D A B
  rw [show prefixedShellZeroThresholdedAwayEndpoints initial t x r terminal D
      upper m ell = (A.image fun b ↦ b.1.1) ∪
        (B.image fun b ↦ tilingPartner t b.1.1) by rfl,
    Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective A (awayBase_injective t x r D),
    Finset.card_image_of_injective B (awayPartner_injective t x r D)]
  unfold endpointIncrementOfVector prefixedShellZeroEndpointContribution
  simp only [Finset.sum_add_distrib]
  change A.card + B.card = _
  simp [A, B]

end

end Erdos1165.TilingShellZeroEndpointIncrementCard
