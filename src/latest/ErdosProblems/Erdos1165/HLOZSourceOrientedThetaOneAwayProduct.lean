/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaExternalProduct

/-!
# One-away-coordinate product bound for Proposition 4.5

For a selected represented base `b`, every other represented domino remains
in the distinguished carrier.  Thus the away coordinate set is obtained by
taking `D = represented \ {b}` and is literally the singleton `b`.  This is
the source-correct atomwise split: it neither truncates nor sums the other
insertion coordinates.

The final theorem below is carrier weighted.  It bounds the normalized
one-coordinate Theta screen by the checked one-site cost and then multiplies
by an arbitrary nonnegative distinguished carrier.  No path probability or
conditional-independence premise occurs in this finite-product layer.
-/

open scoped BigOperators

namespace Erdos1165.HLOZSourceOrientedThetaOneAwayProduct

open FiniteDominoProductLaw HLOZFiniteProductCoordinateUnion
open HLOZAllSixExactCoordinateProductClosure HLOZNegativeBinomialTruncation
open HLOZSourceOrientedThetaBalance HLOZSourceOrientedThetaProduct
open HLOZShellZeroExternalWindow
open TilingCappedMarginalization TilingSpatialInsertionFiber
open ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- All represented bases except the selected Theta base remain
distinguished. -/
def oneAwayDistinguished {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : Point) : Finset Point :=
  (tilingExternalDominoBases t x r).erase b

/-- The selected represented base as the unique away domino. -/
def oneAwayChosen {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t x r) :
    TilingAwayDomino t x r (oneAwayDistinguished t x r b) :=
  ⟨⟨b, hb⟩, by simp [oneAwayDistinguished]⟩

@[simp] theorem oneAwayChosen_base {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t x r) :
    (oneAwayChosen t x r b hb).1.1 = b := rfl

/-- There is no hidden second away coordinate in the one-site split. -/
theorem oneAwayDomino_eq_chosen {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t x r)
    (c : TilingAwayDomino t x r (oneAwayDistinguished t x r b)) :
    c = oneAwayChosen t x r b hb := by
  apply Subtype.ext
  apply Subtype.ext
  have hc : c.1.1 = b := by
    have hmem := c.2
    simp only [oneAwayDistinguished, Finset.mem_erase, not_and_or,
      not_not] at hmem
    rcases hmem with hcb | hnot
    · exact hcb
    · exact (hnot c.1.2).elim
  exact hc

theorem oneAwayDomino_card {i : ℕ} (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x i) (b : Point)
    (hb : b ∈ tilingExternalDominoBases t x r) :
    Fintype.card
      (TilingAwayDomino t x r (oneAwayDistinguished t x r b)) = 1 := by
  classical
  rw [Fintype.card_eq_one_iff]
  exact ⟨oneAwayChosen t x r b hb, oneAwayDomino_eq_chosen t x r b hb⟩

/-- Literal support and scale assumptions for the selected coordinate.  All
fields refer to checked finite negative-binomial point masses. -/
structure OneAwayThetaArithmetic {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (b : Point) (hb : b ∈ tilingExternalDominoBases t x r)
    (m w externalLow externalHigh : ℕ)
    (upper : TilingAwayDomino t x r
      (oneAwayDistinguished t x r b) → ℕ) : Prop where
  level_pos : 0 < m
  width : (w : ℝ) ≤ (m : ℝ) / 10
  width_eq : w = HLOZProposition48Candidates.shellWidth48 m
  externalLow_eq : externalLow = shellZeroExternalLow48 m
  externalHigh_eq : externalHigh = shellZeroExternalHigh48 m
  geometric : geometricDeviation m ≤ m + w
  theta : thetaLowDeviation m ≤ m + w
  thick_nonneg : 0 ≤ ExternalProposition44.hlozThickThresholdReal44 m
  low_dom : (w : ℝ) + thetaLowDeviation m ≤
    (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ)
  upper_pos : ∀ c : TilingAwayDomino t x r
    (oneAwayDistinguished t x r b), 0 < upper c
  upper_le_cap : ∀ c : TilingAwayDomino t x r
    (oneAwayDistinguished t x r b), upper c ≤ cap + 1
  mean : ∀ c : TilingAwayDomino t x r
    (oneAwayDistinguished t x r b),
    2 * Fintype.card (TilingCoordinatesAt t x r c.1) ≤
    15 * upper c
  window_upper : ∀ c : TilingAwayDomino t x r
    (oneAwayDistinguished t x r b), ∀ v,
    v ∈ thetaFailureWindow m w
      (Fintype.card (TilingCoordinatesAt t x r c.1)) →
    v < upper c
  window_cap : ∀ c : TilingAwayDomino t x r
    (oneAwayDistinguished t x r b), ∀ v,
    v ∈ thetaFailureWindow m w
      (Fintype.card (TilingCoordinatesAt t x r c.1)) →
    v ≤ cap

/-- The normalized product screen testing only the chosen away coordinate. -/
noncomputable def oneAwayThetaScreenMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (b : Point) (hb : b ∈ tilingExternalDominoBases t x r)
    (m w externalLow externalHigh : ℕ)
    (upper : TilingAwayDomino t x r
      (oneAwayDistinguished t x r b) → ℕ) : ℝ :=
  screenMass
    (tilingAwayPointMass (cap := cap) t x r
      (oneAwayDistinguished t x r b)) upper
    (fun ell ↦ thetaCoordinateBad m w externalLow externalHigh
      (Fintype.card (TilingCoordinatesAt t x r
        (oneAwayChosen t x r b hb).1))
      (ell (oneAwayChosen t x r b hb)))

/-- The checked one-site cost of the selected retained multiplicity. -/
noncomputable def oneAwayThetaCost {i : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (b : Point) (hb : b ∈ tilingExternalDominoBases t x r) (m : ℕ) : ℝ :=
  thetaCoordinateCost m
    (Fintype.card (TilingCoordinatesAt t x r ⟨b, hb⟩))

/-- The normalized one-away screen costs at most twice the literal one-site
negative-binomial tail. -/
theorem oneAwayThetaScreenMass_le {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (b : Point) (hb : b ∈ tilingExternalDominoBases t x r)
    (m w externalLow externalHigh : ℕ)
    (upper : TilingAwayDomino t x r
      (oneAwayDistinguished t x r b) → ℕ)
    (arith : OneAwayThetaArithmetic (cap := cap) t x r b hb m w externalLow
      externalHigh upper) :
    oneAwayThetaScreenMass (cap := cap) t x r b hb m w externalLow
        externalHigh upper ≤
      2 * oneAwayThetaCost t x r b hb m := by
  classical
  let D := oneAwayDistinguished t x r b
  let chosen := oneAwayChosen t x r b hb
  let pointMass := tilingAwayPointMass (cap := cap) t x r D
  let bad := fun c (v : Fin (upper c)) ↦
    thetaCoordinateBad m w externalLow externalHigh
      (Fintype.card (TilingCoordinatesAt t x r c.1)) v
  let cost := fun c : TilingAwayDomino t x r D ↦
    thetaCoordinateCost m
      (Fintype.card (TilingCoordinatesAt t x r c.1))
  have hpoint : ∀ c v, 0 ≤ pointMass c v := by
    intro c v
    exact tilingAwayExactTotalMass_nonneg t x r D c v
  have hsum : ∀ c, (∑ v : Fin (upper c),
      coordinateMass pointMass upper c v) = 1 := by
    intro c
    exact sum_coordinateMass_eq_one_of_zero_pos pointMass upper hpoint
      arith.upper_pos
      (fun d ↦ tilingAwayExactTotalMass_zero_pos t x r D d) c
  have hden : ∀ c, (1 / 2 : ℝ) ≤
      ∑ v : Fin (upper c), pointMass c v := by
    intro c
    exact half_le_sum_tilingAwayPointMass t x r D c (upper c)
      (arith.upper_pos c) (arith.upper_le_cap c)
      (card_tilingCoordinatesAt_pos t x r c.1) (arith.mean c)
  have hbad : ∀ c, (∑ v : Fin (upper c),
      if bad c v then pointMass c v else 0) ≤ cost c := by
    intro c
    exact sum_thetaCoordinateBad_tilingAwayPointMass_le t x r D c
      arith.level_pos arith.width arith.width_eq arith.externalLow_eq
      arith.externalHigh_eq arith.geometric arith.theta arith.thick_nonneg
      arith.low_dom (arith.window_upper c) (arith.window_cap c)
  have hsingle := sum_bad_coordinateMass_le_two_mul pointMass upper bad cost
    hpoint hden hbad chosen
  have heq : oneAwayThetaScreenMass (cap := cap) t x r b hb m w externalLow
      externalHigh upper = ∑ v : Fin (upper chosen),
        if bad chosen v then coordinateMass pointMass upper chosen v else 0 := by
    unfold oneAwayThetaScreenMass
    exact screenMass_single_coordinate_eq pointMass upper bad hsum chosen
  rw [heq]
  have hcost : cost chosen = oneAwayThetaCost t x r b hb m := by
    rfl
  simpa only [hcost] using hsingle

/-- Carrier-weighted form used by the countable retained-trace summation. -/
theorem oneAwayThetaScreenMass_mul_carrier_le {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (b : Point) (hb : b ∈ tilingExternalDominoBases t x r)
    (m w externalLow externalHigh : ℕ)
    (upper : TilingAwayDomino t x r
      (oneAwayDistinguished t x r b) → ℕ)
    (arith : OneAwayThetaArithmetic (cap := cap) t x r b hb m w externalLow
      externalHigh upper) (carrier : ℝ) (hcarrier : 0 ≤ carrier) :
    oneAwayThetaScreenMass (cap := cap) t x r b hb m w externalLow
        externalHigh upper *
        carrier ≤
      (2 * oneAwayThetaCost t x r b hb m) * carrier := by
  exact mul_le_mul_of_nonneg_right
    (oneAwayThetaScreenMass_le (cap := cap) t x r b hb m w externalLow
      externalHigh upper arith) hcarrier

end

end Erdos1165.HLOZSourceOrientedThetaOneAwayProduct
