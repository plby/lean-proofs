/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaOneAwayProduct

/-!
# Rank-stable source-window part of the one-away Theta product

Only HLOZ's below-level strip `I₁` is stable at the rank-`k` creation
clock.  The above-level comparison strip `I₀` belongs to the separate
actual-rank-increment replacement argument.  This file records the literal
one-coordinate `I₁` screen and bounds it by the already checked union-window
Theta cost.
-/

open scoped BigOperators

namespace Erdos1165.HLOZSourceOrientedThetaSourceWindowProduct

open FiniteDominoProductLaw HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaOneAwayProduct HLOZSourceOrientedThetaProduct
open HLOZShellZeroReplacementWindows
open TilingCappedMarginalization TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def sourceThetaCoordinateBad
    (m w externalLow externalHigh i v : ℕ) : Prop :=
  v ∈ shellZeroSourceFailureWindow m w i ∧
    ¬(externalLow ≤ i ∧ i < externalHigh)

instance (m w externalLow externalHigh i : ℕ) :
    DecidablePred (sourceThetaCoordinateBad m w externalLow externalHigh i) :=
  Classical.decPred _

theorem sourceThetaCoordinateBad_subset_thetaCoordinateBad
    {m w externalLow externalHigh i v : ℕ}
    (h : sourceThetaCoordinateBad m w externalLow externalHigh i v) :
    thetaCoordinateBad m w externalLow externalHigh i v := by
  refine ⟨?_, h.2⟩
  rw [thetaFailureWindow, Finset.mem_union]
  exact Or.inl h.1

noncomputable def oneAwaySourceThetaScreenMass {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (b : Point) (hb : b ∈ tilingExternalDominoBases t x r)
    (m w externalLow externalHigh : ℕ)
    (upper : TilingAwayDomino t x r
      (oneAwayDistinguished t x r b) → ℕ) : ℝ :=
  screenMass
    (tilingAwayPointMass (cap := cap) t x r
      (oneAwayDistinguished t x r b)) upper
    (fun ell ↦ sourceThetaCoordinateBad m w externalLow externalHigh
      (Fintype.card (TilingCoordinatesAt t x r
        (oneAwayChosen t x r b hb).1))
      (ell (oneAwayChosen t x r b hb)))

private theorem screenMass_mono
    {Domino : Type*} [Fintype Domino] [DecidableEq Domino]
    (pointMass : Domino → ℕ → ℝ) (upper : Domino → ℕ)
    (small large : TruncatedTotals upper → Prop)
    (hpoint : ∀ b v, 0 ≤ pointMass b v)
    (hsub : ∀ ell, small ell → large ell) :
    @screenMass Domino _ _ pointMass upper small (Classical.decPred _) ≤
      @screenMass Domino _ _ pointMass upper large (Classical.decPred _) := by
  unfold screenMass
  apply Finset.sum_le_sum
  intro ell _hell
  by_cases hs : small ell
  · rw [if_pos hs, if_pos (hsub ell hs)]
  · rw [if_neg hs]
    by_cases hl : large ell
    · rw [if_pos hl]
      exact HLOZFiniteProductCoordinateUnion.normalizedJointMass_nonneg_of_pointMass_nonneg
        pointMass upper hpoint ell
    · rw [if_neg hl]

theorem oneAwaySourceThetaScreenMass_le {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (b : Point) (hb : b ∈ tilingExternalDominoBases t x r)
    (m w externalLow externalHigh : ℕ)
    (upper : TilingAwayDomino t x r
      (oneAwayDistinguished t x r b) → ℕ)
    (arith : OneAwayThetaArithmetic (cap := cap) t x r b hb m w externalLow
      externalHigh upper) :
    oneAwaySourceThetaScreenMass (cap := cap) t x r b hb m w externalLow
        externalHigh upper ≤
      2 * oneAwayThetaCost t x r b hb m := by
  classical
  calc
    oneAwaySourceThetaScreenMass (cap := cap) t x r b hb m w externalLow
        externalHigh upper ≤
      oneAwayThetaScreenMass (cap := cap) t x r b hb m w externalLow
        externalHigh upper := by
          apply screenMass_mono
          · intro c v
            exact tilingAwayExactTotalMass_nonneg t x r
              (oneAwayDistinguished t x r b) c v
          · intro ell hell
            exact sourceThetaCoordinateBad_subset_thetaCoordinateBad hell
    _ ≤ 2 * oneAwayThetaCost t x r b hb m :=
      oneAwayThetaScreenMass_le (cap := cap) t x r b hb m w externalLow
        externalHigh upper arith

theorem oneAwaySourceThetaScreenMass_mul_carrier_le {i cap : ℕ}
    (t : DominoTiling) (x : Point) (r : TilingRetainedWord t x i)
    (b : Point) (hb : b ∈ tilingExternalDominoBases t x r)
    (m w externalLow externalHigh : ℕ)
    (upper : TilingAwayDomino t x r
      (oneAwayDistinguished t x r b) → ℕ)
    (arith : OneAwayThetaArithmetic (cap := cap) t x r b hb m w externalLow
      externalHigh upper) (carrier : ℝ) (hcarrier : 0 ≤ carrier) :
    oneAwaySourceThetaScreenMass (cap := cap) t x r b hb m w externalLow
        externalHigh upper * carrier ≤
      (2 * oneAwayThetaCost t x r b hb m) * carrier := by
  exact mul_le_mul_of_nonneg_right
    (oneAwaySourceThetaScreenMass_le (cap := cap) t x r b hb m w
      externalLow externalHigh upper arith) hcarrier

end

end Erdos1165.HLOZSourceOrientedThetaSourceWindowProduct
