/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerLemma2Concrete

/-!
# The initial source matrix has the required exponential height

This file collects the four source-faithful entry estimates proved in
`BakerLemma2Concrete`.  The common derivative-order factor uses `15/8` of
the height exponent, while the powered-Delta side, the ordinary-Delta side,
and the prime monomial each use `1/32`.  Their sum is `63/32 < 2`, giving the
literal matrix bound printed in the source.
-/

noncomputable section

open scoped BigOperators

namespace Erdos240.BakerInitialMatrixHeight

open Erdos240
open Erdos240.BakerLemma2Concrete

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The complete source-faithful natural-number majorant fits in the printed
`exp (2 H)` matrix-height allowance. -/
theorem initialSourceMatrixMajorantNat_le_exp_two_height {oldRank : ℕ}
    [Nonempty (Fin oldRank)] (P : VDPLParameters (Fin oldRank)) :
    (initialSourceMatrixMajorantNat P : ℝ) ≤
      Real.exp (2 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld)) := by
  let H : ℝ := (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld
  have hcommon :
      (((max (4 ^ P.h) (2 * P.Bsrc)) ^ initialBudget P : ℕ) : ℝ) ≤
        Real.exp ((15 / 8 : ℝ) * H) := by
    simpa only [H] using initial_commonDerivativeFactor_le P
  have hhead :
      ((4 ^ ((P.Lzero + 1) * (18 * P.h)) : ℕ) : ℝ) ≤
        Real.exp ((1 / 32 : ℝ) * H) := by
    simpa only [H] using initial_headSideFactor_le P
  have hold :
      ((2 ^ (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero)) : ℕ) : ℝ) ≤
        Real.exp ((1 / 32 : ℝ) * H) := by
    simpa only [H] using initial_oldDeltaSideFactor_le P
  have hmono : (initialMonomialMajorantNat P : ℝ) ≤
      Real.exp ((1 / 32 : ℝ) * H) := by
    simpa only [H] using initial_monomialMajorant_le P
  norm_num only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul] at hcommon hhead hold
  have hproduct :
      ((((max (4 ^ P.h) (2 * P.Bsrc) : ℕ) : ℝ) ^ initialBudget P *
          (4 : ℝ) ^ ((P.Lzero + 1) * (18 * P.h))) *
          (2 : ℝ) ^
            (∑ r : Fin oldRank, (P.LiZero r + P.LlastZero))) *
          (initialMonomialMajorantNat P : ℝ) ≤
        ((Real.exp ((15 / 8 : ℝ) * H) *
          Real.exp ((1 / 32 : ℝ) * H)) *
          Real.exp ((1 / 32 : ℝ) * H)) *
          Real.exp ((1 / 32 : ℝ) * H) := by
    have h12 := mul_le_mul hcommon hhead (by positivity) (by positivity)
    have h123 := mul_le_mul h12 hold (by positivity) (by positivity)
    exact mul_le_mul h123 hmono (by positivity) (by positivity)
  unfold initialSourceMatrixMajorantNat
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  refine hproduct.trans ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp only [H]
  have hH : 0 ≤
      (P.h : ℝ) * P.k * P.Omega * Real.log P.OmegaOld := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) P.k_pos.le) P.Omega_pos.le)
      P.log_OmegaOld_pos.le
  nlinarith

/-- The actual integral constraint matrix, not merely its entry majorant,
fits in the printed `exp (2 H)` allowance. -/
theorem norm_initialIntegralConstraintModel_le_exp_two_height
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc) :
    ‖(BakerLemma2Concrete.initialIntegralConstraintModel P b bLast
        (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)).matrix‖ ≤
      Real.exp (2 * ((P.h : ℝ) * P.k * P.Omega *
        Real.log P.OmegaOld)) := by
  exact (norm_initialIntegralConstraintModel_le_sourceMajorant
    P b bLast hb hbLast).trans
      (initialSourceMatrixMajorantNat_le_exp_two_height P)

/-- Source Lemma 2 with the matrix-height hypothesis discharged from the
coefficient bounds.  Only the two finite-ledger membership facts used by
the dimension and column counts remain as inputs. -/
theorem exists_initial_levelState_vanishes_sourceHeight_of_bounds
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hb : ∀ r, (b r).natAbs ≤ P.Bsrc)
    (hbLast : bLast.natAbs ≤ P.Bsrc)
    (hdim : initialDimensionRequirement P ∈ P.kRequirements)
    (hunknownReq : initialUnknownRequirement P ∈ P.kRequirements) :
    ∃ state : Erdos240.BakerSourceState.LevelState P 0,
      Erdos240.VanishesOn
        (Erdos240.BakerSourceState.g state b bLast)
        1 (initialRadius P) (initialBudget P) := by
  exact exists_initial_levelState_vanishes_sourceHeight P b bLast
    hdim hunknownReq
    (norm_initialIntegralConstraintModel_le_exp_two_height
      P b bLast hb hbLast)

end Erdos240.BakerInitialMatrixHeight

#print axioms Erdos240.BakerInitialMatrixHeight.initialSourceMatrixMajorantNat_le_exp_two_height
#print axioms Erdos240.BakerInitialMatrixHeight.norm_initialIntegralConstraintModel_le_exp_two_height
#print axioms Erdos240.BakerInitialMatrixHeight.exists_initial_levelState_vanishes_sourceHeight_of_bounds
