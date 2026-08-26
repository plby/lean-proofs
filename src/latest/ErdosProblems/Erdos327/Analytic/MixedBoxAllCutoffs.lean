import ErdosProblems.Erdos327.Analytic.MixedBoxAssembly
import ErdosProblems.Erdos327.Analytic.ThreeFormBoxAllCutoffs

/-!
# Mixed dyadic assembly in both sieve-cutoff orderings

This module removes the artificial ordering hypothesis `L ≤ z` from the
one-block mixed-coordinate estimate.
-/

namespace Erdos327.Analytic

open Finset Real

noncomputable section

/-- Sharp mixed sieve factor with the piecewise Euler-product envelope. -/
def mixedAllCutoffSharpBoxBound
    (L z X R : ℕ) (qb qo : ℝ) : ℝ :=
  8 * (X : ℝ) ^ 2 *
      exp (mixedAllCutoffMertensEnvelope L z
        (1 / qb) (1 / qo) (1 / (qb * qo))) +
    8 * (X : ℝ) ^ 2 *
      ((3 * primeInvSum z) ^ (2 * R + 1) /
        ((2 * R + 1).factorial : ℝ)) +
    ((2 * R + 1 : ℕ) : ℝ) *
      (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
      (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))

/-- Fully explicit mixed-coordinate estimate valid whether `z < L` or
`L ≤ z`. -/
theorem card_mixedCoordinateBoxBlock_le_allCutoffs_explicit
    {L N z X R : ℕ} {Ab Kb Ao Ko qb qo : ℝ}
    (hL : 3 ≤ L) (hLX : L ≤ X) (hz : 2 ≤ z) (hzX : z ≤ X)
    (hY : L ≤ N / (X * X))
    (hqb : 1 < qb) (hqo : 1 < qo)
    (hM : 0 ≤ Ab * log qb + Ao * log qo) :
    ((mixedCoordinateBoxBlock
        L N Ab Kb Ao Ko X).card : ℝ) ≤
      mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
        mixedAllCutoffSharpBoxBound L z X R qb qo *
        mixedBlockResidualBound L N X qb qo := by
  let alpha : ℝ := 1 / qb
  let beta : ℝ := 1 / qo
  let s : ℝ := 1 / (qb * qo)
  let Y : ℕ := N / (X * X)
  have hqb0 : 0 < qb := zero_lt_one.trans hqb
  have hqo0 : 0 < qo := zero_lt_one.trans hqo
  have hprod0 : 0 < qb * qo := mul_pos hqb0 hqo0
  have hprodOne : 1 ≤ qb * qo := by
    nlinarith [mul_pos (sub_pos.mpr hqb) (sub_pos.mpr hqo)]
  have ha0 : 0 ≤ alpha := by
    dsimp [alpha]
    positivity
  have ha1 : alpha ≤ 1 := by
    dsimp [alpha]
    exact (div_le_one₀ hqb0).mpr hqb.le
  have hb0 : 0 ≤ beta := by
    dsimp [beta]
    positivity
  have hb1 : beta ≤ 1 := by
    dsimp [beta]
    exact (div_le_one₀ hqo0).mpr hqo.le
  have hs0 : 0 ≤ s := by
    dsimp [s]
    positivity
  have hs1 : s ≤ 1 := by
    dsimp [s]
    exact (div_le_one₀ hprod0).mpr hprodOne
  have hY2 : 2 ≤ Y := by
    dsimp [Y]
    omega
  have hbase :=
    card_mixedCoordinateBoxBlock_le_box_mul_residual
      (N := N) (Ab := Ab) (Kb := Kb) (Ao := Ao) (Ko := Ko)
      hL (by omega) hzX hqb hqo hM
  have hbox :
      finiteWeightBoxSum
          (crossRetainedFamily (P := oddPrimesUpTo z)
            (mixedQU L alpha) (mixedQW L beta)
            (mixedQLinear L s)) X ≤
        mixedAllCutoffSharpBoxBound L z X R qb qo := by
    dsimp [mixedAllCutoffSharpBoxBound, alpha, beta, s]
    exact mixed_threeFormBoxSum_le_allCutoffs
      ha0 ha1 hb0 hb1 hs0 hs1 (by omega) hz
  have hresidual :
      (∑ t ∈ Icc 1 Y,
          if Rough L t then
            s ^ primeFactorCountBetween L X t
          else 0) ≤
        mixedBlockResidualBound L N X qb qo := by
    dsimp [mixedBlockResidualBound, Y, s]
    exact roughResidualSubinterval_le_mertens
      hL hLX hY hY2 (by norm_num) hs0 hs1
  have hbox0 :
      0 ≤ finiteWeightBoxSum
        (crossRetainedFamily (P := oddPrimesUpTo z)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) X := by
    rw [finiteWeightBoxSum_cross_eq_integerWeight]
    apply sum_nonneg
    intro p hp
    dsimp [alpha, beta, s]
    exact mixedCrossIntegerWeight_nonneg hqb hqo
  have hresidual0 :
      0 ≤ ∑ t ∈ Icc 1 Y,
        if Rough L t then
          s ^ primeFactorCountBetween L X t
        else 0 := by
    apply sum_nonneg
    intro t ht
    split_ifs <;> positivity
  have hprefactor0 :=
    mixedBlockPrefactor_nonneg
      (Ab := Ab) (Kb := Kb) (Ao := Ao) (Ko := Ko)
      hL ((show 1 ≤ L by omega).trans hLX) hqb hqo
  have hscaledBox :
      mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
          finiteWeightBoxSum
            (crossRetainedFamily (P := oddPrimesUpTo z)
              (mixedQU L alpha) (mixedQW L beta)
              (mixedQLinear L s)) X ≤
        mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
          mixedAllCutoffSharpBoxBound L z X R qb qo :=
    mul_le_mul_of_nonneg_left hbox hprefactor0
  have hscaledBox0 :
      0 ≤ mixedBlockPrefactor L X Ab Kb Ao Ko qb qo *
        mixedAllCutoffSharpBoxBound L z X R qb qo :=
    mul_nonneg hprefactor0 (hbox0.trans hbox)
  dsimp [alpha, beta, s, Y] at hbase hresidual0 hresidual
  exact hbase.trans <|
    (mul_le_mul_of_nonneg_right hscaledBox hresidual0).trans
      (mul_le_mul_of_nonneg_left hresidual hscaledBox0)

end

end Erdos327.Analytic
