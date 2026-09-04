/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerSourceRationalLiouvilleLowerBounds

/-!
# Exact source-scale rational Liouville bound

This file keeps the literal radical-field degree
`d = 13 ^ (oldRank + 1)` and uses the level-scaled algebraic majorant.
The resulting exact product exponent is `(5 + 34 * d) * H`.
-/

noncomputable section

namespace Erdos240.BakerSourceRationalLiouvilleLowerBounds

open BakerLemma3Concrete
open BakerLemma3Instantiation
open BakerSourceAlgebraicLevelMajorant
open BakerSourceAlgebraicMajorant
open BakerSourceOversizedConstantUniform
open BakerSourceState

/-- Exact radical-degree-scale product bound.  The growth premise is on the
source-faithful level algebraic majorant, whose `q ^ (-J)` rate cancels the
size of the rational grid. -/
theorem rationalLiouvilleProduct_le_exp_exactDegreeScale
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (hl : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J)
    (hgrowth :
      (levelAlgebraicExponentialMajorant P state b bLast
        ((l : ℂ) / (P.q : ℂ)) m).growth ≤
        Real.exp (2 * rationalHeightScale P)) :
    2 *
        (rationalTargetConjugateBound P (coordinatesForState state)
            state.support state.coeff P.h P.LzeroPlusOne b bLast J l m ^
          (13 ^ (oldRank + 1) - 1)) *
        ‖(commonDeltaDenominator P.h P.LzeroPlusOne
          (P.q ^ (J + 1)) m : ℂ)‖ ≤
      Real.exp ((5 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        rationalHeightScale P) := by
  let X := rationalHeightScale P
  let d : ℕ := 13 ^ (oldRank + 1)
  let D : ℝ := ‖(commonDeltaDenominator P.h P.LzeroPlusOne
    (P.q ^ (J + 1)) m : ℂ)‖
  let G : ℝ := (levelAlgebraicExponentialMajorant P state b bLast
    ((l : ℂ) / (P.q : ℂ)) m).growth
  let T : ℝ := rationalTargetConjugateBound P (coordinatesForState state)
    state.support state.coeff P.h P.LzeroPlusOne b bLast J l m
  have hX : 1 ≤ X := one_le_rationalHeightScale P
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hkX : P.k ≤ X := k_le_rationalHeightScale P
  have hD : D < Real.exp (4 * X) := by
    simpa only [D, X, rationalHeightScale] using
      norm_state_rational_commonDeltaDenominator_lt_exp_four_heightScale
        P hJ m hm
  have hDle : D ≤ Real.exp (4 * X) := hD.le
  have hG : G ≤ Real.exp (2 * X) := by
    simpa only [G] using hgrowth
  have hdK : (d : ℝ) ≤ P.k ^ (P.mu / 2) := by
    simpa only [d, Nat.cast_pow, Nat.cast_ofNat] using
      sourceDegree_le_k_rpow_mu_div_two P
  have hkpowk : P.k ^ (P.mu / 2) ≤ P.k := by
    calc
      P.k ^ (P.mu / 2) ≤ P.k ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le P.one_le_k (by
          rw [P.mu_eq]
          norm_num)
      _ = P.k := Real.rpow_one _
  have hdX : (d : ℝ) ≤ X := hdK.trans (hkpowk.trans hkX)
  have hdexp : (d : ℝ) ≤ Real.exp X :=
    hdX.trans (by nlinarith [Real.add_one_le_exp X])
  have hTraw := rationalTargetConjugateBound_le_levelAlgebraicGrowth
    P state b bLast l hl m
  have hG0 : 0 ≤ G := by
    dsimp only [G]
    unfold BakerSourceAlgebraicMajorant.AlgebraicExponentialMajorant.growth
    exact mul_nonneg
      (mul_nonneg
        (stateSourceMajorants P state b bLast
          ((l : ℂ) / (P.q : ℂ)) m).supportMajorant_nonneg
        (mul_nonneg P.coeffHeight_pos.le
          (stateSourceMajorants P state b bLast
            ((l : ℂ) / (P.q : ℂ)) m).deltaMajorant_nonneg))
      (levelAlgebraicExponentialMajorant P state b bLast
        ((l : ℂ) / (P.q : ℂ)) m).majorant_nonneg
  have hT : T ≤ Real.exp (34 * X) := by
    have hproduct :
        (d : ℝ) * D * G * Real.exp (26 * X) ≤
          Real.exp (33 * X) := by
      calc
        (d : ℝ) * D * G * Real.exp (26 * X) ≤
            Real.exp X * Real.exp (4 * X) * Real.exp (2 * X) *
              Real.exp (26 * X) := by
          have h1 : (d : ℝ) * D ≤
              Real.exp X * Real.exp (4 * X) :=
            mul_le_mul hdexp hDle (norm_nonneg _) (Real.exp_pos _).le
          have h2 : (d : ℝ) * D * G ≤
              Real.exp X * Real.exp (4 * X) * Real.exp (2 * X) :=
            mul_le_mul h1 hG hG0 (by positivity)
          exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = Real.exp (33 * X) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
    have hone : (1 : ℝ) ≤ Real.exp (33 * X) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    have htwo : (2 : ℝ) ≤ Real.exp X := by
      nlinarith [Real.exp_one_gt_two.le, Real.exp_le_exp.mpr hX]
    calc
      T ≤ 1 + (d : ℝ) * D * G * Real.exp (26 * X) := by
        simpa only [T, d, D, G, X, rationalHeightScale, Nat.cast_pow,
          Nat.cast_ofNat] using hTraw
      _ ≤ 2 * Real.exp (33 * X) := by nlinarith
      _ ≤ Real.exp X * Real.exp (33 * X) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (34 * X) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hTpow : T ^ (d - 1) ≤ Real.exp ((34 * (d : ℝ)) * X) := by
    calc
      T ^ (d - 1) ≤ (Real.exp (34 * X)) ^ (d - 1) := by
        exact pow_le_pow_left₀ (by
          exact (rationalTargetConjugateBound_pos P
            (coordinatesForState state) state.support state.coeff P.h
            P.LzeroPlusOne b bLast J l m).le) hT _
      _ = Real.exp (((d - 1 : ℕ) : ℝ) * (34 * X)) := by
        rw [Real.exp_nat_mul]
      _ ≤ Real.exp ((34 * (d : ℝ)) * X) := by
        apply Real.exp_le_exp.mpr
        have hdsub : ((d - 1 : ℕ) : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast Nat.sub_le d 1
        calc
          ((d - 1 : ℕ) : ℝ) * (34 * X) ≤
              (d : ℝ) * (34 * X) :=
            mul_le_mul_of_nonneg_right hdsub
              (mul_nonneg (by norm_num) hX0)
          _ = (34 * (d : ℝ)) * X := by ring
  have htwo : (2 : ℝ) ≤ Real.exp X := by
    nlinarith [Real.exp_one_gt_two.le, Real.exp_le_exp.mpr hX]
  calc
    2 * T ^ (d - 1) * D ≤
        Real.exp X * Real.exp ((34 * (d : ℝ)) * X) *
          Real.exp (4 * X) := by
      have hTpow0 : 0 ≤ T ^ (d - 1) := pow_nonneg (by
        exact (rationalTargetConjugateBound_pos P
          (coordinatesForState state) state.support state.coeff P.h
          P.LzeroPlusOne b bLast J l m).le) _
      have h1 : 2 * T ^ (d - 1) ≤
          Real.exp X * Real.exp ((34 * (d : ℝ)) * X) :=
        mul_le_mul htwo hTpow hTpow0 (Real.exp_pos _).le
      exact mul_le_mul h1 hDle (norm_nonneg _) (by positivity)
    _ = Real.exp ((5 + 34 * (d : ℝ)) * X) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ = Real.exp ((5 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
          rationalHeightScale P) := by
      dsimp only [d, X]
      norm_num [Nat.cast_pow]

/-- Exact lower bound for the rational Liouville threshold at a Lemma-5
target, retaining the literal radical-field degree. -/
theorem exp_neg_exactDegreeScale_le_stateRationalLiouvilleThreshold
    {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank)) {J : ℕ} (hJ : P.LevelOK J)
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (l : ℕ) (hl : l ≤ P.R (J + 1))
    (m : VDPLMultiIndex (oldRank + 1))
    (hm : VDPLMultiIndex.weight m ≤ P.Sstep J)
    (hgrowth :
      (levelAlgebraicExponentialMajorant P state b bLast
        ((l : ℂ) / (P.q : ℂ)) m).growth ≤
        Real.exp (2 * rationalHeightScale P)) :
    Real.exp (-((5 + 34 * (13 ^ (oldRank + 1) : ℝ)) *
        rationalHeightScale P)) ≤
      stateRationalLiouvilleThreshold P J state b bLast l m := by
  let A : ℝ :=
    (5 + 34 * (13 ^ (oldRank + 1) : ℝ)) * rationalHeightScale P
  have hproduct := rationalLiouvilleProduct_le_exp_exactDegreeScale
    P hJ state b bLast l hl m hm hgrowth
  have hproduct' :
      2 *
          (rationalTargetConjugateBound P (coordinatesForState state)
              state.support state.coeff P.h P.LzeroPlusOne b bLast J l m ^
            (13 ^ (oldRank + 1) - 1)) *
          ‖(commonDeltaDenominator P.h P.LzeroPlusOne
            (P.q ^ (J + 1)) m : ℂ)‖ ≤
        Real.exp (3 * (4 * A / 3) / 4) := by
    convert hproduct using 1 <;> dsimp only [A] <;> ring_nf
  have hgeneric :=
    BakerSourceOversizedConstantUniform.exp_neg_three_quarters_le_stateRationalLiouvilleThreshold
      P state b bLast l m (4 * A / 3) hproduct'
  convert hgeneric using 1 <;> dsimp only [A] <;> ring_nf

end Erdos240.BakerSourceRationalLiouvilleLowerBounds

#print axioms Erdos240.BakerSourceRationalLiouvilleLowerBounds.rationalLiouvilleProduct_le_exp_exactDegreeScale
#print axioms Erdos240.BakerSourceRationalLiouvilleLowerBounds.exp_neg_exactDegreeScale_le_stateRationalLiouvilleThreshold
