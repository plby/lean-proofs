/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section7BiasedAffineSlice

/-!
# The quantitative choice of distortion rank in Bilu Section 7

For `sigma ≥ 1`, take `delta = 1/(2√sigma)` and
`r = ⌈8 sigma log(2 sigma)⌉`.  Remark 6.4 gives
`2 sigma < gamma(delta)^r`, which is precisely the corrected residue-cell
inequality at affine target rank `r - 1`.
-/

namespace Erdos186.CFP.Bilu.Section7BiasedNumerics

open scoped RealInnerProductSpace ENNReal
open Set MeasureTheory DistortingMeasure BadlyApproximable
open Section6BiasedResidueCell Section7FreimanMap Section7AffineSlice
open Section7BiasedAffineSlice Section8Synthesis Proposition75Construction

noncomputable section

/-- Bilu's distortion amount. -/
def distortionDelta (sigma : ℝ) : ℝ :=
  1 / (2 * Real.sqrt sigma)

/-- Bilu's number of distorting coordinates. -/
def distortionRank (sigma : ℝ) : ℕ :=
  Nat.ceil (8 * sigma * Real.log (2 * sigma))

theorem distortionDelta_pos {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    0 < distortionDelta sigma := by
  unfold distortionDelta
  positivity

theorem distortionDelta_lt_one {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    distortionDelta sigma < 1 := by
  have hsqrt : 1 ≤ Real.sqrt sigma := Real.one_le_sqrt.mpr hsigma
  unfold distortionDelta
  have hden : 1 < 2 * Real.sqrt sigma := by nlinarith
  exact (div_lt_one (by positivity)).mpr hden

theorem distortionRank_pos {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    0 < distortionRank sigma := by
  rw [distortionRank, Nat.ceil_pos]
  have hlog : 0 < Real.log (2 * sigma) :=
    Real.log_pos (by nlinarith)
  positivity

/-- The entropy gain accumulated over `distortionRank sigma`
coordinates beats the factor `2 sigma`. -/
theorem two_mul_sigma_lt_biasGamma_pow_distortionRank
    {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    2 * sigma <
      biasGamma (distortionDelta sigma) ^ distortionRank sigma := by
  have hsigmaPos : 0 < sigma := zero_lt_one.trans_le hsigma
  have hdeltaPos := distortionDelta_pos hsigma
  have hdeltaOne := distortionDelta_lt_one hsigma
  have hsqrtSq : Real.sqrt sigma ^ 2 = sigma :=
    Real.sq_sqrt hsigmaPos.le
  have hdeltaSq : distortionDelta sigma ^ 2 / 2 = 1 / (8 * sigma) := by
    unfold distortionDelta
    have hsqrtNe : Real.sqrt sigma ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsigmaPos)
    field_simp
    nlinarith
  have hbase := exp_half_sq_lt_biasGamma hdeltaPos hdeltaOne
  rw [hdeltaSq] at hbase
  let X : ℝ := 8 * sigma * Real.log (2 * sigma)
  let r : ℕ := distortionRank sigma
  have hlog : 0 < Real.log (2 * sigma) :=
    Real.log_pos (by nlinarith)
  have hX : 0 < X := by
    dsimp only [X]
    positivity
  have hr : 0 < r := by
    dsimp only [r]
    exact distortionRank_pos hsigma
  have hceil : X ≤ (r : ℝ) := by
    dsimp only [r, distortionRank, X]
    exact Nat.le_ceil _
  have hdiv : Real.log (2 * sigma) ≤ (r : ℝ) / (8 * sigma) := by
    rw [le_div_iff₀ (by positivity : 0 < 8 * sigma)]
    calc
      Real.log (2 * sigma) * (8 * sigma) = X := by
        dsimp only [X]
        ring
      _ ≤ (r : ℝ) := hceil
  have hexpLe : 2 * sigma ≤ Real.exp ((r : ℝ) / (8 * sigma)) := by
    rw [← Real.exp_log (by positivity : 0 < 2 * sigma)]
    exact Real.exp_le_exp.mpr hdiv
  have hpow : Real.exp (1 / (8 * sigma)) ^ r <
      biasGamma (distortionDelta sigma) ^ r :=
    pow_lt_pow_left₀ hbase (Real.exp_pos _).le hr.ne'
  rw [← Real.exp_nat_mul] at hpow
  have hpow' : Real.exp ((r : ℝ) / (8 * sigma)) <
      biasGamma (distortionDelta sigma) ^ r := by
    convert hpow using 1 <;> field_simp
  exact hexpLe.trans_lt hpow'

/-- The corrected numerical premise for the target affine rank `r-1`
with source gap parameter one. -/
theorem corrected_rank_inequality {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    sigma *
        (2 / biasGamma (distortionDelta sigma)) ^ distortionRank sigma ≤
      Real.rpow 2
        ((((distortionRank sigma - 1 : ℕ) : ℝ) + 1 - 1)) := by
  let r : ℕ := distortionRank sigma
  let gamma : ℝ := biasGamma (distortionDelta sigma)
  have hsigmaPos : 0 < sigma := zero_lt_one.trans_le hsigma
  have hr : 0 < r := by
    dsimp only [r]
    exact distortionRank_pos hsigma
  have hgammaPow : 2 * sigma < gamma ^ r := by
    dsimp only [gamma, r]
    exact two_mul_sigma_lt_biasGamma_pow_distortionRank hsigma
  have hgamma : 0 < gamma := by
    have hdeltaPos := distortionDelta_pos hsigma
    have hdeltaOne := distortionDelta_lt_one hsigma
    exact (Real.exp_pos _).trans
      (exp_half_sq_lt_biasGamma hdeltaPos hdeltaOne)
  have hpowTwo : 0 < (2 : ℝ) ^ r := by positivity
  have hmul := mul_lt_mul_of_pos_left hgammaPow
    (a := (2 : ℝ) ^ r / 2) (by positivity)
  have hquot : sigma * (2 / gamma) ^ r < (2 : ℝ) ^ r / 2 := by
    rw [div_pow, mul_div,
      div_lt_iff₀ (pow_pos hgamma r)]
    convert hmul using 1 <;> ring
  have hright : (2 : ℝ) ^ r / 2 =
      Real.rpow 2 ((((r - 1 : ℕ) : ℝ) + 1 - 1)) := by
    have hrEq : r = (r - 1) + 1 := by omega
    simp only [add_sub_cancel_right]
    have hrpow : Real.rpow 2 ((r - 1 : ℕ) : ℝ) =
        (2 : ℝ) ^ (r - 1) := Real.rpow_natCast 2 (r - 1)
    rw [hrpow]
    nth_rewrite 1 [hrEq]
    rw [pow_succ]
    ring
  dsimp only [r, gamma] at hquot ⊢
  rw [← hright]
  exact hquot.le

/-- Propositions 8.3 and 7.1--7.3, with all numerical parameters chosen
internally.  This is the nonvacuous replacement for the old theorem whose
premise contained the spurious factor `sigma * 2^r`. -/
theorem exists_biased_sourceAffineSlice_of_proposition83
    {m : ℕ} (K : Finset (Mahler.IntegralPoint m)) (hK : K.Nonempty)
    (sigma epsilon : ℝ) (hsigma : 1 ≤ sigma)
    (hsum : ((sumset K).card : ℝ) ≤ sigma * K.card)
    (Bpolar : Set (Fin m → ℝ)) (hpolarMeasurable : MeasurableSet Bpolar)
    (hpolarVolume :
      volume Bpolar ≤
        ENNReal.ofReal ((4 : ℝ) ^ m / (epsilon * K.card)))
    (hepsilon : proposition83Threshold m (distortionRank sigma) sigma < epsilon) :
    ∃ proportionConstant : ℕ,
      ∃ a : Fin (distortionRank sigma) → EuclideanSpace ℝ (Fin m),
        ∃ b : Fin (distortionRank sigma) → ℝ,
          ∃ alpha : Fin (distortionRank sigma) → Fin 2,
            (∀ i, WithLp.ofLp (a i) ∈
              cubeDistortingSet (distortionDelta sigma) K) ∧
            IsBadlyApproximable Bpolar
              (epsilon ^ proposition83Exponent m (distortionRank sigma))
              (epsilon ^ proposition83Exponent m (distortionRank sigma))
              (fun i ↦ WithLp.ofLp (a i)) ∧
            (biasGamma (distortionDelta sigma) / 2) ^
                distortionRank sigma * K.card <
              (residueCell a b alpha K).card ∧
            K.card ≤ 2 ^ distortionRank sigma *
              (residueCell a b alpha K).card ∧
            Nonempty (SourceAffineSlice a b proportionConstant
              (residueCell a b alpha K)) := by
  let r : ℕ := distortionRank sigma
  have hr : 0 < r := by
    dsimp only [r]
    exact distortionRank_pos hsigma
  have hdim : 0 < 2 * m + r := by omega
  obtain ⟨aSeq, haCube, haBad⟩ := bilu_proposition_8_3
    K Bpolar sigma epsilon hK hsigma hdim hsum hpolarMeasurable
      hpolarVolume hepsilon
  let a : Fin r → EuclideanSpace ℝ (Fin m) :=
    euclideanSystem (r := r) aSeq
  have ha : ∀ i, WithLp.ofLp (a i) ∈
      cubeDistortingSet (distortionDelta sigma) K := by
    intro i
    simpa only [a, ofLp_euclideanSystem, distortionDelta] using
      haCube i i.isLt
  obtain ⟨proportionConstant, b, alpha, hlarge, hcover, W⟩ :=
    exists_sourceAffineSlice_of_distortingSystem hr K hK a
      (distortionDelta sigma) sigma 1
      (distortionDelta_pos hsigma) (distortionDelta_lt_one hsigma)
      zero_lt_one (zero_lt_one.trans_le hsigma) ha hsum
      (corrected_rank_inequality hsigma)
  refine ⟨proportionConstant, a, b, alpha, ha, ?_, hlarge, hcover, W⟩
  simpa only [r, a, BadlyApproximable.IsBadlyApproximableUpTo,
    ofLp_euclideanSystem] using haBad

end

end Erdos186.CFP.Bilu.Section7BiasedNumerics

#print axioms
  Erdos186.CFP.Bilu.Section7BiasedNumerics.corrected_rank_inequality
#print axioms
  Erdos186.CFP.Bilu.Section7BiasedNumerics.exists_biased_sourceAffineSlice_of_proposition83
