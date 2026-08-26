import ErdosProblems.Erdos67b.MRGSA10JointNearProjection
import ErdosProblems.Erdos67b.MRGSA10OrdinaryMovingProjectionAverage
import ErdosProblems.Erdos67b.MRGSA10FixedHighRestoredPerron
import ErdosProblems.Erdos67b.MRGSA10DoubleIntegralMajorantOn

/-!
# Joint source projection onto the moving A.10 line

The near-diagonal mass and the half endpoint are averaged jointly before
absolute values are discarded.  The coefficient-mass rectangle is then
added using its already proved moving-power estimate.  Nothing in this
module depends on a particular choice of the two selected prime blocks.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The source scalar left by the joint projection argument. -/
def gsA10JointMovingProjectionSourceBudget (y X : ℕ) : ℝ :=
  4 * (harmonic X : ℝ) * Real.log (y : ℝ) /
      (Real.log (X : ℝ)) ^ 2 +
    Real.log (y : ℝ) / (2 * (X : ℝ)) +
    gsA10MovingPerronAveragedMassConstant *
      (Real.log (y : ℝ))⁻¹

private theorem dirichletPerronNearMass_eq_sum_range_jointSource
    (a : ℕ → ℂ) (X : ℕ) (T : ℝ) :
    dirichletPerronNearMass a X T =
      ∑ n ∈ Finset.range (2 * X),
        ‖a n‖ * dirichletPerronNearError X T n := by
  unfold dirichletPerronNearMass
  rw [tsum_eq_sum (s := Finset.range (2 * X))]
  intro n hn
  have hnLower : 2 * X ≤ n := by simpa using hn
  have hnLowerR : (2 : ℝ) * X ≤ n := by exact_mod_cast hnLower
  rw [dirichletPerronNearError, if_neg]
  · simp
  · intro h
    exact (not_lt_of_ge hnLowerR) h.2.2.1

private theorem doubleIntervalIntegral_add_jointSource
    {F G : ℝ → ℝ → ℝ} {eta : ℝ}
    (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G)) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, F alpha beta + G alpha beta) =
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, F alpha beta) +
      (∫ alpha : ℝ in 0..eta, ∫ beta : ℝ in 0..eta, G alpha beta) := by
  have hFinner : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, F alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF 0 eta
  have hGinner : Continuous (fun alpha : ℝ ↦
      ∫ beta : ℝ in 0..eta, G alpha beta) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hG 0 eta
  calc
    _ = ∫ alpha : ℝ in 0..eta,
        ((∫ beta : ℝ in 0..eta, F alpha beta) +
          ∫ beta : ℝ in 0..eta, G alpha beta) := by
      apply intervalIntegral.integral_congr
      intro alpha halpha
      exact intervalIntegral.integral_add
        ((hF.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
        ((hG.comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable 0 eta)
    _ = _ := intervalIntegral.integral_add
      (hFinner.intervalIntegrable 0 eta) (hGinner.intervalIntegrable 0 eta)

/-- The whole normalized tailored-prefix projection has an explicit source
bound.  The continuity premise is purely the regularity needed to commute
the moving Perron integral through the two Bochner interval integrals; no
projection or prefix estimate is assumed. -/
theorem norm_gsA10TwoBlockTailoredIntegratedPrefix_sub_movingPerronIntegrated_div_le_jointSource
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hprimeMass : Erdos67b.PrimeEstimates.primeReciprocals X ≤
      Real.log (X : ℝ))
    (hySize : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ))
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    (hperron : ContinuousOn (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10TwoBlockMovingPerronIntegral f hmul P₁ P₂ y X alpha beta
        ((Real.log (X : ℝ)) ^ 2)))
      (Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹ ×ˢ
        Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹)) :
    ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y X
          (Real.log (y : ℝ))⁻¹ -
        gsA10TwoBlockMovingPerronIntegrated f hmul P₁ P₂ y X
          (Real.log (y : ℝ))⁻¹ ((Real.log (X : ℝ)) ^ 2)‖ /
        (X : ℝ) ≤
      gsA10JointMovingProjectionSourceBudget y X := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let P : ℝ → ℝ → ℂ := fun alpha beta ↦
    positivePrefixSum
      (gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) X
  let Q : ℝ → ℝ → ℂ := fun alpha beta ↦
    gsA10TwoBlockMovingPerronIntegral f hmul P₁ P₂ y X alpha beta
      ((Real.log (X : ℝ)) ^ 2)
  let NE : ℝ → ℝ → ℝ := fun alpha beta ↦
    dirichletPerronNearMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X
        ((Real.log (X : ℝ)) ^ 2) +
      (1 / 2 : ℝ) *
        ‖gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta X‖
  let M : ℝ → ℝ → ℝ :=
    gsA10OrdinaryMovingProjectionMass y X
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦
    NE alpha beta + M alpha beta
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaPos : 0 < eta := by
    dsimp only [eta]
    exact inv_pos.mpr hlogyPos
  have hetaOne : eta ≤ 1 := by
    dsimp only [eta]
    exact (inv_le_one₀ hlogyPos).2 (by linarith)
  have hP : Continuous (Function.uncurry P) := by
    simpa only [P] using
      continuous_positivePrefixSum_gsA10TwoBlockTailoredCoefficient
        hmul P₁ P₂ y X
  have hQ : ContinuousOn (Function.uncurry Q)
      (Set.Icc (0 : ℝ) eta ×ˢ Set.Icc (0 : ℝ) eta) := by
    simpa only [Q] using hperron
  have hnearCont : Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      dirichletPerronNearMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) X
        ((Real.log (X : ℝ)) ^ 2))) := by
    rw [show Function.uncurry (fun alpha beta : ℝ ↦
        dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X
          ((Real.log (X : ℝ)) ^ 2)) =
        Function.uncurry (fun alpha beta : ℝ ↦
          ∑ n ∈ Finset.range (2 * X),
            ‖gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta n‖ *
              dirichletPerronNearError X
                ((Real.log (X : ℝ)) ^ 2) n) by
      funext z
      rcases z with ⟨alpha, beta⟩
      simp only [Function.uncurry_apply_pair]
      exact dirichletPerronNearMass_eq_sum_range_jointSource _ X _]
    apply continuous_finsetSum
    intro n hn
    exact (continuous_uncurry_norm_gsA10TwoBlockTailoredCoefficient
      hmul P₁ P₂ y X n).mul continuous_const
  have hNE : Continuous (Function.uncurry NE) := by
    dsimp only [NE]
    exact hnearCont.add (continuous_const.mul
      (continuous_uncurry_norm_gsA10TwoBlockTailoredCoefficient
        hmul P₁ P₂ y X X))
  have hM : Continuous (Function.uncurry M) := by
    simpa only [M] using
      (continuous_gsA10OrdinaryMovingProjectionMass
        (y := y) (X := X) (by omega))
  have hG : Continuous (Function.uncurry G) := by
    change Continuous (Function.uncurry (fun alpha beta ↦
      NE alpha beta + M alpha beta))
    rw [show Function.uncurry (fun alpha beta ↦
        NE alpha beta + M alpha beta) =
        Function.uncurry NE + Function.uncurry M by
      funext z
      rfl]
    exact hNE.add hM
  have hpoint : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta,
        ‖P alpha beta - Q alpha beta‖ ≤ G alpha beta := by
    intro alpha halpha beta hbeta
    have hbase :=
      norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_massEnvelope
        hmul hbound P₁ P₂ hy hX hlogX hlogy hQ₂ hQ₃
          halpha.1 halpha.2 hbeta.1 hbeta.2
    simpa only [P, Q, G, NE, M, eta,
      gsA10OrdinaryMovingProjectionMass, add_assoc, add_comm,
      add_left_comm] using hbase
  have havg :=
    norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise_continuousOn
      (P := P) (Q := Q) (G := G) hetaPos.le hP.continuousOn hQ
        hG.continuousOn hpoint
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have havgDiv := div_le_div_of_nonneg_right havg hX0
  have hsplit := doubleIntervalIntegral_add_jointSource
    (eta := eta) hNE hM
  have havg' :
      ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y X eta -
          gsA10TwoBlockMovingPerronIntegrated f hmul P₁ P₂ y X eta
            ((Real.log (X : ℝ)) ^ 2)‖ / (X : ℝ) ≤
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, NE alpha beta) / (X : ℝ) +
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, M alpha beta) / (X : ℝ) := by
    have hraw :
        ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y X eta -
            gsA10TwoBlockMovingPerronIntegrated f hmul P₁ P₂ y X eta
              ((Real.log (X : ℝ)) ^ 2)‖ / (X : ℝ) ≤
          2 * ((∫ alpha : ℝ in 0..eta,
            ∫ beta : ℝ in 0..eta, NE alpha beta) +
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta, M alpha beta)) / (X : ℝ) := by
      simpa only [P, Q, G, gsA10TwoBlockTailoredIntegratedPrefix,
        gsA10TailoredIntegratedPrefix, gsA10TwoBlockTailoredCoefficient,
        gsA10TwoBlockMovingPerronIntegrated, hsplit] using havgDiv
    exact hraw.trans_eq (by ring)
  let J : ℝ :=
    4 * (harmonic X : ℝ) * Real.log (y : ℝ) /
        (Real.log (X : ℝ)) ^ 2 +
      Real.log (y : ℝ) / (2 * (X : ℝ))
  have hnear := source_doubleIntervalIntegral_tailored_near_add_half_le
    hmul hcomp hbound P₁ P₂ (show 2 ≤ y by omega) hX hQ₂ hQ₃
  have hnear' :
      (2 / (eta * (X : ℝ))) *
        (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, NE alpha beta) ≤ J := by
    simpa only [eta, NE, J] using hnear
  have hJ0 : 0 ≤ J := by
    dsimp only [J]
    have hH0 : 0 ≤ (harmonic X : ℝ) := gsA10_harmonic_cast_nonneg X
    positivity
  have hnearFinal :
      2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, NE alpha beta) / (X : ℝ) ≤ J := by
    calc
      2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, NE alpha beta) / (X : ℝ) =
          eta * ((2 / (eta * (X : ℝ))) *
            (∫ alpha : ℝ in 0..eta,
              ∫ beta : ℝ in 0..eta, NE alpha beta)) := by
        field_simp [ne_of_gt hetaPos]
      _ ≤ eta * J := mul_le_mul_of_nonneg_left hnear' hetaPos.le
      _ ≤ J := by nlinarith
  have hmass := gsA10MovingPerronMassRectangle_le_sourceLog
    hX (show 3 ≤ y by omega) hlogX hprimeMass hySize
  have hmass' :
      2 * (∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta, M alpha beta) / (X : ℝ) ≤
        gsA10MovingPerronAveragedMassConstant * eta := by
    simpa only [eta, M, gsA10MovingPerronMassRectangle,
      gsA10OrdinaryMovingProjectionMass] using hmass
  calc
    ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y X
          (Real.log (y : ℝ))⁻¹ -
        gsA10TwoBlockMovingPerronIntegrated f hmul P₁ P₂ y X
          (Real.log (y : ℝ))⁻¹ ((Real.log (X : ℝ)) ^ 2)‖ /
        (X : ℝ) ≤
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, NE alpha beta) / (X : ℝ) +
        2 * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, M alpha beta) / (X : ℝ) := by
      simpa only [eta] using havg'
    _ ≤ J + gsA10MovingPerronAveragedMassConstant * eta :=
      add_le_add hnearFinal hmass'
    _ = gsA10JointMovingProjectionSourceBudget y X := by
      dsimp only [J, eta, gsA10JointMovingProjectionSourceBudget]

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.norm_gsA10TwoBlockTailoredIntegratedPrefix_sub_movingPerronIntegrated_div_le_jointSource
