import ErdosProblems.Erdos1038.PlatformReferenceRootLimits
import ErdosProblems.Erdos1038.PlatformReferenceSeriesLimits
import ErdosProblems.Erdos1038.ResidualWidthSeriesDirectionalRootFormula

/-!
# Directional root limits on the canonical platform mesh

The differentiated finite inverse series is an implicit root velocity.
This file passes its material numerator and spatial denominator through the
canonical quantile limit and identifies the continuum directional series
with the velocity of the two exterior crossings.
-/

set_option warningAsError false

open Filter Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

variable {iota : Type*} [Fintype iota] [LinearOrder iota]

/-- Continuum spatial derivative of the normalized exterior potential. -/
def platformReferenceExteriorPotentialXDerivativeLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (x : ℝ) : ℝ :=
  1 / x -
    platformReferenceBlockObservableLimit C k a hk ha ha2 hthreshold
      (fun _i d ↦ 1 / (d - x))

/-- Continuum material derivative of the normalized exterior potential at
a fixed spatial point. -/
def platformReferenceExteriorPotentialMaterialVelocityLimit
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (x : ℝ) : ℝ :=
  platformReferenceBlockObservableLimit C k a hk ha ha2 hthreshold
    (fun i d ↦ (C.location i - d) / (d - x))

/-- Material velocity of the width between two nondegenerate continuum
crossings. -/
def platformReferenceCrossingWidthMaterialVelocity
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    (xMinus xPlus : ℝ) : ℝ :=
  -platformReferenceExteriorPotentialMaterialVelocityLimit C k a
      hk ha ha2 hthreshold xPlus /
      platformReferenceExteriorPotentialXDerivativeLimit C k a
        hk ha ha2 hthreshold xPlus +
    platformReferenceExteriorPotentialMaterialVelocityLimit C k a
      hk ha ha2 hthreshold xMinus /
      platformReferenceExteriorPotentialXDerivativeLimit C k a
        hk ha ha2 hthreshold xMinus

/-- At a fixed point left of the platform, the discrete material
potential derivative converges to its block-observable integral. -/
theorem tendsto_platformResidualRefinement_exteriorPotentialMaterialVelocity
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) :
    Tendsto
      (fun n ↦ lagrangeExteriorPotentialMaterialVelocity
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget C n) x)
      atTop
      (nhds (platformReferenceExteriorPotentialMaterialVelocityLimit
        C k a hk ha ha2 hthreshold x)) := by
  have h := tendsto_platformResidualRefinement_blockObservable
    C k a hk ha ha2 hthreshold
    (fun i d ↦ (C.location i - d) / (d - x)) (by
      intro i
      exact (continuousOn_const.sub continuousOn_id).div
        (continuousOn_id.sub continuousOn_const) fun d hd ↦
          (sub_pos.mpr (hxa.trans_le hd.1)).ne')
  unfold lagrangeExteriorPotentialMaterialVelocity
    platformReferenceExteriorPotentialMaterialVelocityLimit
  simp only [platformResidualRefinementTarget, refinedCoordinates]
  convert! h using 1
  funext n
  apply Finset.sum_congr rfl
  intro p _hp
  ring

/-- Fixed-point convergence of the discrete spatial potential derivative. -/
theorem tendsto_platformResidualRefinement_exteriorPotentialXDerivative
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) :
    Tendsto
      (fun n ↦ lagrangeExteriorPotentialXDerivative
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n) x)
      atTop
      (nhds (platformReferenceExteriorPotentialXDerivativeLimit
        C k a hk ha ha2 hthreshold x)) := by
  have h := tendsto_platformResidualRefinement_blockObservable
    C k a hk ha ha2 hthreshold
    (fun _i d ↦ 1 / (d - x)) (by
      intro i
      exact continuousOn_const.div
        (continuousOn_id.sub continuousOn_const) fun d hd ↦
          (sub_pos.mpr (hxa.trans_le hd.1)).ne')
  have hconst : Tendsto (fun _n : ℕ ↦ 1 / x) atTop (nhds (1 / x)) :=
    tendsto_const_nhds
  unfold lagrangeExteriorPotentialXDerivative
    platformReferenceExteriorPotentialXDerivativeLimit
  convert! hconst.sub h using 1
  funext n
  congr 1
  apply Finset.sum_congr rfl
  intro p _hp
  ring

private theorem tendsto_weighted_resolvent_moving_of_fixed
    (jota : ℕ → Type*) [∀ n, Fintype (jota n)]
    (alpha location velocity : ∀ n, jota n → ℝ)
    {edge massBound velocityBound x limit : ℝ}
    (hvelocityBound : 0 ≤ velocityBound)
    (halpha : ∀ n i, 0 ≤ alpha n i)
    (hmass : ∀ n, (∑ i, alpha n i) ≤ massBound)
    (hlocation : ∀ n i, edge ≤ location n i)
    (hvelocity : ∀ n i, |velocity n i| ≤ velocityBound)
    {xSequence : ℕ → ℝ} (hxedge : x < edge)
    (hxSequence : Tendsto xSequence atTop (nhds x))
    (hfixed : Tendsto
      (fun n ↦ ∑ i, alpha n i * velocity n i / (location n i - x))
      atTop (nhds limit)) :
    Tendsto
      (fun n ↦ ∑ i,
        alpha n i * velocity n i / (location n i - xSequence n))
      atTop (nhds limit) := by
  let gap : ℝ := (edge - x) / 2
  have hgap : 0 < gap := div_pos (sub_pos.mpr hxedge) (by norm_num)
  have hxclose : ∀ᶠ n in atTop, |xSequence n - x| < gap := by
    have hball := hxSequence.eventually (Metric.ball_mem_nhds x hgap)
    simpa only [Metric.mem_ball, Real.dist_eq] using! hball
  let moving : ℕ → ℝ := fun n ↦ ∑ i,
    alpha n i * velocity n i / (location n i - xSequence n)
  let fixed : ℕ → ℝ := fun n ↦ ∑ i,
    alpha n i * velocity n i / (location n i - x)
  let bound : ℕ → ℝ := fun n ↦
    (massBound * velocityBound / gap ^ 2) * |xSequence n - x|
  have hboundZero : Tendsto bound atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ x) atTop (nhds x) :=
      tendsto_const_nhds
    have hdiff := hxSequence.sub hconst
    have habs := hdiff.abs
    have hscaled := habs.const_mul (massBound * velocityBound / gap ^ 2)
    simpa only [bound, sub_self, abs_zero, mul_zero] using! hscaled
  have hnormBound : ∀ᶠ n in atTop, |moving n - fixed n| ≤ bound n := by
    filter_upwards [hxclose] with n hn
    have hxnUpper : xSequence n < x + gap := by
      linarith [(abs_lt.mp hn).2]
    have hgapIdentity : edge - x = 2 * gap := by
      dsimp only [gap]
      ring
    have hlocationMoving (i : jota n) : gap < location n i - xSequence n := by
      have hedge := hlocation n i
      linarith [hgapIdentity]
    have hlocationFixed (i : jota n) : gap < location n i - x := by
      have hedge := hlocation n i
      linarith [hgapIdentity]
    have hreciprocal (i : jota n) :
        |1 / (location n i - xSequence n) -
            1 / (location n i - x)| ≤
          |xSequence n - x| / gap ^ 2 := by
      have hmovingPos := hlocationMoving i
      have hfixedPos := hlocationFixed i
      have hmovingPos' : 0 < location n i - xSequence n :=
        hgap.trans hmovingPos
      have hfixedPos' : 0 < location n i - x := hgap.trans hfixedPos
      have hidentity :
          1 / (location n i - xSequence n) -
              1 / (location n i - x) =
            (xSequence n - x) /
              ((location n i - xSequence n) * (location n i - x)) := by
        field_simp [hmovingPos'.ne', hfixedPos'.ne']
        ring
      have hdenAbs :
          |(location n i - xSequence n) * (location n i - x)| =
            (location n i - xSequence n) * (location n i - x) :=
        abs_of_pos (mul_pos hmovingPos' hfixedPos')
      rw [hidentity, abs_div, hdenAbs]
      have hgapSqPos : 0 < gap ^ 2 := sq_pos_of_pos hgap
      have hdenBound : gap ^ 2 ≤
          (location n i - xSequence n) * (location n i - x) := by
        rw [pow_two]
        exact mul_le_mul hmovingPos.le hfixedPos.le hgap.le hmovingPos'.le
      exact div_le_div_of_nonneg_left (abs_nonneg _)
        hgapSqPos hdenBound
    have hdifference : moving n - fixed n =
        ∑ i, alpha n i * velocity n i *
          (1 / (location n i - xSequence n) -
            1 / (location n i - x)) := by
      dsimp only [moving, fixed]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [hdifference]
    calc
      |∑ i, alpha n i * velocity n i *
          (1 / (location n i - xSequence n) -
            1 / (location n i - x))| ≤
          ∑ i, |alpha n i * velocity n i *
            (1 / (location n i - xSequence n) -
              1 / (location n i - x))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, alpha n i * velocityBound *
          (|xSequence n - x| / gap ^ 2) := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [abs_mul, abs_mul, abs_of_nonneg (halpha n i)]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hvelocity n i) (halpha n i))
          (hreciprocal i) (abs_nonneg _)
          (mul_nonneg (halpha n i) hvelocityBound)
      _ = (∑ i, alpha n i) *
          (velocityBound * (|xSequence n - x| / gap ^ 2)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ ≤ massBound *
          (velocityBound * (|xSequence n - x| / gap ^ 2)) := by
        exact mul_le_mul_of_nonneg_right (hmass n)
          (mul_nonneg hvelocityBound
            (div_nonneg (abs_nonneg _) (sq_nonneg gap)))
      _ = bound n := by
        dsimp only [bound]
        field_simp [hgap.ne']
  have hnormZero : Tendsto (fun n ↦ |moving n - fixed n|)
      atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun n ↦ abs_nonneg _)
      hnormBound hboundZero
  have hdifferenceZero : Tendsto (fun n ↦ moving n - fixed n)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using! hnormZero
  have hfixed' : Tendsto fixed atTop (nhds limit) := by
    simpa only [fixed] using! hfixed
  have hsum := hdifferenceZero.add hfixed'
  have hmoving : Tendsto moving atTop (nhds limit) := by
    convert! hsum using 1
    · funext n
      ring
    · simp
  simpa only [moving] using! hmoving

private theorem platformResidualRefinement_velocity_abs_le_one
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a) (n : ℕ)
    (p : iota × Fin (n + 1)) :
    |platformResidualRefinementTarget C n p -
        platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n p| ≤ 1 := by
  have href := platformResidualRefinementReference_mem_Icc
    C k a hk ha ha2 hthreshold n p
  have htarget := C.location_mem p.1
  have hrefLower : 1 ≤ platformResidualRefinementReference C k a
      hk ha ha2 hthreshold n p := ha1.trans href.1
  have hrefUpper := href.2
  have htargetLower := htarget.1
  have htargetUpper := htarget.2
  change |C.location p.1 -
    platformResidualRefinementReference C k a
      hk ha ha2 hthreshold n p| ≤ 1
  rw [abs_le]
  constructor <;> linarith

omit [LinearOrder iota] in
private theorem platformResidualRefinement_alpha_sum_le_one
    (C : ResidualConfiguration iota) (k : ℝ) (hk : 1 ≤ k) (n : ℕ) :
    (∑ p, platformResidualRefinementAlpha C k n p) ≤ 1 := by
  rw [sum_platformResidualRefinementAlpha_eq_one_div C k n]
  simpa using! one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hk

/-- The material numerator remains convergent when evaluated at a moving
point tending to a fixed point left of the platform. -/
theorem tendsto_platformResidualRefinement_exteriorPotentialMaterialVelocity_moving
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) {xSequence : ℕ → ℝ}
    (hxSequence : Tendsto xSequence atTop (nhds x)) :
    Tendsto
      (fun n ↦ lagrangeExteriorPotentialMaterialVelocity
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget C n) (xSequence n))
      atTop
      (nhds (platformReferenceExteriorPotentialMaterialVelocityLimit
        C k a hk ha ha2 hthreshold x)) := by
  apply tendsto_weighted_resolvent_moving_of_fixed
    (fun n ↦ iota × Fin (n + 1))
    (fun n ↦ platformResidualRefinementAlpha C k n)
    (fun n ↦ platformResidualRefinementReference C k a
      hk ha ha2 hthreshold n)
    (fun n p ↦ platformResidualRefinementTarget C n p -
      platformResidualRefinementReference C k a
        hk ha ha2 hthreshold n p)
    (edge := a) (massBound := 1) (velocityBound := 1)
    (x := x)
    (limit := platformReferenceExteriorPotentialMaterialVelocityLimit
      C k a hk ha ha2 hthreshold x)
  · norm_num
  · intro n p
    exact (refinedLagrangeWeight_pos (Nat.succ_pos n)
      (residualLagrangeAlpha_pos C (zero_lt_one.trans_le hk)) p).le
  · exact platformResidualRefinement_alpha_sum_le_one C k hk
  · intro n p
    exact (platformResidualRefinementReference_mem_Icc
      C k a hk ha ha2 hthreshold n p).1
  · exact platformResidualRefinement_velocity_abs_le_one
      C k a hk ha ha1 ha2 hthreshold
  · exact hxa
  · exact hxSequence
  · simpa only [lagrangeExteriorPotentialMaterialVelocity] using!
      tendsto_platformResidualRefinement_exteriorPotentialMaterialVelocity
        C k a hk ha ha2 hthreshold hxa

private theorem tendsto_platformResidualRefinement_resolvent
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hxa : x < a) :
    Tendsto
      (fun n ↦ ∑ p, platformResidualRefinementAlpha C k n p /
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n p - x))
      atTop
      (nhds (platformReferenceBlockObservableLimit C k a
        hk ha ha2 hthreshold (fun _i d ↦ 1 / (d - x)))) := by
  have h := tendsto_platformResidualRefinement_blockObservable
    C k a hk ha ha2 hthreshold
    (fun _i d ↦ 1 / (d - x)) (by
      intro i
      exact continuousOn_const.div
        (continuousOn_id.sub continuousOn_const) fun d hd ↦
          (sub_pos.mpr (hxa.trans_le hd.1)).ne')
  convert! h using 1
  funext n
  apply Finset.sum_congr rfl
  intro p _hp
  ring

/-- The spatial derivative also converges at moving nonzero evaluation
points tending to a point left of the platform. -/
theorem tendsto_platformResidualRefinement_exteriorPotentialXDerivative_moving
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {x : ℝ} (hx0 : x ≠ 0) (hxa : x < a) {xSequence : ℕ → ℝ}
    (hxSequence : Tendsto xSequence atTop (nhds x)) :
    Tendsto
      (fun n ↦ lagrangeExteriorPotentialXDerivative
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n) (xSequence n))
      atTop
      (nhds (platformReferenceExteriorPotentialXDerivativeLimit
        C k a hk ha ha2 hthreshold x)) := by
  have hresolvent := tendsto_weighted_resolvent_moving_of_fixed
    (fun n ↦ iota × Fin (n + 1))
    (fun n ↦ platformResidualRefinementAlpha C k n)
    (fun n ↦ platformResidualRefinementReference C k a
      hk ha ha2 hthreshold n)
    (fun _n _p ↦ (1 : ℝ))
    (edge := a) (massBound := 1) (velocityBound := 1)
    (x := x)
    (limit := platformReferenceBlockObservableLimit C k a
      hk ha ha2 hthreshold (fun _i d ↦ 1 / (d - x)))
    (by norm_num)
    (fun n p ↦ (refinedLagrangeWeight_pos (Nat.succ_pos n)
      (residualLagrangeAlpha_pos C (zero_lt_one.trans_le hk)) p).le)
    (platformResidualRefinement_alpha_sum_le_one C k hk)
    (fun n p ↦ (platformResidualRefinementReference_mem_Icc
      C k a hk ha ha2 hthreshold n p).1)
    (fun _n _p ↦ by norm_num) hxa hxSequence
    (by
      simpa using! (tendsto_platformResidualRefinement_resolvent
        C k a hk ha ha2 hthreshold hxa))
  have hinverse := hxSequence.inv₀ hx0
  have hdifference := hinverse.sub hresolvent
  unfold lagrangeExteriorPotentialXDerivative
    platformReferenceExteriorPotentialXDerivativeLimit
  convert! hdifference using 1
  · funext n
    simp only [one_div]
    congr 1
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  · rw [one_div]

/-- The finite implicit root-velocity expression converges to the velocity
of the two continuum crossings. -/
theorem tendsto_lagrangeInverseWidthRootVelocity_platformResidualRefinement
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus s : ℝ} (hxPlusS : xPlus < s)
    (hs : 0 < s) (hsa : s < a)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold s)
    (hminus : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) xMinus)
    (hplus : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) a xPlus)
    (hminusDerivative : platformReferenceExteriorPotentialXDerivativeLimit
      C k a hk ha ha2 hthreshold xMinus ≠ 0)
    (hplusDerivative : platformReferenceExteriorPotentialXDerivativeLimit
      C k a hk ha ha2 hthreshold xPlus ≠ 0) :
    Tendsto
      (fun n ↦ lagrangeInverseWidthRootVelocity
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget C n))
      atTop
      (nhds (platformReferenceCrossingWidthMaterialVelocity C k a
        hk ha ha2 hthreshold xMinus xPlus)) := by
  let Wplus : ℕ → ℝ := fun n ↦
    platformResidualRefinementPositiveInverseValue C k a
      hk ha ha2 hthreshold n
  let Wminus : ℕ → ℝ := fun n ↦
    platformResidualRefinementNegativeInverseValue C k a
      hk ha ha2 hthreshold n
  have hWplus : Tendsto Wplus atTop (nhds xPlus) := by
    simpa only [Wplus] using!
      tendsto_platformResidualRefinementPositiveInverseValue
        C k a hk ha ha1 ha2 hthreshold hxPlusS hs hsa hbarrier hplus
  have hWminus : Tendsto Wminus atTop (nhds xMinus) := by
    simpa only [Wminus] using!
      tendsto_platformResidualRefinementNegativeInverseValue
        C k a hk ha ha1 ha2 hthreshold hs hsa hbarrier hminus
  have hMplus :=
    tendsto_platformResidualRefinement_exteriorPotentialMaterialVelocity_moving
      C k a hk ha ha1 ha2 hthreshold hplus.2.1 hWplus
  have hMminus :=
    tendsto_platformResidualRefinement_exteriorPotentialMaterialVelocity_moving
      C k a hk ha ha1 ha2 hthreshold (hminus.1.trans ha) hWminus
  have hPplus :=
    tendsto_platformResidualRefinement_exteriorPotentialXDerivative_moving
      C k a hk ha ha2 hthreshold hplus.1.ne' hplus.2.1 hWplus
  have hPminus :=
    tendsto_platformResidualRefinement_exteriorPotentialXDerivative_moving
      C k a hk ha ha2 hthreshold hminus.1.ne (hminus.1.trans ha) hWminus
  have hplusVelocity := hMplus.neg.mul (hPplus.inv₀ hplusDerivative)
  have hminusVelocity := hMminus.mul (hPminus.inv₀ hminusDerivative)
  have hwidthVelocity := hplusVelocity.add hminusVelocity
  unfold lagrangeInverseWidthRootVelocity
    platformReferenceCrossingWidthMaterialVelocity
  simpa only [Wplus, Wminus, platformResidualRefinementPositiveInverseValue,
    platformResidualRefinementNegativeInverseValue, div_eq_mul_inv] using!
      hwidthVelocity

/-- Eventually the actual finite directional series is exactly its two-root
implicit velocity, and therefore has the same continuum limit. -/
theorem tendsto_inverseWidthSeriesDirectional_platformResidualRefinement_crossings
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus s : ℝ} (hxPlusS : xPlus < s)
    (hs : 0 < s) (hsa : s < a)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold s)
    (hminus : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) xMinus)
    (hplus : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) a xPlus)
    (hminusDerivative : platformReferenceExteriorPotentialXDerivativeLimit
      C k a hk ha ha2 hthreshold xMinus ≠ 0)
    (hplusDerivative : platformReferenceExteriorPotentialXDerivativeLimit
      C k a hk ha ha2 hthreshold xPlus ≠ 0) :
    Tendsto
      (fun n ↦ inverseWidthSeriesDirectional
        (platformResidualRefinementAlpha C k n)
        (platformResidualRefinementReference C k a
          hk ha ha2 hthreshold n)
        (platformResidualRefinementTarget C n))
      atTop
      (nhds (platformReferenceCrossingWidthMaterialVelocity C k a
        hk ha ha2 hthreshold xMinus xPlus)) := by
  let alpha : (n : ℕ) → (iota × Fin (n + 1)) → ℝ :=
    fun n ↦ platformResidualRefinementAlpha C k n
  let reference : (n : ℕ) → (iota × Fin (n + 1)) → ℝ :=
    fun n ↦ platformResidualRefinementReference C k a
      hk ha ha2 hthreshold n
  let target : (n : ℕ) → (iota × Fin (n + 1)) → ℝ :=
    fun n ↦ platformResidualRefinementTarget C n
  let Wplus : ℕ → ℝ := fun n ↦
    platformResidualRefinementPositiveInverseValue C k a
      hk ha ha2 hthreshold n
  let Wminus : ℕ → ℝ := fun n ↦
    platformResidualRefinementNegativeInverseValue C k a
      hk ha ha2 hthreshold n
  have hWplus : Tendsto Wplus atTop (nhds xPlus) := by
    simpa only [Wplus] using!
      tendsto_platformResidualRefinementPositiveInverseValue
        C k a hk ha ha1 ha2 hthreshold hxPlusS hs hsa hbarrier hplus
  have hWminus : Tendsto Wminus atTop (nhds xMinus) := by
    simpa only [Wminus] using!
      tendsto_platformResidualRefinementNegativeInverseValue
        C k a hk ha ha1 ha2 hthreshold hs hsa hbarrier hminus
  have hPplus :=
    tendsto_platformResidualRefinement_exteriorPotentialXDerivative_moving
      C k a hk ha ha2 hthreshold hplus.1.ne' hplus.2.1 hWplus
  have hPminus :=
    tendsto_platformResidualRefinement_exteriorPotentialXDerivative_moving
      C k a hk ha ha2 hthreshold hminus.1.ne (hminus.1.trans ha) hWminus
  have hPplusNe := hPplus.eventually_ne hplusDerivative
  have hPminusNe := hPminus.eventually_ne hminusDerivative
  have hpotentialEvent :=
    (tendsto_platformResidualRefinement_exteriorPotential
      C k a hk ha ha2 hthreshold hsa).eventually
        (Ioi_mem_nhds hbarrier)
  have hexact : ∀ᶠ n in atTop,
      inverseWidthSeriesDirectional (alpha n) (reference n) (target n) =
        lagrangeInverseWidthRootVelocity (alpha n) (reference n) (target n) := by
    filter_upwards [hPplusNe, hPminusNe, hpotentialEvent] with
      n hnPlus hnMinus hnPotential
    apply inverseWidthSeriesDirectional_eq_rootVelocity
      (alpha n) (reference n) (target n)
    · intro p
      exact refinedLagrangeWeight_pos (Nat.succ_pos n)
        (residualLagrangeAlpha_pos C (zero_lt_one.trans_le hk)) p
    · exact platformResidualRefinementReference_mem_positiveCoordinates
        C k a hk ha ha2 hthreshold n
    · exact hs
    · intro p
      exact hsa.trans_le
        (platformResidualRefinementReference_mem_Icc
          C k a hk ha ha2 hthreshold n p).1
    · simpa only [alpha, reference,
        platformResidualRefinementExteriorPotential, abs_of_pos hs] using!
          hnPotential
    · simpa only [alpha, reference, Wplus,
        platformResidualRefinementPositiveInverseValue] using! hnPlus
    · simpa only [alpha, reference, Wminus,
        platformResidualRefinementNegativeInverseValue] using! hnMinus
  have hrootVelocity :=
    tendsto_lagrangeInverseWidthRootVelocity_platformResidualRefinement
      C k a hk ha ha1 ha2 hthreshold hxPlusS hs hsa hbarrier
        hminus hplus hminusDerivative hplusDerivative
  apply hrootVelocity.congr'
  filter_upwards [hexact] with n hn
  simpa only [alpha, reference, target] using! hn.symm

/-- Final directional-series value identification: the continuum odd
coefficient sum is the material velocity of the two exterior crossings. -/
theorem two_mul_tsum_platformReferenceScaledLagrangeCoefficientDirectionalLimit_eq_crossingVelocity
    (C : ResidualConfiguration iota)
    (k a : ℝ) (hk : 1 ≤ k) (ha : 0 < a) (ha1 : 1 ≤ a) (ha2 : a < 2)
    (hthreshold : platformThreshold k ≤ a)
    {xMinus xPlus s : ℝ} (hxPlusS : xPlus < s)
    (hs : 0 < s) (hsa : s < a)
    (hbarrier : 0 < platformReferenceExteriorPotentialLimit C k a
      hk ha ha2 hthreshold s)
    (hminus : IsNegativeSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) xMinus)
    (hplus : IsPositiveSlopeExteriorCrossing
      (platformReferenceExteriorPotentialLimit C k a
        hk ha ha2 hthreshold) a xPlus)
    (hminusDerivative : platformReferenceExteriorPotentialXDerivativeLimit
      C k a hk ha ha2 hthreshold xMinus ≠ 0)
    (hplusDerivative : platformReferenceExteriorPotentialXDerivativeLimit
      C k a hk ha ha2 hthreshold xPlus ≠ 0) :
    2 * ∑' j,
        platformReferenceScaledLagrangeCoefficientDirectionalLimit
          C k a hk ha ha2 hthreshold (2 * j + 1) =
      platformReferenceCrossingWidthMaterialVelocity C k a
        hk ha ha2 hthreshold xMinus xPlus := by
  have hlogBarrier : 0 < platformReferenceExteriorLogPotentialLimit
      C k a hk ha ha2 hthreshold s := by
    rw [← platformReferenceExteriorPotentialLimit_eq_logPotentialLimit
      C k a hk ha ha2 hthreshold hs]
    exact hbarrier
  have hcoefficient :=
    tendsto_inverseWidthSeriesDirectional_platformResidualRefinement
      C k a hk ha ha2 hthreshold hs hsa hlogBarrier
  have hcrossings :=
    tendsto_inverseWidthSeriesDirectional_platformResidualRefinement_crossings
      C k a hk ha ha1 ha2 hthreshold hxPlusS hs hsa hbarrier
        hminus hplus hminusDerivative hplusDerivative
  exact tendsto_nhds_unique hcoefficient hcrossings

end

end Erdos1038
