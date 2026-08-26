import ErdosProblems.Erdos520.HarperScheduledOffDiagonalCDF
import Mathlib.Probability.Moments.SubGaussian

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal

namespace Erdos.Problem520

/-!
# Global control of large tilted block coordinates

The relative local limit theorem is naturally strongest on the scheduled
moderate box.  Outside that box, Hoeffding's lemma gives a genuinely
Gaussian (in fact, narrower-than-Gaussian) tail for the exact tilted block.
This file packages that tail as domination by a variance-one Gaussian on
every scheduled lattice cell.  The extra coefficient is the summable cell
width, so product expansion retains ballot scale instead of leaving a fixed
additive start error.
-/

/-- The exact Hoeffding proxy of one linear prime coordinate. -/
noncomputable def harperLinearPrimeHoeffdingProxy
    (p : ℕ) (u : ℝ) : ℝ≥0 :=
  ⟨(Real.cos (u * Real.log (p : ℝ)) /
      Real.sqrt (p : ℝ)) ^ 2, sq_nonneg _⟩

@[simp] theorem coe_harperLinearPrimeHoeffdingProxy
    (p : ℕ) (u : ℝ) :
    (harperLinearPrimeHoeffdingProxy p u : ℝ) =
      (Real.cos (u * Real.log (p : ℝ)) /
        Real.sqrt (p : ℝ)) ^ 2 := rfl

/-- A centered tilted prime coordinate is sub-Gaussian with the fair-sign
variance proxy.  Centering does not change the length of its two-point
range, which is the useful gain over a coarse absolute-value bound. -/
theorem hasSubgaussianMGF_harperCenteredLinearPrimeIncrement
    (p : ℕ) (t u : ℝ) :
    HasSubgaussianMGF
      (harperCenteredLinearPrimeIncrement p t u)
      (harperLinearPrimeHoeffdingProxy p u)
      (harperTiltedCoin p t) := by
  let c : ℝ := Real.cos (u * Real.log (p : ℝ)) /
    Real.sqrt (p : ℝ)
  let X : Bool → ℝ := harperLinearPrimeIncrement p u
  have hX (b : Bool) : X b = cubeSign b * c := by
    dsimp [X, c, harperLinearPrimeIncrement]
    ring
  have hmem : ∀ b, X b ∈ Set.Icc (-|c|) |c| := by
    intro b
    rw [hX]
    have habs : |cubeSign b * c| = |c| := by
      cases b <;> norm_num [cubeSign]
    constructor
    · rw [← habs]
      exact neg_abs_le _
    · rw [← habs]
      exact le_abs_self _
  have hbase := hasSubgaussianMGF_of_mem_Icc
    (μ := harperTiltedCoin p t)
    (X := X) (a := -|c|) (b := |c|)
    (measurable_of_finite X).aemeasurable
    (ae_of_all _ hmem)
  have hparam : ((‖|c| - -|c|‖₊ / 2) ^ 2 : ℝ≥0) =
      harperLinearPrimeHoeffdingProxy p u := by
    apply NNReal.eq
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      coe_nnnorm, Real.norm_eq_abs]
    have hdiff : |c| - -|c| = 2 * |c| := by ring
    rw [hdiff, abs_of_nonneg (by positivity : 0 ≤ 2 * |c|)]
    dsimp [c, harperLinearPrimeHoeffdingProxy]
    rw [show 2 * |Real.cos (u * Real.log (p : ℝ)) /
        Real.sqrt (p : ℝ)| / 2 =
          |Real.cos (u * Real.log (p : ℝ)) /
            Real.sqrt (p : ℝ)| by ring,
      sq_abs]
    rfl
  rw [hparam] at hbase
  apply hbase.congr
  exact ae_of_all _ fun b ↦ by
    unfold X harperCenteredLinearPrimeIncrement
    rw [integral_harperLinearPrimeIncrement]

/-- Sum of the fair-sign Hoeffding proxies over a prime block. -/
noncomputable def harperLinearBlockHoeffdingProxy
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (u : ℝ) : ℝ≥0 :=
  ∑ p ∈ S, harperLinearPrimeHoeffdingProxy p.1 u

@[simp] theorem coe_harperLinearBlockHoeffdingProxy
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (u : ℝ) :
    (harperLinearBlockHoeffdingProxy y S u : ℝ) =
      ∑ p ∈ S,
        (Real.cos (u * Real.log (p.1 : ℝ)) /
          Real.sqrt (p.1 : ℝ)) ^ 2 := by
  simp [harperLinearBlockHoeffdingProxy]

/-- The exact centered sum over a finite prime block is sub-Gaussian with
the sum of its fair-sign coordinate proxies. -/
theorem hasSubgaussianMGF_harperCenteredLinearPrimeBlockSum
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    HasSubgaussianMGF
      (harperCenteredLinearPrimeBlockSum y S t u)
      (harperLinearBlockHoeffdingProxy y S u)
      (harperTiltedCubeLaw y t) := by
  let X : HarperPrimeIndex y → HarperPrimeCube y → ℝ := fun p eta ↦
    harperCenteredLinearPrimeIncrement p.1 t u (eta p)
  have hindep : iIndepFun X (harperTiltedCubeLaw y t) := by
    have h := (iIndepFun_harperTiltedCube_coordinates y t).comp
      (fun p b ↦ harperCenteredLinearPrimeIncrement p.1 t u b)
      (fun _p ↦ measurable_of_finite _)
    simpa only [X, Function.comp_apply] using! h
  have hcoordinate : ∀ p ∈ S,
      HasSubgaussianMGF (X p)
        (harperLinearPrimeHoeffdingProxy p.1 u)
        (harperTiltedCubeLaw y t) := by
    intro p hp
    have hcoin :=
      hasSubgaussianMGF_harperCenteredLinearPrimeIncrement p.1 t u
    have hmp := measurePreserving_harperTiltedCube_eval y t p
    have hcoinMap :
        HasSubgaussianMGF
          (harperCenteredLinearPrimeIncrement p.1 t u)
          (harperLinearPrimeHoeffdingProxy p.1 u)
          ((harperTiltedCubeLaw y t).map
            (fun eta : HarperPrimeCube y ↦ eta p)) := by
      simpa only [hmp.map_eq] using! hcoin
    have hpull := HasSubgaussianMGF.of_map
      hmp.measurable.aemeasurable hcoinMap
    simpa only [X, Function.comp_apply] using! hpull
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun
    hindep (s := S) hcoordinate
  simpa only [X, harperCenteredLinearPrimeBlockSum,
    harperLinearBlockHoeffdingProxy] using! hsum

/-- The exact tilted variance never exceeds the fair-sign Hoeffding proxy. -/
theorem harperLinearBlockVariance_le_hoeffdingProxy
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    harperLinearBlockVariance y S t u ≤
      (harperLinearBlockHoeffdingProxy y S u : ℝ) := by
  unfold harperLinearBlockVariance harperLinearBlockHoeffdingProxy
  simp only [NNReal.coe_sum, coe_harperLinearPrimeHoeffdingProxy]
  apply Finset.sum_le_sum
  intro p hp
  unfold harperLinearPrimeCenteredVariance
  have hcoeff : 0 ≤
      (Real.cos (u * Real.log (p.1 : ℝ)) /
        Real.sqrt (p.1 : ℝ)) ^ 2 := sq_nonneg _
  exact mul_le_of_le_one_right hcoeff
    (one_sub_harperTiltBias_sq_le_one p.1 t)

/-- From prime 16 onward, at least three quarters of the fair-sign proxy
survives in the exact tilted variance. -/
theorem three_fourths_mul_harperLinearBlockHoeffdingProxy_le_variance
    (y : ℕ) (S : Finset (HarperPrimeIndex y))
    (h16 : ∀ p ∈ S, 16 ≤ p.1) (t u : ℝ) :
    (3 / 4 : ℝ) * (harperLinearBlockHoeffdingProxy y S u : ℝ) ≤
      harperLinearBlockVariance y S t u := by
  unfold harperLinearBlockVariance harperLinearBlockHoeffdingProxy
  simp only [NNReal.coe_sum, coe_harperLinearPrimeHoeffdingProxy,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  unfold harperLinearPrimeCenteredVariance
  simpa only [mul_comm] using!
    mul_le_mul_of_nonneg_left
      (three_fourths_le_one_sub_harperTiltBias_sq (h16 p hp) t)
      (sq_nonneg
        (Real.cos (u * Real.log (p.1 : ℝ)) /
          Real.sqrt (p.1 : ℝ)))

/-- Scheduled blocks therefore have proxy at most `2/3` whenever their
exact off-diagonal variance is at most `1/2`. -/
theorem harperScheduledLinearBlockHoeffdingProxy_le_two_thirds
    {y j : ℕ} {t u : ℝ}
    (hvar : harperLinearBlockVariance y
        (harperScheduledPrimeBlock y j) t u ≤ (1 / 2 : ℝ)) :
    (harperLinearBlockHoeffdingProxy y
        (harperScheduledPrimeBlock y j) u : ℝ) ≤ 2 / 3 := by
  have hlower :=
    three_fourths_mul_harperLinearBlockHoeffdingProxy_le_variance
      y (harperScheduledPrimeBlock y j)
      (fun p hp ↦ sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp)
      t u
  linarith

/-! ## Exact tilted block tails -/

/-- Two-sided Chernoff bound for an arbitrary finite tilted prime block. -/
theorem harperCenteredLinearBlockLaw_real_abs_ge_le_exp
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u R : ℝ)
    (hR : 0 ≤ R) :
    (harperCenteredLinearBlockLaw y S t u).real
        {z : ℝ | R ≤ |z|} ≤
      2 * Real.exp
        (-R ^ 2 /
          (2 * (harperLinearBlockHoeffdingProxy y S u : ℝ))) := by
  let X : HarperPrimeCube y → ℝ :=
    harperCenteredLinearPrimeBlockSum y S t u
  let P : ℝ≥0 := harperLinearBlockHoeffdingProxy y S u
  have hsub : HasSubgaussianMGF X P (harperTiltedCubeLaw y t) := by
    simpa only [X, P] using!
      hasSubgaussianMGF_harperCenteredLinearPrimeBlockSum y S t u
  have hpos :
      (harperTiltedCubeLaw y t).real {eta | R ≤ X eta} ≤
        Real.exp (-R ^ 2 / (2 * (P : ℝ))) :=
    hsub.measure_ge_le hR
  have hneg :
      (harperTiltedCubeLaw y t).real {eta | R ≤ -X eta} ≤
        Real.exp (-R ^ 2 / (2 * (P : ℝ))) := by
    simpa only [Pi.neg_apply] using! hsub.neg.measure_ge_le hR
  have hsplit : {eta | R ≤ |X eta|} ⊆
      {eta | R ≤ X eta} ∪ {eta | R ≤ -X eta} := by
    intro eta heta
    change R ≤ |X eta| at heta
    by_cases hx : 0 ≤ X eta
    · left
      change R ≤ X eta
      rwa [abs_of_nonneg hx] at heta
    · have hx' : X eta ≤ 0 := le_of_not_ge hx
      right
      change R ≤ -X eta
      rwa [abs_of_nonpos hx'] at heta
  have hcube :
      (harperTiltedCubeLaw y t).real {eta | R ≤ |X eta|} ≤
        2 * Real.exp (-R ^ 2 / (2 * (P : ℝ))) := by
    calc
      (harperTiltedCubeLaw y t).real {eta | R ≤ |X eta|} ≤
          (harperTiltedCubeLaw y t).real
            ({eta | R ≤ X eta} ∪ {eta | R ≤ -X eta}) :=
        measureReal_mono hsplit
      _ ≤ (harperTiltedCubeLaw y t).real {eta | R ≤ X eta} +
          (harperTiltedCubeLaw y t).real {eta | R ≤ -X eta} :=
        measureReal_union_le _ _
      _ ≤ Real.exp (-R ^ 2 / (2 * (P : ℝ))) +
          Real.exp (-R ^ 2 / (2 * (P : ℝ))) := add_le_add hpos hneg
      _ = 2 * Real.exp (-R ^ 2 / (2 * (P : ℝ))) := by ring
  have hset : MeasurableSet {z : ℝ | R ≤ |z|} :=
    measurableSet_le measurable_const measurable_id.abs
  have hmap := map_measureReal_apply
    (μ := harperTiltedCubeLaw y t)
    (measurable_of_finite X) hset
  rw [show harperCenteredLinearBlockLaw y S t u =
      Measure.map X (harperTiltedCubeLaw y t) by
        rfl,
    hmap]
  simpa only [Set.preimage_setOf_eq, X, P] using! hcube

/-- With proxy at most `2/3`, the exact tilted block has the explicit
two-sided tail `2 exp (-3 R^2/4)`. -/
theorem harperCenteredLinearBlockLaw_real_abs_ge_le_exp_three_fourths
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u R : ℝ)
    (hR : 0 ≤ R)
    (hproxyPos : 0 < (harperLinearBlockHoeffdingProxy y S u : ℝ))
    (hproxy : (harperLinearBlockHoeffdingProxy y S u : ℝ) ≤ 2 / 3) :
    (harperCenteredLinearBlockLaw y S t u).real
        {z : ℝ | R ≤ |z|} ≤
      2 * Real.exp (-(3 / 4 : ℝ) * R ^ 2) := by
  have htail := harperCenteredLinearBlockLaw_real_abs_ge_le_exp
    y S t u R hR
  have hden :
      2 * (harperLinearBlockHoeffdingProxy y S u : ℝ) ≤ 4 / 3 := by
    linarith
  have hdenPos : 0 <
      2 * (harperLinearBlockHoeffdingProxy y S u : ℝ) := by positivity
  have hquot : (3 / 4 : ℝ) * R ^ 2 ≤
      R ^ 2 /
        (2 * (harperLinearBlockHoeffdingProxy y S u : ℝ)) := by
    apply (le_div_iff₀ hdenPos).2
    have hR2 : 0 ≤ R ^ 2 := sq_nonneg R
    nlinarith
  have hexponent :
      -R ^ 2 / (2 * (harperLinearBlockHoeffdingProxy y S u : ℝ)) ≤
        -(3 / 4 : ℝ) * R ^ 2 := by
    calc
      -R ^ 2 / (2 * (harperLinearBlockHoeffdingProxy y S u : ℝ)) =
          -(R ^ 2 /
            (2 * (harperLinearBlockHoeffdingProxy y S u : ℝ))) := by ring
      _ ≤ -((3 / 4 : ℝ) * R ^ 2) := neg_le_neg hquot
      _ = -(3 / 4 : ℝ) * R ^ 2 := by ring
  exact htail.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexponent) (by norm_num))

/-! ## Variance-one Gaussian cell mass -/

/-- A coarse lower density bound for the variance-one comparison Gaussian. -/
theorem gaussianPDFReal_zero_one_ge
    {a delta x : ℝ} (hdelta1 : delta ≤ 1)
    (hx : x ∈ Ioc a (a + delta)) :
    (1 / 3 : ℝ) * Real.exp (-((|a| + 1) ^ 2) / 2) ≤
      gaussianPDFReal 0 (1 : ℝ≥0) x := by
  have hdenPos : 0 < Real.sqrt (2 * Real.pi * (1 : ℝ)) := by
    apply Real.sqrt_pos.2
    positivity
  have hinside : 2 * Real.pi * (1 : ℝ) ≤ 9 := by
    nlinarith [Real.pi_lt_four]
  have hsqrt : Real.sqrt (2 * Real.pi * (1 : ℝ)) ≤ 3 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    nlinarith [hinside]
  have hcoef : (1 / 3 : ℝ) ≤
      (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ := by
    simpa only [one_div] using!
      one_div_le_one_div_of_le hdenPos hsqrt
  have hxsub0 : 0 ≤ x - a := by linarith [hx.1]
  have hxsub : x - a ≤ delta := by linarith [hx.2]
  have hxabs : |x| ≤ |a| + 1 := by
    calc
      |x| = |a + (x - a)| := by ring_nf
      _ ≤ |a| + |x - a| := abs_add_le _ _
      _ = |a| + (x - a) := by rw [abs_of_nonneg hxsub0]
      _ ≤ |a| + delta := by linarith
      _ ≤ |a| + 1 := by linarith
  have hxsq : x ^ 2 ≤ (|a| + 1) ^ 2 := by
    rw [← sq_abs x]
    exact pow_le_pow_left₀ (abs_nonneg x) hxabs 2
  have hexp :
      Real.exp (-((|a| + 1) ^ 2) / 2) ≤
        Real.exp (-x ^ 2 / (2 * (1 : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold gaussianPDFReal
  simp only [sub_zero, NNReal.coe_one, mul_one]
  have hcoef' : (1 / 3 : ℝ) ≤
      (Real.sqrt (2 * Real.pi))⁻¹ := by simpa using! hcoef
  have hexp' : Real.exp (-((|a| + 1) ^ 2) / 2) ≤
      Real.exp (-x ^ 2 / 2) := by simpa using! hexp
  exact mul_le_mul hcoef' hexp' (by positivity) (by positivity)

/-- Every interval of positive length at most one has the corresponding
variance-one Gaussian mass lower bound. -/
theorem gaussianReal_zero_one_real_Ioc_ge
    {a delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (delta / 3) * Real.exp (-((|a| + 1) ^ 2) / 2) ≤
      (gaussianReal 0 (1 : ℝ≥0)).real (Ioc a (a + delta)) := by
  rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num)]
  rw [ENNReal.toReal_ofReal]
  · calc
      (delta / 3) * Real.exp (-((|a| + 1) ^ 2) / 2) =
          ∫ _x in Ioc a (a + delta),
            (1 / 3 : ℝ) * Real.exp (-((|a| + 1) ^ 2) / 2) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
          ENNReal.toReal_ofReal (by linarith : 0 ≤ a + delta - a)]
        simp only [smul_eq_mul]
        ring
      _ ≤ ∫ x in Ioc a (a + delta),
          gaussianPDFReal 0 (1 : ℝ≥0) x := by
        apply setIntegral_mono_on
        · exact MeasureTheory.integrableOn_const
            (μ := volume) (s := Ioc a (a + delta))
            (C := (1 / 3 : ℝ) *
              Real.exp (-((|a| + 1) ^ 2) / 2))
            (hs := by rw [Real.volume_Ioc]; simp)
        · exact (integrable_gaussianPDFReal 0 (1 : ℝ≥0)).integrableOn
        · exact measurableSet_Ioc
        · intro x hx
          exact gaussianPDFReal_zero_one_ge hdelta1 hx
  · exact integral_nonneg fun x ↦
      gaussianPDFReal_nonneg 0 (1 : ℝ≥0) x

/-! ## Outside-cell domination -/

/-- The exponential margin at the scheduled threshold dominates the fourth
power of the polynomial lattice denominator. -/
theorem eventually_six_mul_scheduledWidthDenominator_sq_le_exp_twoPow :
    ∀ᶠ j : ℕ in atTop,
      6 * ((((j + 1 : ℕ) : ℝ) ^ 2) ^ 2) ≤
        Real.exp ((((2 ^ j : ℕ) : ℝ)) / 1024) := by
  have ht : Tendsto
      (fun x : ℝ ↦ Real.exp ((1 / 1024 : ℝ) * x) / x ^ (4 : ℝ))
      atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop (4 : ℝ) (1 / 1024 : ℝ) (by norm_num)
  have hpowNat : Tendsto (fun j : ℕ ↦ 2 ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))
  have hpowReal : Tendsto (fun j : ℕ ↦ (((2 ^ j : ℕ) : ℝ)))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hpowNat
  have hcomp := ht.comp hpowReal
  filter_upwards [hcomp.eventually (eventually_ge_atTop (96 : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with j hj hjOne
  let n : ℝ := (((2 ^ j : ℕ) : ℝ))
  have hnPos : 0 < n := by dsimp [n]; positivity
  have hjpow : j ≤ 2 ^ j := (Nat.lt_two_pow_self (n := j)).le
  have hsucc : ((j + 1 : ℕ) : ℝ) ≤ 2 * n := by
    have hnat : j + 1 ≤ 2 * (2 ^ j) := by omega
    dsimp [n]
    exact_mod_cast hnat
  have hraw : 96 * n ^ 4 ≤ Real.exp ((1 / 1024 : ℝ) * n) := by
    change 96 ≤ Real.exp ((1 / 1024 : ℝ) * n) / n ^ (4 : ℝ) at hj
    have hj' : 96 ≤ Real.exp ((1 / 1024 : ℝ) * n) / n ^ (4 : ℕ) := by
      have hfour : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
      rw [hfour, Real.rpow_natCast] at hj
      exact hj
    exact (le_div_iff₀ (pow_pos hnPos 4)).mp hj'
  calc
    6 * ((((j + 1 : ℕ) : ℝ) ^ 2) ^ 2) =
        6 * (((j + 1 : ℕ) : ℝ) ^ 4) := by ring
    _ ≤ 6 * (2 * n) ^ 4 := by gcongr
    _ = 96 * n ^ 4 := by ring
    _ ≤ Real.exp ((1 / 1024 : ℝ) * n) := hraw
    _ = Real.exp ((((2 ^ j : ℕ) : ℝ)) / 1024) := by
      dsimp [n]
      congr 1
      ring

/-- Outside the moderate threshold, the strict Hoeffding/Gaussian exponent
gap pays for two powers of the scheduled cell denominator. -/
theorem eventually_scheduledOutsideCell_exponential_budget :
    ∀ᶠ j : ℕ in atTop, ∀ a : ℝ,
      (1 / 4 : ℝ) * Real.sqrt (((2 ^ j : ℕ) : ℝ)) < |a| + 1 →
        6 * ((((j + 1 : ℕ) : ℝ) ^ 2) ^ 2) *
            Real.exp (-(3 / 4 : ℝ) * (|a| - 1) ^ 2) ≤
          Real.exp (-((|a| + 1) ^ 2) / 2) := by
  filter_upwards
      [eventually_six_mul_scheduledWidthDenominator_sq_le_exp_twoPow,
        eventually_ge_atTop (16 : ℕ)] with j hpoly hj
  intro a ha
  let n : ℝ := (((2 ^ j : ℕ) : ℝ))
  let A : ℝ := |a|
  let T : ℝ := (1 / 4 : ℝ) * Real.sqrt n
  let D : ℝ := (((j + 1 : ℕ) : ℝ) ^ 2)
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hsqrtSq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  have hpowNat : 2 ^ 16 ≤ 2 ^ j :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hj
  have hpowReal : (65536 : ℝ) ≤ n := by
    dsimp [n]
    exact_mod_cast hpowNat
  have hsqrt : (256 : ℝ) ≤ Real.sqrt n := by
    have h := Real.sqrt_le_sqrt hpowReal
    norm_num at h ⊢
    exact h
  have hT : 64 ≤ T := by dsimp [T]; nlinarith
  have hAhalf : T / 2 ≤ A := by
    dsimp [A, T, n] at ha ⊢
    linarith
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA16 : 16 ≤ A := by
    have : 32 ≤ T / 2 := by linarith
    linarith
  have hAsq : n / 64 ≤ A ^ 2 := by
    have hhalf0 : 0 ≤ T / 2 := by linarith
    have hsquare := pow_le_pow_left₀ hhalf0 hAhalf 2
    dsimp [T] at hsquare
    nlinarith
  have hgap : A ^ 2 / 16 ≤
      (3 / 4 : ℝ) * (A - 1) ^ 2 - (A + 1) ^ 2 / 2 := by
    nlinarith
  have hnA : n / 1024 ≤ A ^ 2 / 16 := by nlinarith
  have hpoly' : 6 * D ^ 2 ≤ Real.exp (n / 1024) := by
    simpa only [D, n] using! hpoly
  have hcoef : 6 * D ^ 2 ≤ Real.exp
      ((3 / 4 : ℝ) * (A - 1) ^ 2 - (A + 1) ^ 2 / 2) := by
    calc
      6 * D ^ 2 ≤ Real.exp (n / 1024) := hpoly'
      _ ≤ Real.exp (A ^ 2 / 16) := Real.exp_le_exp.mpr hnA
      _ ≤ Real.exp
          ((3 / 4 : ℝ) * (A - 1) ^ 2 - (A + 1) ^ 2 / 2) :=
        Real.exp_le_exp.mpr hgap
  calc
    6 * ((((j + 1 : ℕ) : ℝ) ^ 2) ^ 2) *
          Real.exp (-(3 / 4 : ℝ) * (|a| - 1) ^ 2) =
        (6 * D ^ 2) *
          Real.exp (-(3 / 4 : ℝ) * (A - 1) ^ 2) := by rfl
    _ ≤ Real.exp
          ((3 / 4 : ℝ) * (A - 1) ^ 2 - (A + 1) ^ 2 / 2) *
        Real.exp (-(3 / 4 : ℝ) * (A - 1) ^ 2) := by
      exact mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = Real.exp (-((A + 1) ^ 2) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-((|a| + 1) ^ 2) / 2) := rfl

/-- Every sufficiently late off-diagonal tilted block cell outside the
moderate range is dominated by one summable cell-width times a
variance-one Gaussian cell. -/
theorem
    exists_eventually_harperScheduledOffDiagonalOutsideCellProbability_le_width_mul_gaussianOne
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
          |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
              (1 / 64 : ℝ) →
            ∀ a : ℝ,
              (1 / 4 : ℝ) *
                  Real.sqrt (((2 ^ j : ℕ) : ℝ)) < |a| + 1 →
              (harperCenteredLinearBlockLaw y
                  (harperScheduledPrimeBlock y j) t u).real
                    (Ioc a
                      (a + harperScheduledRelativeIntervalWidth j)) ≤
                harperScheduledRelativeIntervalWidth j *
                  (gaussianReal 0 (1 : ℝ≥0)).real
                    (Ioc a
                      (a + harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jvar, hJvar⟩ :=
    exists_eventually_harperScheduledOffDiagonalVariance_quarter_half M
  obtain ⟨Jbudget, hJbudget⟩ := Filter.eventually_atTop.1
    eventually_scheduledOutsideCell_exponential_budget
  refine ⟨max (max Jvar Jbudget) 16, ?_⟩
  intro j hj y hy t htLower htUpper u hscale a ha
  have hjvar : Jvar ≤ j :=
    (le_max_left Jvar Jbudget).trans (le_max_left _ 16) |>.trans hj
  have hjbudget : Jbudget ≤ j :=
    (le_max_right Jvar Jbudget).trans (le_max_left _ 16) |>.trans hj
  have hj16 : 16 ≤ j := (le_max_right _ 16).trans hj
  let delta : ℝ := harperScheduledRelativeIntervalWidth j
  let D : ℝ := (((j + 1 : ℕ) : ℝ) ^ 2)
  let R : ℝ := |a| - 1
  have hdeltaPos : 0 < delta := by
    simpa only [delta] using! harperScheduledRelativeIntervalWidth_pos j
  have hdeltaOne : delta ≤ 1 := by
    simpa only [delta] using! harperScheduledRelativeIntervalWidth_le_one j
  have hpowNat : 2 ^ 16 ≤ 2 ^ j :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hj16
  have hpowReal : (65536 : ℝ) ≤ (((2 ^ j : ℕ) : ℝ)) := by
    exact_mod_cast hpowNat
  have hsqrt : (256 : ℝ) ≤
      Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by
    have h := Real.sqrt_le_sqrt hpowReal
    norm_num at h ⊢
    exact h
  have hR : 0 ≤ R := by
    dsimp [R]
    nlinarith
  have hvar := hJvar j hjvar y hy t htLower htUpper u hscale
  have hproxyUpper :
      (harperLinearBlockHoeffdingProxy y
          (harperScheduledPrimeBlock y j) u : ℝ) ≤ 2 / 3 :=
    harperScheduledLinearBlockHoeffdingProxy_le_two_thirds hvar.2.le
  have hproxyLower :
      harperLinearBlockVariance y
          (harperScheduledPrimeBlock y j) t u ≤
        (harperLinearBlockHoeffdingProxy y
          (harperScheduledPrimeBlock y j) u : ℝ) :=
    harperLinearBlockVariance_le_hoeffdingProxy y
      (harperScheduledPrimeBlock y j) t u
  have hproxyPos : 0 <
      (harperLinearBlockHoeffdingProxy y
        (harperScheduledPrimeBlock y j) u : ℝ) :=
    ((by norm_num : (0 : ℝ) < 1 / 4).trans hvar.1).trans_le hproxyLower
  have htail :=
    harperCenteredLinearBlockLaw_real_abs_ge_le_exp_three_fourths
      y (harperScheduledPrimeBlock y j) t u R hR
      hproxyPos hproxyUpper
  have hcellSubset : Ioc a (a + delta) ⊆ {z : ℝ | R ≤ |z|} := by
    intro z hz
    change R ≤ |z|
    have hzsub0 : 0 ≤ z - a := by linarith [hz.1]
    have hzsub : z - a ≤ delta := by linarith [hz.2]
    have haAbs : |a| ≤ |z| + 1 := by
      calc
        |a| = |z - (z - a)| := by ring_nf
        _ ≤ |z| + |z - a| := abs_sub _ _
        _ = |z| + (z - a) := by rw [abs_of_nonneg hzsub0]
        _ ≤ |z| + delta := by linarith
        _ ≤ |z| + 1 := by linarith
    dsimp [R]
    linarith
  have hcellTail :
      (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u).real
            (Ioc a (a + delta)) ≤
        2 * Real.exp (-(3 / 4 : ℝ) * R ^ 2) :=
    (measureReal_mono hcellSubset).trans htail
  have hbudget := hJbudget j hjbudget a ha
  have hDPos : 0 < D := by dsimp [D]; positivity
  have hdeltaD : delta = D⁻¹ := by
    rfl
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ delta ^ 2 / 3 by positivity)
  have htailVsDensity :
      2 * Real.exp (-(3 / 4 : ℝ) * R ^ 2) ≤
        delta * ((delta / 3) *
          Real.exp (-((|a| + 1) ^ 2) / 2)) := by
    calc
      2 * Real.exp (-(3 / 4 : ℝ) * R ^ 2) =
          (delta ^ 2 / 3) *
            (6 * D ^ 2 *
              Real.exp (-(3 / 4 : ℝ) * (|a| - 1) ^ 2)) := by
        rw [hdeltaD]
        dsimp [R]
        field_simp [ne_of_gt hDPos]
        ring
      _ ≤ (delta ^ 2 / 3) *
          Real.exp (-((|a| + 1) ^ 2) / 2) := hscaled
      _ = delta * ((delta / 3) *
          Real.exp (-((|a| + 1) ^ 2) / 2)) := by ring
  have hgaussian := gaussianReal_zero_one_real_Ioc_ge
    (a := a) hdeltaPos hdeltaOne
  calc
    (harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y j) t u).real
          (Ioc a (a + harperScheduledRelativeIntervalWidth j)) =
        (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u).real
            (Ioc a (a + delta)) := rfl
    _ ≤ 2 * Real.exp (-(3 / 4 : ℝ) * R ^ 2) := hcellTail
    _ ≤ delta * ((delta / 3) *
        Real.exp (-((|a| + 1) ^ 2) / 2)) := htailVsDensity
    _ ≤ delta * (gaussianReal 0 (1 : ℝ≥0)).real
        (Ioc a (a + delta)) :=
      mul_le_mul_of_nonneg_left hgaussian hdeltaPos.le
    _ = harperScheduledRelativeIntervalWidth j *
        (gaussianReal 0 (1 : ℝ≥0)).real
          (Ioc a
            (a + harperScheduledRelativeIntervalWidth j)) := rfl

/-- Global scheduled cell envelope: the variance-matched Gaussian controls
the moderate part, while a summably weighted variance-one Gaussian controls
the large-coordinate part. -/
theorem
    exists_eventually_harperScheduledOffDiagonalGlobalCellProbability_le_gaussianMixture
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : ℝ,
          |u - t| * Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤
              (1 / 64 : ℝ) →
            ∀ a : ℝ,
              (harperCenteredLinearBlockLaw y
                  (harperScheduledPrimeBlock y j) t u).real
                    (Ioc a
                      (a + harperScheduledRelativeIntervalWidth j)) ≤
                (1 + harperScheduledRelativeIntervalWidth j) *
                    (harperGaussianBlockLaw y
                      (harperScheduledPrimeBlock y j) t u).real
                        (Ioc a
                          (a + harperScheduledRelativeIntervalWidth j)) +
                  harperScheduledRelativeIntervalWidth j *
                    (gaussianReal 0 (1 : ℝ≥0)).real
                      (Ioc a
                        (a + harperScheduledRelativeIntervalWidth j)) := by
  obtain ⟨Jmoderate, hJmoderate⟩ :=
    exists_eventually_harperScheduledOffDiagonalRelativeIntervalProbability_le_one_add_width_mul_gaussian M
  obtain ⟨Joutside, hJoutside⟩ :=
    exists_eventually_harperScheduledOffDiagonalOutsideCellProbability_le_width_mul_gaussianOne M
  refine ⟨max Jmoderate Joutside, ?_⟩
  intro j hj y hy t htLower htUpper u hscale a
  have hjmoderate : Jmoderate ≤ j :=
    (le_max_left Jmoderate Joutside).trans hj
  have hjoutside : Joutside ≤ j :=
    (le_max_right Jmoderate Joutside).trans hj
  by_cases ha : |a| + 1 ≤ (1 / 4 : ℝ) *
      Real.sqrt (((2 ^ j : ℕ) : ℝ))
  · have hmain := hJmoderate j hjmoderate y hy t htLower htUpper
      u hscale a ha
    exact hmain.trans (le_add_of_nonneg_right
      (mul_nonneg (harperScheduledRelativeIntervalWidth_pos j).le
        (measureReal_nonneg)))
  · have ha' : (1 / 4 : ℝ) *
        Real.sqrt (((2 ^ j : ℕ) : ℝ)) < |a| + 1 :=
      lt_of_not_ge ha
    have hmain := hJoutside j hjoutside y hy t htLower htUpper
      u hscale a ha'
    exact hmain.trans (le_add_of_nonneg_left
      (mul_nonneg
        (by linarith [harperScheduledRelativeIntervalWidth_pos j] :
          0 ≤ 1 + harperScheduledRelativeIntervalWidth j)
        measureReal_nonneg))

/-! ## Variance-only form for shrinking central bands -/

/-- Pointwise outside-cell domination assuming only the exact variance
window.  This form has no lower bound on the tilt height, so central-band
arithmetic can supply the two variance hypotheses after its `J+d` shift. -/
theorem
    harperScheduledOutsideCellProbability_le_width_mul_gaussianOne_of_variance
    {y j : ℕ} (hj16 : 16 ≤ j) (t u a : ℝ)
    (hvarLower : (1 / 4 : ℝ) <
      harperLinearBlockVariance y
        (harperScheduledPrimeBlock y j) t u)
    (hvarUpper :
      harperLinearBlockVariance y
          (harperScheduledPrimeBlock y j) t u < (1 / 2 : ℝ))
    (ha : (1 / 4 : ℝ) *
      Real.sqrt (((2 ^ j : ℕ) : ℝ)) < |a| + 1)
    (hbudget :
      6 * ((((j + 1 : ℕ) : ℝ) ^ 2) ^ 2) *
          Real.exp (-(3 / 4 : ℝ) * (|a| - 1) ^ 2) ≤
        Real.exp (-((|a| + 1) ^ 2) / 2)) :
    (harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y j) t u).real
          (Ioc a (a + harperScheduledRelativeIntervalWidth j)) ≤
      harperScheduledRelativeIntervalWidth j *
        (gaussianReal 0 (1 : ℝ≥0)).real
          (Ioc a (a + harperScheduledRelativeIntervalWidth j)) := by
  let delta : ℝ := harperScheduledRelativeIntervalWidth j
  let D : ℝ := (((j + 1 : ℕ) : ℝ) ^ 2)
  let R : ℝ := |a| - 1
  have hdeltaPos : 0 < delta := by
    simpa only [delta] using! harperScheduledRelativeIntervalWidth_pos j
  have hdeltaOne : delta ≤ 1 := by
    simpa only [delta] using! harperScheduledRelativeIntervalWidth_le_one j
  have hpowNat : 2 ^ 16 ≤ 2 ^ j :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hj16
  have hpowReal : (65536 : ℝ) ≤ (((2 ^ j : ℕ) : ℝ)) := by
    exact_mod_cast hpowNat
  have hsqrt : (256 : ℝ) ≤
      Real.sqrt (((2 ^ j : ℕ) : ℝ)) := by
    have h := Real.sqrt_le_sqrt hpowReal
    norm_num at h ⊢
    exact h
  have hR : 0 ≤ R := by
    dsimp [R]
    nlinarith
  have hproxyUpper :
      (harperLinearBlockHoeffdingProxy y
          (harperScheduledPrimeBlock y j) u : ℝ) ≤ 2 / 3 :=
    harperScheduledLinearBlockHoeffdingProxy_le_two_thirds hvarUpper.le
  have hproxyLower :
      harperLinearBlockVariance y
          (harperScheduledPrimeBlock y j) t u ≤
        (harperLinearBlockHoeffdingProxy y
          (harperScheduledPrimeBlock y j) u : ℝ) :=
    harperLinearBlockVariance_le_hoeffdingProxy y
      (harperScheduledPrimeBlock y j) t u
  have hproxyPos : 0 <
      (harperLinearBlockHoeffdingProxy y
        (harperScheduledPrimeBlock y j) u : ℝ) :=
    ((by norm_num : (0 : ℝ) < 1 / 4).trans hvarLower).trans_le hproxyLower
  have htail :=
    harperCenteredLinearBlockLaw_real_abs_ge_le_exp_three_fourths
      y (harperScheduledPrimeBlock y j) t u R hR
      hproxyPos hproxyUpper
  have hcellSubset : Ioc a (a + delta) ⊆ {z : ℝ | R ≤ |z|} := by
    intro z hz
    change R ≤ |z|
    have hzsub0 : 0 ≤ z - a := by linarith [hz.1]
    have hzsub : z - a ≤ delta := by linarith [hz.2]
    have haAbs : |a| ≤ |z| + 1 := by
      calc
        |a| = |z - (z - a)| := by ring_nf
        _ ≤ |z| + |z - a| := abs_sub _ _
        _ = |z| + (z - a) := by rw [abs_of_nonneg hzsub0]
        _ ≤ |z| + delta := by linarith
        _ ≤ |z| + 1 := by linarith
    dsimp [R]
    linarith
  have hcellTail :
      (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u).real
            (Ioc a (a + delta)) ≤
        2 * Real.exp (-(3 / 4 : ℝ) * R ^ 2) :=
    (measureReal_mono hcellSubset).trans htail
  have hDPos : 0 < D := by dsimp [D]; positivity
  have hdeltaD : delta = D⁻¹ := by rfl
  have hscaled := mul_le_mul_of_nonneg_left hbudget
    (show 0 ≤ delta ^ 2 / 3 by positivity)
  have htailVsDensity :
      2 * Real.exp (-(3 / 4 : ℝ) * R ^ 2) ≤
        delta * ((delta / 3) *
          Real.exp (-((|a| + 1) ^ 2) / 2)) := by
    calc
      2 * Real.exp (-(3 / 4 : ℝ) * R ^ 2) =
          (delta ^ 2 / 3) *
            (6 * D ^ 2 *
              Real.exp (-(3 / 4 : ℝ) * (|a| - 1) ^ 2)) := by
        rw [hdeltaD]
        dsimp [R]
        field_simp [ne_of_gt hDPos]
        ring
      _ ≤ (delta ^ 2 / 3) *
          Real.exp (-((|a| + 1) ^ 2) / 2) := hscaled
      _ = delta * ((delta / 3) *
          Real.exp (-((|a| + 1) ^ 2) / 2)) := by ring
  have hgaussian := gaussianReal_zero_one_real_Ioc_ge
    (a := a) hdeltaPos hdeltaOne
  calc
    (harperCenteredLinearBlockLaw y
        (harperScheduledPrimeBlock y j) t u).real
          (Ioc a (a + harperScheduledRelativeIntervalWidth j)) =
        (harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y j) t u).real
            (Ioc a (a + delta)) := rfl
    _ ≤ 2 * Real.exp (-(3 / 4 : ℝ) * R ^ 2) := hcellTail
    _ ≤ delta * ((delta / 3) *
        Real.exp (-((|a| + 1) ^ 2) / 2)) := htailVsDensity
    _ ≤ delta * (gaussianReal 0 (1 : ℝ≥0)).real
        (Ioc a (a + delta)) :=
      mul_le_mul_of_nonneg_left hgaussian hdeltaPos.le
    _ = harperScheduledRelativeIntervalWidth j *
        (gaussianReal 0 (1 : ℝ≥0)).real
          (Ioc a
            (a + harperScheduledRelativeIntervalWidth j)) := rfl

end Erdos.Problem520
