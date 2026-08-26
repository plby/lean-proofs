import ErdosProblems.Erdos1038.ResidualWidthSeriesBranchIdentity
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Differentiating a strictly separated inverse-width series

Strict room in the positive inverse branch controls one degree of the
scaled Lagrange coefficients.  This file uses that room uniformly on a
small coordinate line, and hence justifies differentiating the full
positive and negative inverse branches term by term.
-/

set_option warningAsError false

open Filter Metric Set
open scoped BigOperators Topology

namespace Erdos1038

noncomputable section

private lemma inverseMonomial_antitone_coordinates
    {iota : Type*} [Fintype iota]
    (gamma d e : iota → ℝ)
    (hgamma : ∀ i, 0 ≤ gamma i)
    (hd : d ∈ positiveCoordinates iota)
    (hde : ∀ i, d i ≤ e i) :
    inverseMonomial gamma e ≤ inverseMonomial gamma d := by
  unfold inverseMonomial
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply Finset.sum_le_sum
  intro i _hi
  exact mul_le_mul_of_nonneg_left
    (Real.strictMonoOn_log.monotoneOn (hd i)
      ((hd i).trans_le (hde i)) (hde i)) (hgamma i)

private lemma scaledLagrangeCoefficient_antitone_coordinates
    {iota : Type*} [Fintype iota]
    (alpha d e : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (hd : d ∈ positiveCoordinates iota)
    (hde : ∀ i, d i ≤ e i) (degree : ℕ) :
    scaledLagrangeCoefficient alpha degree e ≤
      scaledLagrangeCoefficient alpha degree d := by
  classical
  by_cases hdegree : degree = 0
  · subst degree
    have he : e ∈ positiveCoordinates iota := fun i ↦
      (hd i).trans_le (hde i)
    rw [scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow alpha e he 0,
      scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow alpha d hd 0,
      PowerSeries.coeff_zero_lagrangeInversePowerSeries]
    simp
  unfold scaledLagrangeCoefficient scaledLagrangeTerm
  apply Finset.sum_le_sum
  intro r hr
  have hgamma := lagrangeExponent_nonneg alpha
    (fun i ↦ (halpha i).le) degree r
  have hmono := inverseMonomial_antitone_coordinates
    (lagrangeExponent alpha degree r) d e hgamma hd hde
  exact mul_le_mul_of_nonneg_left hmono
    (scaledLagrangePrefactor_pos alpha halpha
      (Nat.pos_of_ne_zero hdegree) r).le

private lemma hasDerivAt_scaledLagrangeCoefficient_line_at
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ) (degree : ℕ)
    {t : ℝ}
    (ht : AffineMap.lineMap (k := ℝ) reference target t ∈
      positiveCoordinates iota) :
    HasDerivAt
      (scaledLagrangeCoefficient alpha degree ∘
        AffineMap.lineMap (k := ℝ) reference target)
      (scaledLagrangeCoefficientDirectional alpha degree
        (AffineMap.lineMap (k := ℝ) reference target t)
        (AffineMap.lineMap (k := ℝ) reference target (t + 1))) t := by
  let line := AffineMap.lineMap (k := ℝ) reference target
  have hlocal := hasDerivAt_scaledLagrangeCoefficient_line
    alpha degree
    (reference := line t) (target := line (t + 1)) ht
  have hshift : HasDerivAt (fun u : ℝ ↦ u - t) 1 t := by
    simpa using! (hasDerivAt_id t).sub_const t
  have hlocal' : HasDerivAt
      (scaledLagrangeCoefficient alpha degree ∘
        AffineMap.lineMap (k := ℝ) (line t) (line (t + 1)))
      (scaledLagrangeCoefficientDirectional alpha degree
        (line t) (line (t + 1))) (t - t) := by
    simpa using! hlocal
  have hcomp := hlocal'.comp_sub_const t t
  have hfunction :
      (fun u ↦ (scaledLagrangeCoefficient alpha degree ∘
        AffineMap.lineMap (k := ℝ) (line t) (line (t + 1))) (u - t)) =
      (scaledLagrangeCoefficient alpha degree ∘ line) := by
    funext u
    apply congrArg (scaledLagrangeCoefficient alpha degree)
    funext i
    change (u - t) *
        (((t + 1) * (target i - reference i) + reference i) -
          (t * (target i - reference i) + reference i)) +
          (t * (target i - reference i) + reference i) =
      u * (target i - reference i) + reference i
    ring
  rw [hfunction] at hcomp
  exact hcomp

private lemma abs_line_relative_velocity_le_sum
    {iota : Type*} [Fintype iota]
    (reference target lower : iota → ℝ) {t : ℝ}
    (hlower : lower ∈ positiveCoordinates iota)
    (hlt : ∀ i, lower i ≤
      AffineMap.lineMap (k := ℝ) reference target t i) (i : iota) :
    |(AffineMap.lineMap (k := ℝ) reference target (t + 1) i -
          AffineMap.lineMap (k := ℝ) reference target t i) /
        AffineMap.lineMap (k := ℝ) reference target t i| ≤
      ∑ j, |target j - reference j| / lower j := by
  let line := AffineMap.lineMap (k := ℝ) reference target
  have htpos : 0 < line t i := (hlower i).trans_le (hlt i)
  have htermNonneg (j : iota) :
      0 ≤ |target j - reference j| / lower j :=
    div_nonneg (abs_nonneg _) (hlower j).le
  have hsingle : |target i - reference i| / lower i ≤
      ∑ j, |target j - reference j| / lower j :=
    Finset.single_le_sum (fun j _hj ↦ htermNonneg j) (Finset.mem_univ i)
  calc
    |(line (t + 1) i - line t i) / line t i| =
        |target i - reference i| / line t i := by
      rw [abs_div, abs_of_pos htpos]
      congr 1
      change |((t + 1) * (target i - reference i) + reference i) -
          (t * (target i - reference i) + reference i)| =
        |target i - reference i|
      congr 1
      ring
    _ ≤ |target i - reference i| / lower i := by
      exact div_le_div_of_nonneg_left (abs_nonneg _)
        (hlower i) (hlt i)
    _ ≤ ∑ j, |target j - reference j| / lower j := hsingle

private lemma directional_coefficient_degree_majorant
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (href : reference ∈ positiveCoordinates iota)
    {degree : ℕ} (hdegree : 0 < degree)
    {B : ℝ} (hB : 0 ≤ B)
    (hratio : ∀ i,
      |(target i - reference i) / reference i| ≤ B) :
    |scaledLagrangeCoefficientDirectional alpha degree
        reference target| ≤
      (B * ((∑ i, alpha i) + 1)) *
        (((degree : ℝ) + 1) *
          scaledLagrangeCoefficient alpha degree reference) := by
  have hraw := abs_scaledLagrangeCoefficientDirectional_le
    alpha reference target halpha hdegree hratio
  have hsumAlpha : 0 ≤ ∑ i, alpha i :=
    Finset.sum_nonneg fun i _hi ↦ (halpha i).le
  have hcoeff := scaledLagrangeCoefficient_nonneg
    alpha reference halpha href degree
  have hsub : ((degree - 1 : ℕ) : ℝ) ≤ degree := by
    exact_mod_cast Nat.sub_le degree 1
  have hdegreeBound :
      (degree : ℝ) * (∑ i, alpha i) + (degree - 1 : ℕ) ≤
        ((∑ i, alpha i) + 1) * ((degree : ℝ) + 1) := by
    nlinarith
  calc
    |scaledLagrangeCoefficientDirectional alpha degree reference target| ≤
        B * ((degree : ℝ) * (∑ i, alpha i) + (degree - 1 : ℕ)) *
          scaledLagrangeCoefficient alpha degree reference := hraw
    _ ≤ (B * ((∑ i, alpha i) + 1) * ((degree : ℝ) + 1)) *
          scaledLagrangeCoefficient alpha degree reference := by
      have hconstant :
          B * ((degree : ℝ) * (∑ i, alpha i) + (degree - 1 : ℕ)) ≤
            B * ((∑ i, alpha i) + 1) * ((degree : ℝ) + 1) := by
        calc
          B * ((degree : ℝ) * (∑ i, alpha i) + (degree - 1 : ℕ)) ≤
              B * (((∑ i, alpha i) + 1) * ((degree : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hdegreeBound hB
          _ = B * ((∑ i, alpha i) + 1) * ((degree : ℝ) + 1) := by ring
      exact mul_le_mul_of_nonneg_right
        hconstant hcoeff
    _ = (B * ((∑ i, alpha i) + 1)) *
        (((degree : ℝ) + 1) *
          scaledLagrangeCoefficient alpha degree reference) := by ring

private lemma exists_strict_lower_scale
    {iota : Type*} [Fintype iota]
    (alpha reference : iota → ℝ)
    {s : ℝ} (hsref : ∀ i, s < reference i)
    (hpotential : 0 < Real.log s +
      ∑ i, alpha i * Real.log (reference i - s)) :
    ∃ c < 1, 0 < c ∧ (∀ i, s < c * reference i) ∧
      0 < Real.log s +
        ∑ i, alpha i * Real.log (c * reference i - s) := by
  let potential : ℝ → ℝ := fun c ↦ Real.log s +
    ∑ i, alpha i * Real.log (c * reference i - s)
  have hcontinuous : ContinuousAt potential 1 := by
    have hsum := HasDerivAt.sum (u := Finset.univ) fun i _hi ↦ by
      have hlinear : HasDerivAt
          (fun c : ℝ ↦ c * reference i - s) (reference i) 1 := by
        convert! ((hasDerivAt_id 1).mul_const (reference i)).sub_const s using 1
        ring
      have hgap : 1 * reference i - s ≠ 0 :=
        sub_ne_zero.mpr (by simpa using! ne_of_gt (hsref i))
      exact (hlinear.log hgap).const_mul (alpha i)
    have hc := (hsum.const_add (Real.log s)).continuousAt
    convert! hc using 1
    funext c
    simp only [potential, Finset.sum_apply]
  have hpotentialOne : 0 < potential 1 := by
    simpa only [potential, one_mul] using! hpotential
  have heventPotential : ∀ᶠ c in nhds (1 : ℝ), 0 < potential c :=
    hcontinuous.eventually (Ioi_mem_nhds hpotentialOne)
  have heventPos : ∀ᶠ c in nhds (1 : ℝ), 0 < c :=
    Ioi_mem_nhds zero_lt_one
  have heventGap : ∀ᶠ c in nhds (1 : ℝ),
      ∀ i, s < c * reference i := by
    rw [eventually_all]
    intro i
    have hcontinuousCoordinate : ContinuousAt
        (fun c : ℝ ↦ c * reference i) 1 :=
      continuousAt_id.mul_const (reference i)
    have hvalue : s < (fun c : ℝ ↦ c * reference i) 1 := by
      simpa using! hsref i
    exact hcontinuousCoordinate.eventually (Ioi_mem_nhds hvalue)
  obtain ⟨c, hc, hcpos, hcgap, hcpotential⟩ :=
    (heventPos.and (heventGap.and heventPotential)).exists_lt
  exact ⟨c, hc, hcpos, hcgap, by simpa only [potential] using! hcpotential⟩

private lemma hasDerivAt_tsum_scaledLagrangeCoefficient_line
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (href : reference ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsref : ∀ i, s < reference i)
    (hpotential : 0 < Real.log s +
      ∑ i, alpha i * Real.log (reference i - s))
    (sign : ℝ) (hsign : |sign| ≤ 1) :
    HasDerivAt
      (fun t ↦ ∑' degree : ℕ,
        sign ^ degree * scaledLagrangeCoefficient alpha degree
          (AffineMap.lineMap (k := ℝ) reference target t))
      (∑' degree : ℕ,
        sign ^ degree * scaledLagrangeCoefficientDirectional alpha degree
          reference target) 0 := by
  classical
  obtain ⟨c, hc, hcpos, hcgap, hcpotential⟩ :=
    exists_strict_lower_scale alpha reference hsref hpotential
  let lower : iota → ℝ := fun i ↦ c * reference i
  let line := AffineMap.lineMap (k := ℝ) reference target
  have hlower : lower ∈ positiveCoordinates iota := by
    intro i
    exact mul_pos hcpos (href i)
  have hstrictLower : inverseMonomial alpha lower <
      s / lagrangePhiValue alpha lower s :=
    inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
      alpha lower hlower hs hcgap hcpotential
  have hweighted : Summable (fun degree : ℕ ↦
      ((degree : ℝ) + 1) *
        scaledLagrangeCoefficient alpha degree lower) :=
    summable_degreeWeight_scaledLagrangeCoefficient_of_lt_comparison
      alpha lower halpha hlower hs hcgap hstrictLower
  let B : ℝ := ∑ i, |target i - reference i| / lower i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _hi ↦
    div_nonneg (abs_nonneg _) (hlower i).le
  let K : ℝ := B * ((∑ i, alpha i) + 1)
  let majorant : ℕ → ℝ := fun degree ↦
    K * (((degree : ℝ) + 1) *
      scaledLagrangeCoefficient alpha degree lower)
  have hmajorant : Summable majorant := by
    exact hweighted.mul_left K
  have heventLower : ∀ᶠ t in nhds (0 : ℝ),
      ∀ i, lower i < line t i := by
    rw [eventually_all]
    intro i
    have hcontinuous :=
      (hasDerivAt_lineMap_coordinate reference target i).continuousAt
    have hzero : lower i < line 0 i := by
      simp only [lower, line, AffineMap.lineMap_apply_zero]
      nlinarith [href i]
    exact hcontinuous.eventually (Ioi_mem_nhds hzero)
  rw [Metric.eventually_nhds_iff] at heventLower
  obtain ⟨epsilon, hepsilon, hball⟩ := heventLower
  have hderiv (degree : ℕ) (t : ℝ) (ht : t ∈ ball 0 epsilon) :
      HasDerivAt
        (fun u ↦ sign ^ degree *
          scaledLagrangeCoefficient alpha degree (line u))
        (sign ^ degree * scaledLagrangeCoefficientDirectional alpha degree
          (line t) (line (t + 1))) t := by
    have htLower := hball ht
    have htpos : line t ∈ positiveCoordinates iota := fun i ↦
      (hlower i).trans (htLower i)
    exact (hasDerivAt_scaledLagrangeCoefficient_line_at
      alpha reference target degree htpos).const_mul (sign ^ degree)
  have hbound (degree : ℕ) (t : ℝ) (ht : t ∈ ball 0 epsilon) :
      ‖sign ^ degree * scaledLagrangeCoefficientDirectional alpha degree
          (line t) (line (t + 1))‖ ≤ majorant degree := by
    have htLower := hball ht
    have htpos : line t ∈ positiveCoordinates iota := fun i ↦
      (hlower i).trans (htLower i)
    have hcoordinates : ∀ i, lower i ≤ line t i :=
      fun i ↦ (htLower i).le
    have hcoefficient := scaledLagrangeCoefficient_antitone_coordinates
      alpha lower (line t) halpha hlower hcoordinates degree
    by_cases hdegree : degree = 0
    · subst degree
      have hzeroCoefficient (d : iota → ℝ)
          (hd : d ∈ positiveCoordinates iota) :
          scaledLagrangeCoefficient alpha 0 d = 0 := by
        rw [scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow alpha d hd 0,
          PowerSeries.coeff_zero_lagrangeInversePowerSeries]
        simp
      have hzeroDirectional :
          scaledLagrangeCoefficientDirectional alpha 0
            (line t) (line (t + 1)) = 0 := by
        simp [scaledLagrangeCoefficientDirectional,
          scaledLagrangeTermDirectional, scaledLagrangePrefactor]
      rw [hzeroDirectional, mul_zero, norm_zero]
      simp [majorant, hzeroCoefficient lower hlower]
    · have hdegreePos : 0 < degree := Nat.pos_of_ne_zero hdegree
      have hratio (i : iota) :
          |(line (t + 1) i - line t i) / line t i| ≤ B := by
        exact abs_line_relative_velocity_le_sum reference target lower
          hlower hcoordinates i
      have hdirectional := directional_coefficient_degree_majorant
        alpha (line t) (line (t + 1)) halpha htpos hdegreePos hB hratio
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      have hsignPow : |sign| ^ degree ≤ 1 :=
        pow_le_one₀ (abs_nonneg sign) hsign
      calc
        |sign| ^ degree *
            |scaledLagrangeCoefficientDirectional alpha degree
              (line t) (line (t + 1))| ≤
            |scaledLagrangeCoefficientDirectional alpha degree
              (line t) (line (t + 1))| := by
          exact mul_le_of_le_one_left (abs_nonneg _) hsignPow
        _ ≤ K * (((degree : ℝ) + 1) *
              scaledLagrangeCoefficient alpha degree (line t)) := by
          simpa only [K] using! hdirectional
        _ ≤ K * (((degree : ℝ) + 1) *
              scaledLagrangeCoefficient alpha degree lower) := by
          have hK : 0 ≤ K := mul_nonneg hB (by
            have hsumAlpha : 0 ≤ ∑ i, alpha i :=
              Finset.sum_nonneg fun i _hi ↦ (halpha i).le
            linarith)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hcoefficient (by positivity)) hK
        _ = majorant degree := rfl
  have hrefStrict : inverseMonomial alpha reference <
      s / lagrangePhiValue alpha reference s :=
    inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
      alpha reference href hs hsref hpotential
  have hrefWeighted : Summable (fun degree : ℕ ↦
      ((degree : ℝ) + 1) *
        scaledLagrangeCoefficient alpha degree reference) :=
    summable_degreeWeight_scaledLagrangeCoefficient_of_lt_comparison
      alpha reference halpha href hs hsref hrefStrict
  have hrefSum : Summable (fun degree : ℕ ↦
      sign ^ degree * scaledLagrangeCoefficient alpha degree (line 0)) := by
    have hbase := summable_scaledLagrangeCoefficient_of_degreeWeight
      alpha reference halpha href hrefWeighted
    apply Summable.of_norm_bounded hbase
    intro degree
    simp only [line, AffineMap.lineMap_apply_zero, norm_mul, Real.norm_eq_abs]
    have hsignPow : |sign| ^ degree ≤ 1 :=
      pow_le_one₀ (abs_nonneg sign) hsign
    rw [abs_pow, abs_of_nonneg
      (scaledLagrangeCoefficient_nonneg alpha reference halpha href degree)]
    exact mul_le_of_le_one_left
      (scaledLagrangeCoefficient_nonneg alpha reference halpha href degree)
      hsignPow
  have hsum := hasDerivAt_tsum_of_isPreconnected hmajorant
    isOpen_ball (convex_ball (0 : ℝ) epsilon).isPreconnected
    hderiv hbound (mem_ball_self hepsilon) hrefSum
    (mem_ball_self hepsilon)
  simpa only [line, AffineMap.lineMap_apply_zero, zero_add,
    AffineMap.lineMap_apply_one] using! hsum

/-- The positive inverse branch is differentiable along every material
coordinate line for which the reference has a strict comparison point. -/
theorem hasDerivAt_lagrangeInverseValue_inverseMonomial_line
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (href : reference ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsref : ∀ i, s < reference i)
    (hpotential : 0 < Real.log s +
      ∑ i, alpha i * Real.log (reference i - s)) :
    HasDerivAt
      (fun t ↦ lagrangeInverseValue alpha
        (AffineMap.lineMap (k := ℝ) reference target t)
        (inverseMonomial alpha
          (AffineMap.lineMap (k := ℝ) reference target t)))
      (∑' degree : ℕ,
        scaledLagrangeCoefficientDirectional alpha degree
          reference target) 0 := by
  have hseries := hasDerivAt_tsum_scaledLagrangeCoefficient_line
    alpha reference target halpha href hs hsref hpotential 1 (by norm_num)
  have hpositive : ∀ᶠ t in nhds (0 : ℝ),
      AffineMap.lineMap (k := ℝ) reference target t ∈
        positiveCoordinates iota := by
    change ∀ᶠ t in nhds (0 : ℝ), ∀ i, 0 <
      AffineMap.lineMap (k := ℝ) reference target t i
    rw [eventually_all]
    intro i
    exact (hasDerivAt_lineMap_coordinate reference target i).continuousAt
      |>.eventually (Ioi_mem_nhds (by simpa using! href i))
  have heq : (fun t ↦ lagrangeInverseValue alpha
      (AffineMap.lineMap (k := ℝ) reference target t)
      (inverseMonomial alpha
        (AffineMap.lineMap (k := ℝ) reference target t))) =ᶠ[nhds 0]
      (fun t ↦ ∑' degree : ℕ,
        (1 : ℝ) ^ degree * scaledLagrangeCoefficient alpha degree
          (AffineMap.lineMap (k := ℝ) reference target t)) := by
    filter_upwards [hpositive] with t ht
    simpa only [one_pow, one_mul] using!
      lagrangeInverseValue_inverseMonomial_eq_tsum_scaled alpha
        (AffineMap.lineMap (k := ℝ) reference target t) ht
  simpa only [one_pow, one_mul] using! hseries.congr_of_eventuallyEq heq

/-- The negative inverse branch has the alternating differentiated series. -/
theorem hasDerivAt_lagrangeInverseValue_neg_inverseMonomial_line
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (href : reference ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsref : ∀ i, s < reference i)
    (hpotential : 0 < Real.log s +
      ∑ i, alpha i * Real.log (reference i - s)) :
    HasDerivAt
      (fun t ↦ lagrangeInverseValue alpha
        (AffineMap.lineMap (k := ℝ) reference target t)
        (-inverseMonomial alpha
          (AffineMap.lineMap (k := ℝ) reference target t)))
      (∑' degree : ℕ,
        (-1 : ℝ) ^ degree *
          scaledLagrangeCoefficientDirectional alpha degree
            reference target) 0 := by
  have hseries := hasDerivAt_tsum_scaledLagrangeCoefficient_line
    alpha reference target halpha href hs hsref hpotential (-1) (by norm_num)
  have hpositive : ∀ᶠ t in nhds (0 : ℝ),
      AffineMap.lineMap (k := ℝ) reference target t ∈
        positiveCoordinates iota := by
    change ∀ᶠ t in nhds (0 : ℝ), ∀ i, 0 <
      AffineMap.lineMap (k := ℝ) reference target t i
    rw [eventually_all]
    intro i
    exact (hasDerivAt_lineMap_coordinate reference target i).continuousAt
      |>.eventually (Ioi_mem_nhds (by simpa using! href i))
  have heq : (fun t ↦ lagrangeInverseValue alpha
      (AffineMap.lineMap (k := ℝ) reference target t)
      (-inverseMonomial alpha
        (AffineMap.lineMap (k := ℝ) reference target t))) =ᶠ[nhds 0]
      (fun t ↦ ∑' degree : ℕ,
        (-1 : ℝ) ^ degree * scaledLagrangeCoefficient alpha degree
          (AffineMap.lineMap (k := ℝ) reference target t)) := by
    filter_upwards [hpositive] with t ht
    exact lagrangeInverseValue_neg_inverseMonomial_eq_tsum_signed_scaled
      alpha (AffineMap.lineMap (k := ℝ) reference target t) ht
  exact hseries.congr_of_eventuallyEq heq

/-! ## Implicit root formula -/

/-- Logarithmic exterior potential associated with arbitrary positive
Lagrange weights and coordinates. -/
def lagrangeExteriorPotential {iota : Type*} [Fintype iota]
    (alpha d : iota → ℝ) (x : ℝ) : ℝ :=
  Real.log |x| + ∑ i, alpha i * Real.log (d i - x)

/-- Spatial derivative of `lagrangeExteriorPotential` away from its poles. -/
def lagrangeExteriorPotentialXDerivative
    {iota : Type*} [Fintype iota]
    (alpha d : iota → ℝ) (x : ℝ) : ℝ :=
  1 / x - ∑ i, alpha i / (d i - x)

/-- Material derivative of the exterior potential at a fixed spatial point. -/
def lagrangeExteriorPotentialMaterialVelocity
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ) (x : ℝ) : ℝ :=
  ∑ i, alpha i * (target i - reference i) / (reference i - x)

private theorem lagrangeExteriorPotential_eq_zero_of_abs_fixedPoint
    {iota : Type*} [Fintype iota]
    (alpha d : iota → ℝ)
    (hd : d ∈ positiveCoordinates iota) {x : ℝ}
    (hxd : ∀ i, x < d i)
    (hfixed : |x| = inverseMonomial alpha d * lagrangePhiValue alpha d x) :
    lagrangeExteriorPotential alpha d x = 0 := by
  rw [lagrangeExteriorPotential, hfixed,
    inverseMonomial_mul_lagrangePhiValue_eq_exp_logGap alpha d hxd hd,
    Real.log_exp]
  ring

private theorem eventually_lagrangeInverseBranches_exteriorPotential_zero
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (href : reference ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsref : ∀ i, s < reference i)
    (hpotential : 0 < Real.log s +
      ∑ i, alpha i * Real.log (reference i - s)) :
    ∀ᶠ t in nhds (0 : ℝ),
      lagrangeExteriorPotential alpha
          (AffineMap.lineMap (k := ℝ) reference target t)
          (lagrangeInverseValue alpha
            (AffineMap.lineMap (k := ℝ) reference target t)
            (inverseMonomial alpha
              (AffineMap.lineMap (k := ℝ) reference target t))) = 0 ∧
        lagrangeExteriorPotential alpha
          (AffineMap.lineMap (k := ℝ) reference target t)
          (lagrangeInverseValue alpha
            (AffineMap.lineMap (k := ℝ) reference target t)
            (-inverseMonomial alpha
              (AffineMap.lineMap (k := ℝ) reference target t))) = 0 := by
  let line := AffineMap.lineMap (k := ℝ) reference target
  let comparisonPotential : ℝ → ℝ := fun t ↦ Real.log s +
    ∑ i, alpha i * Real.log (line t i - s)
  have hpositive : ∀ᶠ t in nhds (0 : ℝ),
      line t ∈ positiveCoordinates iota := by
    change ∀ᶠ t in nhds (0 : ℝ), ∀ i, 0 < line t i
    rw [eventually_all]
    intro i
    exact (hasDerivAt_lineMap_coordinate reference target i).continuousAt
      |>.eventually (Ioi_mem_nhds (by simpa only [line,
        AffineMap.lineMap_apply_zero] using! href i))
  have hgap : ∀ᶠ t in nhds (0 : ℝ), ∀ i, s < line t i := by
    rw [eventually_all]
    intro i
    exact (hasDerivAt_lineMap_coordinate reference target i).continuousAt
      |>.eventually (Ioi_mem_nhds (by simpa only [line,
        AffineMap.lineMap_apply_zero] using! hsref i))
  have hcomparisonContinuous : ContinuousAt comparisonPotential 0 := by
    have hsum := HasDerivAt.sum (u := Finset.univ) fun i _hi ↦ by
      have hcoordinate := hasDerivAt_lineMap_coordinate reference target i
      have hlog := (hcoordinate.sub_const s).log (by
        simpa only [line, AffineMap.lineMap_apply_zero, sub_ne_zero]
          using! (ne_of_gt (hsref i)))
      exact hlog.const_mul (alpha i)
    have hc := (hsum.const_add (Real.log s)).continuousAt
    convert! hc using 1
    funext t
    simp only [comparisonPotential, line, Finset.sum_apply]
  have hcomparisonZero : 0 < comparisonPotential 0 := by
    simpa only [comparisonPotential, line, AffineMap.lineMap_apply_zero]
      using! hpotential
  have hcomparison : ∀ᶠ t in nhds (0 : ℝ),
      0 < comparisonPotential t :=
    hcomparisonContinuous.eventually (Ioi_mem_nhds hcomparisonZero)
  filter_upwards [hpositive, hgap, hcomparison] with t htpos hts htp
  let d := line t
  let z := inverseMonomial alpha d
  let Wplus := lagrangeInverseValue alpha d z
  let Wminus := lagrangeInverseValue alpha d (-z)
  have hz : 0 < z := inverseMonomial_pos alpha d
  have hstrict : z < s / lagrangePhiValue alpha d s := by
    apply inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
      alpha d htpos hs hts
    simpa only [comparisonPotential, d, line] using! htp
  have hsum := summable_lagrangeInversePowerSeries_of_lt
    alpha d halpha htpos hs hts hz.le hstrict
  have hplusLt : Wplus < s := by
    exact lagrangeInverseValue_lt_comparison
      alpha d halpha htpos hs hts hz.le hstrict
  have hplusD (i : iota) : Wplus < d i := hplusLt.trans (hts i)
  have hplusFixed : Wplus = z * lagrangePhiValue alpha d Wplus :=
    lagrangeInverseValue_fixedPoint_of_lt
      alpha d halpha htpos hs hts hz.le hstrict
  have hplusPhi : 0 < lagrangePhiValue alpha d Wplus :=
    lagrangePhiValue_pos alpha d htpos hplusD
  have hplusPos : 0 < Wplus := by
    rw [hplusFixed]
    exact mul_pos hz hplusPhi
  have hplusAbsFixed :
      |Wplus| = inverseMonomial alpha d * lagrangePhiValue alpha d Wplus := by
    rw [abs_of_pos hplusPos]
    exact hplusFixed
  have hplusZero : lagrangeExteriorPotential alpha d Wplus = 0 :=
    lagrangeExteriorPotential_eq_zero_of_abs_fixedPoint
      alpha d htpos hplusD hplusAbsFixed
  have hminusFixed : Wminus =
      (-z) * lagrangePhiValue alpha d Wminus :=
    (lagrangeInverseValue_neg_fixedPoint_of_pos_summable
      alpha d halpha htpos hz.le hsum hplusD).2
  have hminusAbs : |Wminus| ≤ Wplus := by
    exact abs_lagrangeInverseValue_neg_le_pos
      alpha d halpha htpos hz.le hsum
  have hminusD (i : iota) : Wminus < d i :=
    (le_abs_self Wminus).trans hminusAbs |>.trans_lt (hplusD i)
  have hminusPhi : 0 < lagrangePhiValue alpha d Wminus :=
    lagrangePhiValue_pos alpha d htpos hminusD
  have hminusNeg : Wminus < 0 := by
    rw [hminusFixed]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos hz) hminusPhi
  have hminusAbsFixed :
      |Wminus| = inverseMonomial alpha d *
        lagrangePhiValue alpha d Wminus := by
    have hnegated : -Wminus =
        z * lagrangePhiValue alpha d Wminus := by
      linarith [hminusFixed]
    calc
      |Wminus| = -Wminus := abs_of_neg hminusNeg
      _ = z * lagrangePhiValue alpha d Wminus := hnegated
      _ = inverseMonomial alpha d * lagrangePhiValue alpha d Wminus := rfl
  have hminusZero : lagrangeExteriorPotential alpha d Wminus = 0 :=
    lagrangeExteriorPotential_eq_zero_of_abs_fixedPoint
      alpha d htpos hminusD hminusAbsFixed
  exact ⟨by simpa only [d, z, Wplus, line] using! hplusZero,
    by simpa only [d, z, Wminus, line] using! hminusZero⟩

private theorem hasDerivAt_log_abs_local {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.log |y|) (1 / x) x := by
  rcases hx.lt_or_gt with hneg | hpos
  · convert! (Real.hasDerivAt_log (abs_ne_zero.mpr hx)).comp x
      (hasDerivAt_abs_neg hneg) using 1
    rw [abs_of_neg hneg]
    field_simp
  · convert! (Real.hasDerivAt_log (abs_ne_zero.mpr hx)).comp x
      (hasDerivAt_abs_pos hpos) using 1
    rw [abs_of_pos hpos]
    simp [div_eq_mul_inv]

private theorem hasDerivAt_lagrangeExteriorPotential_line
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    {W : ℝ → ℝ} {W' : ℝ}
    (hW : HasDerivAt W W' 0) (hWne : W 0 ≠ 0)
    (hWd : ∀ i, W 0 < reference i) :
    HasDerivAt
      (fun t ↦ lagrangeExteriorPotential alpha
        (AffineMap.lineMap (k := ℝ) reference target t) (W t))
      (lagrangeExteriorPotentialMaterialVelocity alpha reference target (W 0) +
        W' * lagrangeExteriorPotentialXDerivative alpha reference (W 0)) 0 := by
  have hlogAbs := (hasDerivAt_log_abs_local hWne).comp 0 hW
  have hsum := HasDerivAt.sum (u := Finset.univ) fun i _hi ↦ by
    have hgap := (hasDerivAt_lineMap_coordinate reference target i).sub hW
    have hgapNe :
        ((fun t ↦ AffineMap.lineMap (k := ℝ) reference target t i) - W) 0 ≠
          0 := by
      simp only [Pi.sub_apply, AffineMap.lineMap_apply_zero]
      exact sub_ne_zero.mpr (ne_of_gt (hWd i))
    have hlog := hgap.log hgapNe
    exact hlog.const_mul (alpha i)
  have hraw := hlogAbs.add hsum
  have hraw' : HasDerivAt
      (fun t ↦ lagrangeExteriorPotential alpha
        (AffineMap.lineMap (k := ℝ) reference target t) (W t))
      (1 / W 0 * W' + ∑ i, alpha i *
        ((target i - reference i) - W') / (reference i - W 0)) 0 := by
    convert! hraw using 1
    · funext t
      simp only [lagrangeExteriorPotential, Function.comp_apply,
        Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
    · simp only [Pi.sub_apply, AffineMap.lineMap_apply_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      ring
  let M := lagrangeExteriorPotentialMaterialVelocity
    alpha reference target (W 0)
  let S := ∑ i, alpha i / (reference i - W 0)
  have hsplit :
      (∑ i, alpha i *
        ((target i - reference i) - W') / (reference i - W 0)) =
        M - W' * S := by
    change (∑ i, alpha i *
        ((target i - reference i) - W') / (reference i - W 0)) =
      (∑ i, alpha i * (target i - reference i) /
        (reference i - W 0)) -
        W' * ∑ i, alpha i / (reference i - W 0)
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  convert! hraw' using 1
  change M + W' * (1 / W 0 - S) =
    1 / W 0 * W' + ∑ i, alpha i *
      ((target i - reference i) - W') / (reference i - W 0)
  rw [hsplit]
  ring

/-- At a nondegenerate positive inverse root, the derivative of the full
positive inverse series is the material potential velocity divided by the
negative spatial slope. -/
theorem tsum_scaledLagrangeCoefficientDirectional_eq_rootVelocity_pos
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (href : reference ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsref : ∀ i, s < reference i)
    (hpotential : 0 < Real.log s +
      ∑ i, alpha i * Real.log (reference i - s))
    (hderivative : lagrangeExteriorPotentialXDerivative alpha reference
      (lagrangeInverseValue alpha reference
        (inverseMonomial alpha reference)) ≠ 0) :
    (∑' degree : ℕ,
      scaledLagrangeCoefficientDirectional alpha degree reference target) =
      -lagrangeExteriorPotentialMaterialVelocity alpha reference target
          (lagrangeInverseValue alpha reference
            (inverseMonomial alpha reference)) /
        lagrangeExteriorPotentialXDerivative alpha reference
          (lagrangeInverseValue alpha reference
            (inverseMonomial alpha reference)) := by
  let W : ℝ → ℝ := fun t ↦ lagrangeInverseValue alpha
    (AffineMap.lineMap (k := ℝ) reference target t)
    (inverseMonomial alpha
      (AffineMap.lineMap (k := ℝ) reference target t))
  let W' := ∑' degree : ℕ,
    scaledLagrangeCoefficientDirectional alpha degree reference target
  have hW : HasDerivAt W W' 0 := by
    simpa only [W, W'] using!
      hasDerivAt_lagrangeInverseValue_inverseMonomial_line
        alpha reference target halpha href hs hsref hpotential
  have hstrict := inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
    alpha reference href hs hsref hpotential
  have hWlt : W 0 < s := by
    simpa only [W, AffineMap.lineMap_apply_zero] using!
      lagrangeInverseValue_lt_comparison alpha reference halpha href
        hs hsref (inverseMonomial_pos alpha reference).le hstrict
  have hWd (i : iota) : W 0 < reference i := hWlt.trans (hsref i)
  have hfixed : W 0 = inverseMonomial alpha reference *
      lagrangePhiValue alpha reference (W 0) := by
    simpa only [W, AffineMap.lineMap_apply_zero] using!
      lagrangeInverseValue_fixedPoint_of_lt alpha reference halpha href
        hs hsref (inverseMonomial_pos alpha reference).le hstrict
  have hWpos : 0 < W 0 := by
    rw [hfixed]
    exact mul_pos (inverseMonomial_pos alpha reference)
      (lagrangePhiValue_pos alpha reference href hWd)
  have hP := hasDerivAt_lagrangeExteriorPotential_line
    alpha reference target hW hWpos.ne' hWd
  have hzeroEvent :=
    eventually_lagrangeInverseBranches_exteriorPotential_zero
      alpha reference target halpha href hs hsref hpotential
  have hPzero : HasDerivAt
      (fun t ↦ lagrangeExteriorPotential alpha
        (AffineMap.lineMap (k := ℝ) reference target t) (W t)) 0 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [hzeroEvent] with t ht
    simpa only [W] using! ht.1
  have hequation := hP.unique hPzero
  have hderivative' : lagrangeExteriorPotentialXDerivative alpha reference
      (W 0) ≠ 0 := by
    simpa only [W, AffineMap.lineMap_apply_zero] using! hderivative
  have hformula : W' =
      -lagrangeExteriorPotentialMaterialVelocity alpha reference target (W 0) /
        lagrangeExteriorPotentialXDerivative alpha reference (W 0) := by
    field_simp [hderivative'] at hequation ⊢
    linarith
  simpa only [W', W, AffineMap.lineMap_apply_zero] using! hformula

/-- The analogous formula for the alternating negative inverse branch. -/
theorem tsum_signed_scaledLagrangeCoefficientDirectional_eq_rootVelocity_neg
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (href : reference ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsref : ∀ i, s < reference i)
    (hpotential : 0 < Real.log s +
      ∑ i, alpha i * Real.log (reference i - s))
    (hderivative : lagrangeExteriorPotentialXDerivative alpha reference
      (lagrangeInverseValue alpha reference
        (-inverseMonomial alpha reference)) ≠ 0) :
    (∑' degree : ℕ, (-1 : ℝ) ^ degree *
      scaledLagrangeCoefficientDirectional alpha degree reference target) =
      -lagrangeExteriorPotentialMaterialVelocity alpha reference target
          (lagrangeInverseValue alpha reference
            (-inverseMonomial alpha reference)) /
        lagrangeExteriorPotentialXDerivative alpha reference
          (lagrangeInverseValue alpha reference
            (-inverseMonomial alpha reference)) := by
  let W : ℝ → ℝ := fun t ↦ lagrangeInverseValue alpha
    (AffineMap.lineMap (k := ℝ) reference target t)
    (-inverseMonomial alpha
      (AffineMap.lineMap (k := ℝ) reference target t))
  let W' := ∑' degree : ℕ, (-1 : ℝ) ^ degree *
    scaledLagrangeCoefficientDirectional alpha degree reference target
  have hW : HasDerivAt W W' 0 := by
    simpa only [W, W'] using!
      hasDerivAt_lagrangeInverseValue_neg_inverseMonomial_line
        alpha reference target halpha href hs hsref hpotential
  have hstrict := inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
    alpha reference href hs hsref hpotential
  have hsum := summable_lagrangeInversePowerSeries_of_lt
    alpha reference halpha href hs hsref
      (inverseMonomial_pos alpha reference).le hstrict
  let Wplus := lagrangeInverseValue alpha reference
    (inverseMonomial alpha reference)
  have hplusLt : Wplus < s :=
    lagrangeInverseValue_lt_comparison alpha reference halpha href
      hs hsref (inverseMonomial_pos alpha reference).le hstrict
  have hplusD (i : iota) : Wplus < reference i := hplusLt.trans (hsref i)
  have hminusAbs : |W 0| ≤ Wplus := by
    simpa only [W, AffineMap.lineMap_apply_zero] using!
      abs_lagrangeInverseValue_neg_le_pos alpha reference halpha href
        (inverseMonomial_pos alpha reference).le hsum
  have hWd (i : iota) : W 0 < reference i :=
    (le_abs_self (W 0)).trans hminusAbs |>.trans_lt (hplusD i)
  have hfixed : W 0 = (-inverseMonomial alpha reference) *
      lagrangePhiValue alpha reference (W 0) := by
    simpa only [W, AffineMap.lineMap_apply_zero] using!
      (lagrangeInverseValue_neg_fixedPoint_of_pos_summable
        alpha reference halpha href
          (inverseMonomial_pos alpha reference).le hsum hplusD).2
  have hWneg : W 0 < 0 := by
    rw [hfixed]
    exact mul_neg_of_neg_of_pos
      (neg_neg_of_pos (inverseMonomial_pos alpha reference))
      (lagrangePhiValue_pos alpha reference href hWd)
  have hP := hasDerivAt_lagrangeExteriorPotential_line
    alpha reference target hW hWneg.ne hWd
  have hzeroEvent :=
    eventually_lagrangeInverseBranches_exteriorPotential_zero
      alpha reference target halpha href hs hsref hpotential
  have hPzero : HasDerivAt
      (fun t ↦ lagrangeExteriorPotential alpha
        (AffineMap.lineMap (k := ℝ) reference target t) (W t)) 0 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [hzeroEvent] with t ht
    simpa only [W] using! ht.2
  have hequation := hP.unique hPzero
  have hderivative' : lagrangeExteriorPotentialXDerivative alpha reference
      (W 0) ≠ 0 := by
    simpa only [W, AffineMap.lineMap_apply_zero] using! hderivative
  have hformula : W' =
      -lagrangeExteriorPotentialMaterialVelocity alpha reference target (W 0) /
        lagrangeExteriorPotentialXDerivative alpha reference (W 0) := by
    field_simp [hderivative'] at hequation ⊢
    linarith
  simpa only [W', W, AffineMap.lineMap_apply_zero] using! hformula

private theorem summable_scaledLagrangeCoefficientDirectional_full_of_strict
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (href : reference ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsref : ∀ i, s < reference i)
    (hpotential : 0 < Real.log s +
      ∑ i, alpha i * Real.log (reference i - s)) :
    Summable (fun degree : ℕ ↦
      scaledLagrangeCoefficientDirectional alpha degree reference target) := by
  have hstrict := inverseMonomial_lt_div_lagrangePhiValue_of_logPotential_pos
    alpha reference href hs hsref hpotential
  have hweighted : Summable (fun degree : ℕ ↦
      ((degree : ℝ) + 1) *
        scaledLagrangeCoefficient alpha degree reference) :=
    summable_degreeWeight_scaledLagrangeCoefficient_of_lt_comparison
      alpha reference halpha href hs hsref hstrict
  let B : ℝ := ∑ i, |target i - reference i| / reference i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _hi ↦
    div_nonneg (abs_nonneg _) (href i).le
  let K : ℝ := B * ((∑ i, alpha i) + 1)
  have hmajor : Summable (fun degree : ℕ ↦
      K * (((degree : ℝ) + 1) *
        scaledLagrangeCoefficient alpha degree reference)) :=
    hweighted.mul_left K
  apply Summable.of_norm_bounded hmajor
  intro degree
  rw [Real.norm_eq_abs]
  by_cases hdegree : degree = 0
  · subst degree
    have hcoefficientZero :
        scaledLagrangeCoefficient alpha 0 reference = 0 := by
      rw [scaledLagrangeCoefficient_eq_inverseCoeff_mul_pow
        alpha reference href 0,
        PowerSeries.coeff_zero_lagrangeInversePowerSeries]
      simp
    rw [hcoefficientZero]
    simp [scaledLagrangeCoefficientDirectional,
      scaledLagrangeTermDirectional, scaledLagrangePrefactor]
  · have hdegreePos := Nat.pos_of_ne_zero hdegree
    have hratio (i : iota) :
        |(target i - reference i) / reference i| ≤ B := by
      rw [abs_div, abs_of_pos (href i)]
      change |target i - reference i| / reference i ≤
        ∑ j, |target j - reference j| / reference j
      exact Finset.single_le_sum
        (fun j _hj ↦ div_nonneg
          (abs_nonneg (target j - reference j)) (href j).le)
        (Finset.mem_univ i)
    simpa only [K] using! directional_coefficient_degree_majorant
      alpha reference target halpha href hdegreePos hB hratio

private theorem tsum_sub_signed_eq_two_mul_tsum_odd
    (coefficient : ℕ → ℝ) (hsum : Summable coefficient) :
    (∑' n, coefficient n) -
        (∑' n, (-1 : ℝ) ^ n * coefficient n) =
      2 * ∑' j, coefficient (2 * j + 1) := by
  have hinjEven : Function.Injective (fun j : ℕ ↦ 2 * j) := by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by omega) hmn
  have hinjOdd : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := by
    intro m n hmn
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel hmn)
  have hEven : Summable (fun j ↦ coefficient (2 * j)) := by
    simpa only [Function.comp_apply] using! hsum.comp_injective hinjEven
  have hOdd : Summable (fun j ↦ coefficient (2 * j + 1)) := by
    simpa only [Function.comp_apply] using! hsum.comp_injective hinjOdd
  let signed : ℕ → ℝ := fun n ↦ (-1 : ℝ) ^ n * coefficient n
  have hSignedEven : Summable (fun j ↦ signed (2 * j)) := by
    simpa only [signed, pow_mul, neg_one_sq, one_pow, one_mul] using! hEven
  have hSignedOdd : Summable (fun j ↦ signed (2 * j + 1)) := by
    simpa [signed, pow_add, pow_mul] using! hOdd.neg
  have hsplit :
      (∑' j, coefficient (2 * j)) +
          (∑' j, coefficient (2 * j + 1)) =
        ∑' n, coefficient n :=
    tsum_even_add_odd hEven hOdd
  have hsplitSigned :
      (∑' j, signed (2 * j)) + (∑' j, signed (2 * j + 1)) =
        ∑' n, signed n :=
    tsum_even_add_odd hSignedEven hSignedOdd
  have hsignedEven :
      (∑' j, signed (2 * j)) = ∑' j, coefficient (2 * j) := by
    apply tsum_congr
    intro j
    simp [signed, pow_mul]
  have hsignedOdd :
      (∑' j, signed (2 * j + 1)) =
        -∑' j, coefficient (2 * j + 1) := by
    rw [← tsum_neg]
    apply tsum_congr
    intro j
    simp [signed, pow_add, pow_mul]
  rw [← hsplit, ← hsplitSigned, hsignedEven, hsignedOdd]
  ring

/-- Material velocity predicted by the two nondegenerate inverse roots. -/
def lagrangeInverseWidthRootVelocity
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ) : ℝ :=
  let Wplus := lagrangeInverseValue alpha reference
    (inverseMonomial alpha reference)
  let Wminus := lagrangeInverseValue alpha reference
    (-inverseMonomial alpha reference)
  (-lagrangeExteriorPotentialMaterialVelocity alpha reference target Wplus /
      lagrangeExteriorPotentialXDerivative alpha reference Wplus +
    lagrangeExteriorPotentialMaterialVelocity alpha reference target Wminus /
      lagrangeExteriorPotentialXDerivative alpha reference Wminus)

/-- Exact finite implicit-root formula for the material inverse-width
series.  This is the bridge from coefficient differentiation to the two
zero-potential crossings. -/
theorem inverseWidthSeriesDirectional_eq_rootVelocity
    {iota : Type*} [Fintype iota]
    (alpha reference target : iota → ℝ)
    (halpha : ∀ i, 0 < alpha i)
    (href : reference ∈ positiveCoordinates iota)
    {s : ℝ} (hs : 0 < s) (hsref : ∀ i, s < reference i)
    (hpotential : 0 < Real.log s +
      ∑ i, alpha i * Real.log (reference i - s))
    (hplusDerivative : lagrangeExteriorPotentialXDerivative alpha reference
      (lagrangeInverseValue alpha reference
        (inverseMonomial alpha reference)) ≠ 0)
    (hminusDerivative : lagrangeExteriorPotentialXDerivative alpha reference
      (lagrangeInverseValue alpha reference
        (-inverseMonomial alpha reference)) ≠ 0) :
    inverseWidthSeriesDirectional alpha reference target =
      lagrangeInverseWidthRootVelocity alpha reference target := by
  let coefficient : ℕ → ℝ := fun degree ↦
    scaledLagrangeCoefficientDirectional alpha degree reference target
  have hsum : Summable coefficient := by
    simpa only [coefficient] using!
      summable_scaledLagrangeCoefficientDirectional_full_of_strict
        alpha reference target halpha href hs hsref hpotential
  have hparity := tsum_sub_signed_eq_two_mul_tsum_odd coefficient hsum
  have hplus :=
    tsum_scaledLagrangeCoefficientDirectional_eq_rootVelocity_pos
      alpha reference target halpha href hs hsref hpotential hplusDerivative
  have hminus :=
    tsum_signed_scaledLagrangeCoefficientDirectional_eq_rootVelocity_neg
      alpha reference target halpha href hs hsref hpotential hminusDerivative
  rw [inverseWidthSeriesDirectional]
  rw [← hparity]
  simp only [coefficient] at hplus hminus ⊢
  rw [hplus, hminus]
  unfold lagrangeInverseWidthRootVelocity
  ring

end

end Erdos1038
