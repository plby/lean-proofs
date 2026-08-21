import ErdosProblems.Erdos88.GaussianDensityLower
import ErdosProblems.Erdos88.GaussianMoments

/-!
# The influential-coordinate lower-bound ingredients

This file begins the complementary case in KSSS Theorem 5.2(2).  Its first
result is the one-sided fourth-moment estimate of Lemma 5.9, stated for an
arbitrary probability measure.  It is the input used for the sum of all
coordinates other than the selected influential coordinate.
-/

open MeasureTheory ProbabilityTheory Set

namespace Erdos88.GaussianQuadratic

private lemma oneSidedFourthMoment_polynomial_le_on
    {B x : ℝ} (hB : 1 ≤ B)
    (hx : x ∈ Set.Icc (-2 * Real.sqrt B) 0) :
    -x * (x + 2 * Real.sqrt B) * (x - Real.sqrt B) ^ 2 ≤ 9 * B ^ 2 := by
  have hs0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hsSq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB0
  have hcenter : |x + Real.sqrt B| ≤ Real.sqrt B := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hcenterSq : (x + Real.sqrt B) ^ 2 ≤ B := by
    have hsquare := (sq_le_sq₀ (abs_nonneg (x + Real.sqrt B)) hs0).2 hcenter
    simpa only [sq_abs, hsSq] using hsquare
  have hfirst0 : 0 ≤ B - (x + Real.sqrt B) ^ 2 := by
    linarith
  have hfirst : B - (x + Real.sqrt B) ^ 2 ≤ B := by
    nlinarith [sq_nonneg (x + Real.sqrt B)]
  have hsecond0 : 0 ≤ (x - Real.sqrt B) ^ 2 := sq_nonneg _
  have hsecond : (x - Real.sqrt B) ^ 2 ≤ 9 * B := by
    have habs : |x - Real.sqrt B| ≤ 3 * Real.sqrt B := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hsquare := (sq_le_sq₀ (abs_nonneg (x - Real.sqrt B))
      (mul_nonneg (by norm_num) hs0)).2 habs
    calc
      (x - Real.sqrt B) ^ 2 = |x - Real.sqrt B| ^ 2 := by
        rw [sq_abs]
      _ ≤ (3 * Real.sqrt B) ^ 2 := hsquare
      _ = 9 * B := by rw [mul_pow, hsSq]; ring
  have hprod := mul_le_mul hfirst hsecond hsecond0 hB0
  calc
    -x * (x + 2 * Real.sqrt B) * (x - Real.sqrt B) ^ 2 =
        ((Real.sqrt B) ^ 2 - (x + Real.sqrt B) ^ 2) *
          (x - Real.sqrt B) ^ 2 := by ring
    _ = (B - (x + Real.sqrt B) ^ 2) *
          (x - Real.sqrt B) ^ 2 := by rw [hsSq]
    _ ≤ B * (9 * B) := hprod
    _ = 9 * B ^ 2 := by ring

private lemma oneSidedFourthMoment_polynomial_nonpos_off
    {B x : ℝ} (hB : 1 ≤ B)
    (hx : x ∉ Set.Icc (-2 * Real.sqrt B) 0) :
    -x * (x + 2 * Real.sqrt B) * (x - Real.sqrt B) ^ 2 ≤ 0 := by
  have hs0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg _
  have hout : x < -2 * Real.sqrt B ∨ 0 < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  have hfac : -x * (x + 2 * Real.sqrt B) ≤ 0 := by
    rcases hout with hx | hx <;> nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg hfac (sq_nonneg _)

/-- KSSS Lemma 5.9, normalized to variance one.  A centered random variable
with fourth moment at most `B` has probability at least `1/(5B)` of lying
between `-2√B` and zero. -/
theorem measureReal_oneSided_interval_ge_of_fourthMoment
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (mu : Measure Ω)
    [IsProbabilityMeasure mu] (Y : Ω → ℝ)
    {B : ℝ} (hB : 1 ≤ B)
    (hYmeas : Measurable Y)
    (hY : Integrable Y mu)
    (hY2 : Integrable (fun w ↦ Y w ^ 2) mu)
    (hY4 : Integrable (fun w ↦ Y w ^ 4) mu)
    (hmean : ∫ w, Y w ∂mu = 0)
    (hsecond : ∫ w, Y w ^ 2 ∂mu = 1)
    (hfourth : ∫ w, Y w ^ 4 ∂mu ≤ B) :
    1 / (5 * B) ≤
      mu.real (Y ⁻¹' Set.Icc (-2 * Real.sqrt B) 0) := by
  let S : Set Ω := Y ⁻¹' Set.Icc (-2 * Real.sqrt B) 0
  let q : Ω → ℝ := fun w ↦
    -Y w * (Y w + 2 * Real.sqrt B) * (Y w - Real.sqrt B) ^ 2
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hsSq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB0
  have hS : MeasurableSet S := measurableSet_Icc.preimage hYmeas
  have hqInt : Integrable q mu := by
    have hY2c : Integrable (fun w ↦ (3 * B) * Y w ^ 2) mu :=
      hY2.const_mul _
    have hYc : Integrable (fun w ↦ (2 * B * Real.sqrt B) * Y w) mu :=
      hY.const_mul _
    have hsum := hY4.neg.add hY2c |>.sub hYc
    convert hsum using 1
    funext w
    dsimp only [q]
    calc
      -Y w * (Y w + 2 * Real.sqrt B) * (Y w - Real.sqrt B) ^ 2 =
          -Y w ^ 4 + 3 * (Real.sqrt B) ^ 2 * Y w ^ 2 -
            2 * (Real.sqrt B) ^ 3 * Y w := by ring
      _ = -Y w ^ 4 + 3 * B * Y w ^ 2 -
            2 * B * Real.sqrt B * Y w := by
        rw [hsSq, show (Real.sqrt B) ^ 3 =
          B * Real.sqrt B by rw [pow_succ, hsSq]]
        ring
  have hrhsInt : Integrable (fun w ↦
      9 * B ^ 2 * S.indicator (1 : Ω → ℝ) w) mu :=
    (Integrable.indicator (integrable_const (1 : ℝ)) hS).const_mul _
  have hpoint : ∀ w,
      q w ≤ 9 * B ^ 2 * S.indicator (1 : Ω → ℝ) w := by
    intro w
    by_cases hw : w ∈ S
    · rw [Set.indicator_of_mem hw, Pi.one_apply, mul_one]
      exact oneSidedFourthMoment_polynomial_le_on hB hw
    · rw [Set.indicator_of_notMem hw, mul_zero]
      exact oneSidedFourthMoment_polynomial_nonpos_off hB hw
  have hintegral := integral_mono hqInt hrhsInt hpoint
  have hqIntegral : 2 * B ≤ ∫ w, q w ∂mu := by
    have hqEq : (∫ w, q w ∂mu) =
        -(∫ w, Y w ^ 4 ∂mu) +
          3 * B * (∫ w, Y w ^ 2 ∂mu) -
            2 * B * Real.sqrt B * (∫ w, Y w ∂mu) := by
      have hY2c : Integrable (fun w ↦ (3 * B) * Y w ^ 2) mu :=
        hY2.const_mul _
      have hYc : Integrable (fun w ↦ (2 * B * Real.sqrt B) * Y w) mu :=
        hY.const_mul _
      have hfun : q =
          (- fun w ↦ Y w ^ 4) +
            (fun w ↦ (3 * B) * Y w ^ 2) -
              (fun w ↦ (2 * B * Real.sqrt B) * Y w) := by
        funext w
        dsimp only [q]
        change -Y w * (Y w + 2 * Real.sqrt B) *
            (Y w - Real.sqrt B) ^ 2 =
          -Y w ^ 4 + (3 * B) * Y w ^ 2 -
            (2 * B * Real.sqrt B) * Y w
        calc
          -Y w * (Y w + 2 * Real.sqrt B) *
              (Y w - Real.sqrt B) ^ 2 =
            -Y w ^ 4 + 3 * (Real.sqrt B) ^ 2 * Y w ^ 2 -
              2 * (Real.sqrt B) ^ 3 * Y w := by ring
          _ = _ := by
            rw [hsSq, show (Real.sqrt B) ^ 3 =
              B * Real.sqrt B by rw [pow_succ, hsSq]]
            ring
      rw [hfun]
      let f4 : Ω → ℝ := fun w ↦ -(Y w ^ 4)
      let f2 : Ω → ℝ := fun w ↦ (3 * B) * Y w ^ 2
      let f1 : Ω → ℝ := fun w ↦ (2 * B * Real.sqrt B) * Y w
      have hf4 : Integrable f4 mu := by
        have heq : f4 = -(fun w ↦ Y w ^ 4) := by
          funext w
          rfl
        rw [heq]
        exact hY4.neg
      have hf2 : Integrable f2 mu := by simpa only [f2] using hY2c
      have hf1 : Integrable f1 mu := by simpa only [f1] using hYc
      have hadd : (∫ w, (f4 + f2) w ∂mu) =
          (∫ w, f4 w ∂mu) + ∫ w, f2 w ∂mu :=
        integral_add hf4 hf2
      change (∫ w, ((f4 + f2) - f1) w ∂mu) = _
      calc
        (∫ w, ((f4 + f2) - f1) w ∂mu) =
            (∫ w, (f4 + f2) w ∂mu) - ∫ w, f1 w ∂mu :=
          integral_sub (hf4.add hf2) hf1
        _ = ((∫ w, f4 w ∂mu) + ∫ w, f2 w ∂mu) -
            ∫ w, f1 w ∂mu := by
          rw [hadd]
        _ = _ := by
          dsimp only [f4, f2, f1]
          rw [integral_neg, integral_const_mul, integral_const_mul]
    rw [hqEq, hmean, hsecond, mul_zero, sub_zero]
    linarith
  have hrhsIntegral :
      (∫ w, 9 * B ^ 2 * S.indicator (1 : Ω → ℝ) w ∂mu) =
        9 * B ^ 2 * mu.real S := by
    rw [integral_const_mul, integral_indicator_one hS]
  rw [hrhsIntegral] at hintegral
  have hmass : 2 * B ≤ 9 * B ^ 2 * mu.real S := hqIntegral.trans hintegral
  change 1 / (5 * B) ≤ mu.real S
  have hcoef : 1 / (5 * B) ≤ 2 / (9 * B) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 5 * B)
      (by positivity : 0 < 9 * B)).2
    nlinarith
  calc
    1 / (5 * B) ≤ 2 / (9 * B) := hcoef
    _ ≤ mu.real S := by
      apply (div_le_iff₀ (by positivity : 0 < 9 * B)).2
      have hnorm : 9 * B ^ 2 = (9 * B) * B := by ring
      rw [hnorm] at hmass
      nlinarith

/-- Scale-covariant form of KSSS Lemma 5.9. -/
theorem measureReal_oneSided_interval_ge_of_fourthMoment_scaled
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (mu : Measure Ω)
    [IsProbabilityMeasure mu] (X : Ω → ℝ)
    {B sigma : ℝ} (hB : 1 ≤ B) (hsigma : 0 < sigma)
    (hXmeas : Measurable X)
    (hX : Integrable X mu)
    (hX2 : Integrable (fun w ↦ X w ^ 2) mu)
    (hX4 : Integrable (fun w ↦ X w ^ 4) mu)
    (hmean : ∫ w, X w ∂mu = 0)
    (hsecond : ∫ w, X w ^ 2 ∂mu = sigma ^ 2)
    (hfourth : ∫ w, X w ^ 4 ∂mu ≤ B * sigma ^ 4) :
    1 / (5 * B) ≤
      mu.real (X ⁻¹' Set.Icc (-2 * Real.sqrt B * sigma) 0) := by
  let Y : Ω → ℝ := fun w ↦ X w / sigma
  have hYmeas : Measurable Y := hXmeas.div_const _
  have hY : Integrable Y mu := hX.div_const _
  have hY2 : Integrable (fun w ↦ Y w ^ 2) mu := by
    have h := hX2.div_const (sigma ^ 2)
    convert h using 1
    funext w
    dsimp only [Y]
    field_simp [hsigma.ne']
  have hY4 : Integrable (fun w ↦ Y w ^ 4) mu := by
    have h := hX4.div_const (sigma ^ 4)
    convert h using 1
    funext w
    dsimp only [Y]
    field_simp [hsigma.ne']
  have hYmean : ∫ w, Y w ∂mu = 0 := by
    dsimp only [Y]
    rw [integral_div, hmean, zero_div]
  have hYsecond : ∫ w, Y w ^ 2 ∂mu = 1 := by
    have hfun : (fun w ↦ Y w ^ 2) = fun w ↦ X w ^ 2 / sigma ^ 2 := by
      funext w
      dsimp only [Y]
      field_simp [hsigma.ne']
    rw [hfun, integral_div, hsecond, div_self (pow_ne_zero 2 hsigma.ne')]
  have hYfourth : ∫ w, Y w ^ 4 ∂mu ≤ B := by
    have hfun : (fun w ↦ Y w ^ 4) = fun w ↦ X w ^ 4 / sigma ^ 4 := by
      funext w
      dsimp only [Y]
      field_simp [hsigma.ne']
    rw [hfun, integral_div]
    apply (div_le_iff₀ (pow_pos hsigma 4)).2
    simpa only [mul_comm] using hfourth
  have hbase := measureReal_oneSided_interval_ge_of_fourthMoment
    mu Y hB hYmeas hY hY2 hY4 hYmean hYsecond hYfourth
  have hpreimage :
      Y ⁻¹' Set.Icc (-2 * Real.sqrt B) 0 =
        X ⁻¹' Set.Icc (-2 * Real.sqrt B * sigma) 0 := by
    ext w
    simp only [Set.mem_preimage, Set.mem_Icc]
    dsimp only [Y]
    constructor
    · rintro ⟨hlower, hupper⟩
      constructor
      · have := (le_div_iff₀ hsigma).mp hlower
        nlinarith
      · have := (div_le_iff₀ hsigma).mp hupper
        simpa only [zero_mul] using this
    · rintro ⟨hlower, hupper⟩
      constructor
      · apply (le_div_iff₀ hsigma).2
        nlinarith
      · apply (div_le_iff₀ hsigma).2
        simpa only [zero_mul] using hupper
  rw [hpreimage] at hbase
  exact hbase

end Erdos88.GaussianQuadratic
