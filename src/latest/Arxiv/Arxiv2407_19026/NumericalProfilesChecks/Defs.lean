import Arxiv.Arxiv2407_19026.PointwiseOptimization
import LeanCert.Tactic.IntervalAuto
import LeanCert.Validity.AffineCover

/-!
# Certified numerical facts for the Section 4 profiles

The paper delegates its profile inequalities to Mathematica.  Here numerical
claims are kernel-checked using rational interval subdivision.  In particular,
the four profiles have *positive* slope on `[0.05,1]`; this certifies the sign
correction made in `Profiles.lean`.
-/

noncomputable section

namespace Arxiv2407_19026

/-- Log-exp expansion of the first book coordinate, suitable for certified
interval arithmetic. -/
def optimizationXExp (β z : ℝ) : ℝ :=
  Real.exp
      (Real.log (optimizationP β z) /
        (1 - optimizationM z)) *
    (1 - optimizationM z)

lemma optimizationXExp_eq {β z : ℝ}
    (hp : 0 < optimizationP β z) :
    optimizationXExp β z = optimizationX β z := by
  rw [optimizationX, optimizationXExp,
    Real.rpow_def_of_pos hp]
  congr 2
  ring

set_option maxRecDepth 10000 in
theorem optimizedRamseySlope_beta0_pos :
    ∀ z ∈ Set.Icc (1 / 50 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (2 / 25) z := by
  have hleft : ∀ z ∈ Set.Icc (1 / 50 : ℝ) (51 / 100),
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (2 / 25) z := by
    unfold optimizedRamseySlope
    certify_bound 20
  have hright : ∀ z ∈ Set.Icc (51 / 100 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (2 / 25) z := by
    unfold optimizedRamseySlope
    certify_bound 20
  intro z hz
  by_cases hsplit : z ≤ (51 / 100 : ℝ)
  · exact hleft z ⟨hz.1, hsplit⟩
  · exact hright z ⟨le_of_not_ge hsplit, hz.2⟩

set_option maxRecDepth 10000 in
theorem optimizedRamseySlope_beta1_pos :
    ∀ z ∈ Set.Icc (1 / 20 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (9 / 200) z := by
  have hleft : ∀ z ∈ Set.Icc (1 / 20 : ℝ) (21 / 40),
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (9 / 200) z := by
    unfold optimizedRamseySlope
    certify_bound 20
  have hright : ∀ z ∈ Set.Icc (21 / 40 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (9 / 200) z := by
    unfold optimizedRamseySlope
    certify_bound 20
  intro z hz
  by_cases hsplit : z ≤ (21 / 40 : ℝ)
  · exact hleft z ⟨hz.1, hsplit⟩
  · exact hright z ⟨le_of_not_ge hsplit, hz.2⟩

set_option maxRecDepth 10000 in
theorem optimizedRamseySlope_beta2_pos :
    ∀ z ∈ Set.Icc (1 / 20 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (33 / 1000) z := by
  have hleft : ∀ z ∈ Set.Icc (1 / 20 : ℝ) (21 / 40),
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (33 / 1000) z := by
    unfold optimizedRamseySlope
    certify_bound 20
  have hright : ∀ z ∈ Set.Icc (21 / 40 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (33 / 1000) z := by
    unfold optimizedRamseySlope
    certify_bound 20
  intro z hz
  by_cases hsplit : z ≤ (21 / 40 : ℝ)
  · exact hleft z ⟨hz.1, hsplit⟩
  · exact hright z ⟨le_of_not_ge hsplit, hz.2⟩

set_option maxRecDepth 10000 in
theorem optimizedRamseySlope_beta3_pos :
    ∀ z ∈ Set.Icc (1 / 20 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (3 / 100) z := by
  have hleft : ∀ z ∈ Set.Icc (1 / 20 : ℝ) (21 / 40),
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (3 / 100) z := by
    unfold optimizedRamseySlope
    certify_bound 20
  have hright : ∀ z ∈ Set.Icc (21 / 40 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (3 / 100) z := by
    unfold optimizedRamseySlope
    certify_bound 20
  intro z hz
  by_cases hsplit : z ≤ (21 / 40 : ℝ)
  · exact hleft z ⟨hz.1, hsplit⟩
  · exact hright z ⟨le_of_not_ge hsplit, hz.2⟩

/-- The first-round elementary book margin after cancelling the two
occurrences of `z log z`.  This form is substantially better conditioned
for kernel interval arithmetic near zero. -/
def beta0ElementaryMargin (z : ℝ) : ℝ :=
  (1 + z) * Real.log (1 + z) + ramseyCorrection (2 / 25) z +
    (Real.log (optimizationP (2 / 25) z) / (1 - optimizationM z) +
      Real.log (1 - optimizationM z) - z ^ 2 +
      z * Real.log
        ((1 - optimizationXExp (2 / 25) z) / z)) / 2

lemma beta0ElementaryMargin_eq
    {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1)
    (hX1 : optimizationXExp (2 / 25) z < 1) :
    beta0ElementaryMargin z =
      optimizedRamseyExponent (2 / 25) z +
        (Real.log (optimizationXExp (2 / 25) z) +
          z * Real.log (optimizationM z) +
          z * Real.log (1 - optimizationXExp (2 / 25) z)) / 2 := by
  have he0 : 0 < Real.exp (-z) := Real.exp_pos _
  have he1 : Real.exp (-z) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hm1 : optimizationM z < 1 := by
    unfold optimizationM
    exact mul_lt_one_of_nonneg_of_lt_one_right hz1 he0.le he1
  have h1m : 0 < 1 - optimizationM z := sub_pos.mpr hm1
  have hratio :
      0 < (1 - optimizationXExp (2 / 25) z) / z :=
    div_pos (sub_pos.mpr hX1) hz
  have hlog :
      Real.log (1 - optimizationXExp (2 / 25) z) =
        Real.log z +
          Real.log ((1 - optimizationXExp (2 / 25) z) / z) := by
    rw [← Real.log_mul hz.ne' hratio.ne']
    congr 1
    field_simp
  rw [beta0ElementaryMargin, hlog, optimizationXExp,
    Real.log_mul (Real.exp_ne_zero _) h1m.ne',
    Real.log_exp, optimizationM, Real.log_mul hz.ne' he0.ne',
    Real.log_exp]
  unfold optimizedRamseyExponent ramseyEntropy
  ring_nf

/-- Degree-nine polynomial lower approximation to
`exp (-optimizedRamseySlope β₀ z) / z`. -/
def beta0U (z : ℝ) : ℝ :=
  1.284024751404 +
    z * (-2.131427997038 +
    z * (2.891286818537 +
    z * (-3.264680122333 +
    z * (3.285022020636 +
    z * (-2.940312871156 +
    z * (2.192513219941 +
    z * (-1.218022340257 +
    z * (0.429628799767 +
    z * (-0.070285151867))))))))) +
    1 / 2000

/-- The degree-nine large-ratio approximation to the normalized loss of the
first book coordinate. -/
def beta0VLarge (z : ℝ) : ℝ :=
  2.284025580120 +
    z * (-3.131445731927 +
    z * (2.567372678585 +
    z * (-1.052523072075 +
    z * (-0.329273824258 +
    z * (0.842245058702 +
    z * (-0.605732339550 +
    z * (0.214074650516 +
    z * (-0.026060252906 +
    z * (-0.002738794873))))))))) +
    1 / 1000 + 1 / 50 * (1 - z) ^ 6

/-- A deliberately discontinuous pointwise choice is permitted here: the
constant near zero gives well-conditioned linear slack, while the optimized
polynomial is used on the rest of the compact ratio interval. -/
def beta0V (z : ℝ) : ℝ :=
  if z ≤ 3 / 1000 then 461 / 200 else beta0VLarge z

def beta0PolynomialP (z : ℝ) : ℝ := 1 - z * beta0U z
def beta0PolynomialX (z : ℝ) : ℝ := 1 - z * beta0V z
def beta0PolynomialY (z : ℝ) : ℝ :=
  z * (beta0V z - 1 / 100000)

/-- The non-entropy part of the derivative of the first profile. -/
def beta0CorrectionSlope (z : ℝ) : ℝ :=
  (-(1 / 4 : ℝ) + 2 * (2 / 25 : ℝ) * z +
      (6 / 25 : ℝ) * z ^ 2 -
    (-(1 / 4 : ℝ) * z + (2 / 25 : ℝ) * z ^ 2 +
      (2 / 25 : ℝ) * z ^ 3)) * Real.exp (-z)

def beta0PolynomialBookMargin (z : ℝ) : ℝ :=
  (1 + z) * Real.log (1 + z) + ramseyCorrection (2 / 25) z +
    (Real.log (beta0PolynomialX z) - z ^ 2 +
      z * Real.log (beta0V z - 1 / 100000)) / 2

def beta0PolynomialBlueLogMargin (z : ℝ) : ℝ :=
  Real.log (1 + z) + beta0CorrectionSlope z +
    Real.log (9999 / 10000 : ℝ) + Real.log (beta0U z)

def beta0PolynomialLimitLogMargin (z : ℝ) : ℝ :=
  Real.log (beta0PolynomialP z) -
    (1 - optimizationM z) *
      (Real.log (beta0PolynomialX z) -
        Real.log (1 - optimizationM z))

/-- The small-ratio book margin after fixing the normalized loss at
`461 / 200` and subtracting a strict linear reserve. -/
def beta0SmallBookMargin (z : ℝ) : ℝ :=
  (z + 1) * Real.log (z + 1) + ramseyCorrection (2 / 25) z +
    (Real.log (1 - z * (461 / 200)) - z ^ 2 +
      z * Real.log ((461 / 200) - 1 / 100000)) * (1 / 2) -
    z * (1 / 10000)

/-- Exact derivative of `beta0SmallBookMargin`. -/
def beta0SmallBookSlope (z : ℝ) : ℝ :=
  Real.log (1 + z) + 1 + beta0CorrectionSlope z +
    (-(461 / 200) / (1 - z * (461 / 200)) - 2 * z +
      Real.log ((461 / 200) - 1 / 100000)) / 2 -
    1 / 10000

set_option maxRecDepth 10000 in
lemma beta0SmallBookSlope_cleared_pos :
    ∀ z ∈ Set.Icc (0 : ℝ) (3 / 1000),
      0 ≤
        (Real.log (1 + z) + 1 + beta0CorrectionSlope z +
            (-2 * z + Real.log ((461 / 200) - 1 / 100000)) * (1 / 2) -
            1 / 10000 - 1 / 100000) *
          (1 - z * (461 / 200)) -
        (461 / 200) * (1 / 2) := by
  unfold beta0CorrectionSlope
  rintro z ⟨hz0, hz1⟩
  have hlog :
      (83 / 100 : ℝ) ≤ Real.log ((461 / 200 : ℝ) - 1 / 100000) := by
    have hlogAdd := Real.le_log_one_add_of_nonneg
      (show (0 : ℝ) ≤ 30499 / 200000 by norm_num)
    rw [show (461 / 200 : ℝ) - 1 / 100000 =
      2 * (1 + 30499 / 200000) by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num at hlogAdd ⊢
    nlinarith [Real.log_two_gt_d9]
  have hlogz : 0 ≤ Real.log (1 + z) :=
    Real.log_nonneg (by linarith)
  have hqLower :
      (-1 / 4 : ℝ) ≤
        -(1 / 4 : ℝ) + 2 * (2 / 25 : ℝ) * z +
            (6 / 25 : ℝ) * z ^ 2 -
          (-(1 / 4 : ℝ) * z + (2 / 25 : ℝ) * z ^ 2 +
            (2 / 25 : ℝ) * z ^ 3) := by
    have haux : 0 ≤ z ^ 2 * (2 - z) :=
      mul_nonneg (sq_nonneg z) (by linarith)
    nlinarith
  have hqUpper :
      -(1 / 4 : ℝ) + 2 * (2 / 25 : ℝ) * z +
            (6 / 25 : ℝ) * z ^ 2 -
          (-(1 / 4 : ℝ) * z + (2 / 25 : ℝ) * z ^ 2 +
            (2 / 25 : ℝ) * z ^ 3) ≤ 0 := by
    have hzsq : 0 ≤ z * (3 / 1000 - z) :=
      mul_nonneg hz0 (by linarith)
    have hzcube : 0 ≤ z ^ 3 := pow_nonneg hz0 3
    nlinarith
  have hexp : Real.exp (-z) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hcorr :
      (-1 / 4 : ℝ) ≤
        (-(1 / 4 : ℝ) + 2 * (2 / 25 : ℝ) * z +
            (6 / 25 : ℝ) * z ^ 2 -
          (-(1 / 4 : ℝ) * z + (2 / 25 : ℝ) * z ^ 2 +
            (2 / 25 : ℝ) * z ^ 3)) * Real.exp (-z) := by
    have hmul := mul_le_mul_of_nonpos_left hexp hqUpper
    nlinarith
  have hinner :
      (116189 / 100000 : ℝ) ≤
        Real.log (1 + z) + 1 +
            (-(1 / 4 : ℝ) + 2 * (2 / 25 : ℝ) * z +
                (6 / 25 : ℝ) * z ^ 2 -
              (-(1 / 4 : ℝ) * z + (2 / 25 : ℝ) * z ^ 2 +
                (2 / 25 : ℝ) * z ^ 3)) * Real.exp (-z) +
            (-2 * z + Real.log ((461 / 200 : ℝ) - 1 / 100000)) *
              (1 / 2) -
            1 / 10000 - 1 / 100000 := by
    nlinarith
  have hfactor :
      (198617 / 200000 : ℝ) ≤ 1 - z * (461 / 200) := by
    nlinarith
  have hinner0 :
      0 ≤
        Real.log (1 + z) + 1 +
            (-(1 / 4 : ℝ) + 2 * (2 / 25 : ℝ) * z +
                (6 / 25 : ℝ) * z ^ 2 -
              (-(1 / 4 : ℝ) * z + (2 / 25 : ℝ) * z ^ 2 +
                (2 / 25 : ℝ) * z ^ 3)) * Real.exp (-z) +
            (-2 * z + Real.log ((461 / 200 : ℝ) - 1 / 100000)) *
              (1 / 2) -
            1 / 10000 - 1 / 100000 := by
    nlinarith
  have hprod := mul_le_mul hinner hfactor
    (by norm_num : (0 : ℝ) ≤ 198617 / 200000) hinner0
  nlinarith

lemma beta0SmallBookSlope_pos :
    ∀ z ∈ Set.Icc (0 : ℝ) (3 / 1000),
      (1 / 100000 : ℝ) ≤ beta0SmallBookSlope z := by
  intro z hz
  have hden : 0 < 1 - z * (461 / 200 : ℝ) := by
    norm_num at hz ⊢
    nlinarith
  have h := beta0SmallBookSlope_cleared_pos z hz
  have hdiv :
      ((461 / 200 : ℝ) / 2) / (1 - z * (461 / 200)) ≤
        Real.log (1 + z) + 1 + beta0CorrectionSlope z +
            (-2 * z + Real.log ((461 / 200) - 1 / 100000)) / 2 -
            1 / 10000 - 1 / 100000 := by
    rw [div_le_iff₀ hden]
    linarith
  unfold beta0SmallBookSlope
  have heq :
      (-(461 / 200 : ℝ) / (1 - z * (461 / 200)) - 2 * z +
          Real.log ((461 / 200) - 1 / 100000)) / 2 =
        (-2 * z + Real.log ((461 / 200) - 1 / 100000)) / 2 -
          ((461 / 200 : ℝ) / 2) / (1 - z * (461 / 200)) := by
    field_simp [hden.ne']
    ring
  rw [heq]
  linarith

lemma hasDerivAt_beta0SmallBookMargin {z : ℝ}
    (hplus : 1 + z ≠ 0)
    (hx : 1 - z * (461 / 200 : ℝ) ≠ 0) :
    HasDerivAt beta0SmallBookMargin (beta0SmallBookSlope z) z := by
  have hpderiv := (hasDerivAt_id z).add_const 1
  have hplus' : id z + 1 ≠ 0 := by
    simpa [Function.id_def, add_comm] using hplus
  have hmain := hpderiv.mul (hpderiv.log hplus')
  have hxlin :=
    (hasDerivAt_const z (1 : ℝ)).sub
      ((hasDerivAt_id z).mul_const (461 / 200 : ℝ))
  have hlogx := hxlin.log hx
  have hquad := (hasDerivAt_id z).pow 2
  have hlogw :=
    (hasDerivAt_id z).mul_const
      (Real.log ((461 / 200 : ℝ) - 1 / 100000))
  have hbook := ((hlogx.sub hquad).add hlogw).mul_const (1 / 2 : ℝ)
  have hreserve := (hasDerivAt_id z).mul_const (1 / 10000 : ℝ)
  unfold beta0SmallBookMargin
  convert ((hmain.add (hasDerivAt_ramseyCorrection (2 / 25))).add
    hbook).sub hreserve using 1
  all_goals try rfl
  all_goals
    try simp only [Function.id_def, Pi.sub_apply, one_mul, mul_one]
  unfold beta0SmallBookSlope beta0CorrectionSlope
  rw [add_comm z 1]
  field_simp [hplus, hplus', hx]
  ring

lemma beta0SmallBookMargin_pos {z : ℝ}
    (hz : z ∈ Set.Ioc (0 : ℝ) (3 / 1000)) :
    0 < beta0SmallBookMargin z := by
  have hderiv :
      ∀ x ∈ Set.Icc (0 : ℝ) (3 / 1000),
        HasDerivAt beta0SmallBookMargin (beta0SmallBookSlope x) x := by
    intro x hx
    apply hasDerivAt_beta0SmallBookMargin
    · norm_num at hx ⊢
      linarith [hx.1]
    norm_num at hx ⊢
    linarith [hx.1, hx.2]
  have hcont :
      ContinuousOn beta0SmallBookMargin
        (Set.Icc (0 : ℝ) (3 / 1000)) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  have hmono :
      StrictMonoOn beta0SmallBookMargin
        (Set.Icc (0 : ℝ) (3 / 1000)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) (3 / 1000) :=
      interior_subset hx
    rw [(hderiv x hx').deriv]
    exact lt_of_lt_of_le (by norm_num)
      (beta0SmallBookSlope_pos x hx')
  have hzero : beta0SmallBookMargin 0 = 0 := by
    norm_num [beta0SmallBookMargin, ramseyCorrection]
  rw [← hzero]
  exact hmono (by norm_num) ⟨le_of_lt hz.1, hz.2⟩ hz.1

set_option maxRecDepth 10000 in
lemma beta0U_mul_margin_small :
    ∀ z ∈ Set.Icc (0 : ℝ) (3 / 1000),
      0 ≤ (129 / 100 : ℝ) * beta0PolynomialP z - beta0U z := by
  intro z hz
  rcases hz with ⟨hz0, hz3⟩
  have hz1 : z ≤ 1 := by
    norm_num at hz3 ⊢
    linarith
  have hzpow (n : ℕ) (hn : 1 ≤ n) : z ^ n ≤ z := by
    simpa using (pow_le_pow_of_le_one hz0 hz1 hn)
  have hU : beta0U z ≤ (1.284524751404 : ℝ) := by
    rw [beta0U]
    have h2 := hzpow 2 (by omega)
    have h3 := hzpow 3 (by omega)
    have h4 := hzpow 4 (by omega)
    have h5 := hzpow 5 (by omega)
    have h6 := hzpow 6 (by omega)
    have h7 := hzpow 7 (by omega)
    have h8 := hzpow 8 (by omega)
    have h9 := hzpow 9 (by omega)
    ring_nf at ⊢
    nlinarith
  unfold beta0PolynomialP
  have hfactor : 1 + (129 / 100 : ℝ) * z ≤ 1.00387 := by
    norm_num at hz3 ⊢
    linarith
  have hfactor_nonneg : 0 ≤ 1 + (129 / 100 : ℝ) * z := by positivity
  have hmul := mul_le_mul_of_nonneg_left hU hfactor_nonneg
  have hconst :
      (1.284524751404 : ℝ) * (1 + (129 / 100 : ℝ) * z) ≤
        (1.284524751404 : ℝ) * 1.00387 := by
    exact mul_le_mul_of_nonneg_left hfactor (by norm_num)
  ring_nf at hmul hconst ⊢
  nlinarith

lemma beta0U_le_mul_beta0PolynomialP_small :
    ∀ z ∈ Set.Icc (0 : ℝ) (3 / 1000),
      beta0U z ≤ (129 / 100 : ℝ) * beta0PolynomialP z := by
  intro z hz
  have h := beta0U_mul_margin_small z hz
  linarith

set_option maxRecDepth 10000 in
lemma beta0PolynomialP_small_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (3 / 1000),
      (99 / 100 : ℝ) ≤ beta0PolynomialP z := by
  intro z hz
  rcases hz with ⟨hz0, hz3⟩
  have h9 : (-0.070285151867 : ℝ) ≤ 0 := by norm_num
  have h8 :
      (0.429628799767 : ℝ) + z * (-0.070285151867) ≤ 1 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz0 h9]
  have h7 :
      (-1.218022340257 : ℝ) +
          z * (0.429628799767 + z * (-0.070285151867)) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left h8 hz0
    norm_num at hz3 ⊢
    nlinarith
  have h6 :
      (2.192513219941 : ℝ) +
          z * (-1.218022340257 +
            z * (0.429628799767 + z * (-0.070285151867))) ≤ 3 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz0 h7]
  have h5 :
      (-2.940312871156 : ℝ) +
          z * (2.192513219941 +
            z * (-1.218022340257 +
              z * (0.429628799767 + z * (-0.070285151867)))) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left h6 hz0
    norm_num at hz3 ⊢
    nlinarith
  have h4 :
      (3.285022020636 : ℝ) +
          z * (-2.940312871156 +
            z * (2.192513219941 +
              z * (-1.218022340257 +
                z * (0.429628799767 + z * (-0.070285151867))))) ≤ 4 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz0 h5]
  have h3 :
      (-3.264680122333 : ℝ) +
          z * (3.285022020636 +
            z * (-2.940312871156 +
              z * (2.192513219941 +
                z * (-1.218022340257 +
                  z * (0.429628799767 + z * (-0.070285151867)))))) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left h4 hz0
    norm_num at hz3 ⊢
    nlinarith
  have h2 :
      (2.891286818537 : ℝ) +
          z * (-3.264680122333 +
            z * (3.285022020636 +
              z * (-2.940312871156 +
                z * (2.192513219941 +
                  z * (-1.218022340257 +
                    z * (0.429628799767 + z * (-0.070285151867))))))) ≤ 3 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz0 h3]
  have h1 :
      (-2.131427997038 : ℝ) +
          z * (2.891286818537 +
            z * (-3.264680122333 +
              z * (3.285022020636 +
                z * (-2.940312871156 +
                  z * (2.192513219941 +
                    z * (-1.218022340257 +
                      z * (0.429628799767 + z * (-0.070285151867)))))))) ≤ 0 := by
    have := mul_le_mul_of_nonneg_left h2 hz0
    norm_num at hz3 ⊢
    nlinarith
  have hU : beta0U z ≤ 2 := by
    unfold beta0U
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hz0 h1]
  unfold beta0PolynomialP
  have hmul := mul_le_mul_of_nonneg_left hU hz0
  norm_num at hz3 ⊢
  nlinarith

lemma beta0PolynomialLimitLogMargin_small_pos {z : ℝ}
    (hz : z ∈ Set.Ioc (0 : ℝ) (3 / 1000)) :
    0 < beta0PolynomialLimitLogMargin z := by
  have hzIcc : z ∈ Set.Icc (0 : ℝ) (3 / 1000) :=
    ⟨le_of_lt hz.1, hz.2⟩
  have hp : 0 < beta0PolynomialP z :=
    lt_of_lt_of_le (by norm_num) (beta0PolynomialP_small_lower z hzIcc)
  have hx : 0 < 1 - z * (461 / 200 : ℝ) := by
    norm_num at hz ⊢
    nlinarith
  have he0 : 0 < Real.exp (-z) := Real.exp_pos _
  have he1 : Real.exp (-z) ≤ 1 :=
    (Real.exp_le_one_iff).mpr (by linarith [hz.1])
  have hm0 : 0 ≤ optimizationM z := by
    unfold optimizationM
    exact mul_nonneg (le_of_lt hz.1) he0.le
  have hm1 : optimizationM z < 1 := by
    unfold optimizationM
    norm_num at hz ⊢
    nlinarith
  have hA : 0 < 1 - optimizationM z := sub_pos.mpr hm1
  have hu :
      beta0U z / beta0PolynomialP z ≤ (129 / 100 : ℝ) := by
    rw [div_le_iff₀ hp]
    exact beta0U_le_mul_beta0PolynomialP_small z hzIcc
  have hlogp :
      -(z * beta0U z) / beta0PolynomialP z ≤
        Real.log (beta0PolynomialP z) := by
    calc
      -(z * beta0U z) / beta0PolynomialP z =
          1 - (beta0PolynomialP z)⁻¹ := by
            rw [div_eq_mul_inv]
            field_simp [hp.ne']
            unfold beta0PolynomialP
            ring
      _ ≤ Real.log (beta0PolynomialP z) :=
        Real.one_sub_inv_le_log_of_pos hp
  have hlogx :
      Real.log (1 - z * (461 / 200 : ℝ)) ≤
        -(z * (461 / 200 : ℝ)) := by
    have h := Real.log_le_sub_one_of_pos hx
    linarith
  have hlogA :
      1 - (1 - optimizationM z)⁻¹ ≤
        Real.log (1 - optimizationM z) :=
    Real.one_sub_inv_le_log_of_pos hA
  have hAlogA :
      -optimizationM z ≤
        (1 - optimizationM z) *
          Real.log (1 - optimizationM z) := by
    calc
      -optimizationM z =
          (1 - optimizationM z) *
            (1 - (1 - optimizationM z)⁻¹) := by
              field_simp [hA.ne']
              ring
      _ ≤ (1 - optimizationM z) *
          Real.log (1 - optimizationM z) :=
        mul_le_mul_of_nonneg_left hlogA hA.le
  have hAx :
      (1 - optimizationM z) * (z * (461 / 200 : ℝ)) ≤
        -(1 - optimizationM z) *
          Real.log (1 - z * (461 / 200 : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hlogx hA.le
    linarith
  have hlower :
      -(z * beta0U z) / beta0PolynomialP z +
          (1 - optimizationM z) * (z * (461 / 200 : ℝ)) -
          optimizationM z ≤
        Real.log (beta0PolynomialP z) -
          (1 - optimizationM z) *
            (Real.log (1 - z * (461 / 200 : ℝ)) -
              Real.log (1 - optimizationM z)) := by
    linarith
  have hzu :
      z * (beta0U z / beta0PolynomialP z) ≤
        z * (129 / 100 : ℝ) :=
    mul_le_mul_of_nonneg_left hu (le_of_lt hz.1)
  have hm_le : optimizationM z ≤ z := by
    unfold optimizationM
    exact mul_le_of_le_one_right (le_of_lt hz.1) he1
  have hA_le :
      1 - z ≤ 1 - optimizationM z := by
    linarith
  have hmain :
      0 <
        -(z * beta0U z) / beta0PolynomialP z +
          (1 - optimizationM z) * (z * (461 / 200 : ℝ)) -
          optimizationM z := by
    have hzsq : z ^ 2 ≤ (3 / 1000 : ℝ) * z := by
      nlinarith [hz.1, hz.2]
    have hvA :=
      mul_le_mul_of_nonneg_right hA_le
        (mul_nonneg (le_of_lt hz.1) (by norm_num : (0 : ℝ) ≤ 461 / 200))
    rw [neg_div, ← neg_mul, mul_div_assoc] at *
    norm_num at hz ⊢
    nlinarith [hzu, hm_le, hvA, hzsq]
  have hzcut : z ≤ 3 / 1000 := hz.2
  rw [beta0PolynomialLimitLogMargin, beta0PolynomialX, beta0V,
    if_pos hzcut]
  exact lt_of_lt_of_le hmain hlower

set_option maxRecDepth 10000 in
lemma beta0U_small_upper :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 1000),
      beta0U z ≤ (257 / 200 : ℝ) := by
  unfold beta0U
  interval_bound_subdiv 8 2

set_option maxRecDepth 10000 in
lemma beta0V_small_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 1000),
      (2301 / 1000 : ℝ) ≤ beta0V z := by
  intro z hz
  have hzcut : z ≤ 3 / 1000 := by
    norm_num at hz ⊢
    linarith [hz.2]
  simp [beta0V, if_pos hzcut]
  norm_num

set_option maxRecDepth 10000 in
lemma beta0V_small_upper :
    ∀ z ∈ Set.Icc (0 : ℝ) (1 / 1000),
      beta0V z ≤ (12 / 5 : ℝ) := by
  intro z hz
  have hzcut : z ≤ 3 / 1000 := by
    norm_num at hz ⊢
    linarith [hz.2]
  simp [beta0V, if_pos hzcut]
  norm_num

namespace Beta0Affine

open LeanCert.Core

def z : Expr := .var 0
def c (q : ℚ) : Expr := .const q
def add (a b : Expr) : Expr := .add a b
def mul (a b : Expr) : Expr := .mul a b
def neg (a : Expr) : Expr := .neg a
def sub (a b : Expr) : Expr := add a (neg b)

def horner : List ℚ → Expr
  | [] => c 0
  | a :: as => add (c a) (mul z (horner as))

def u : Expr := horner
  [1.284024751404 + 1 / 2000,
    -2.131427997038, 2.891286818537, -3.264680122333,
    3.285022020636, -2.940312871156, 2.192513219941,
    -1.218022340257, 0.429628799767, -0.070285151867]

def vBase : Expr := horner
  [2.284025580120 + 1 / 1000,
    -3.131445731927, 2.567372678585, -1.052523072075,
    -0.329273824258, 0.842245058702, -0.605732339550,
    0.214074650516, -0.026060252906, -0.002738794873]

def v : Expr :=
  add vBase
    (mul (c (1 / 50)) (Expr.pow (sub (c 1) z) 6))

def vSmall : Expr := c (461 / 200)

def p : Expr := sub (c 1) (mul z u)
def x : Expr := sub (c 1) (mul z v)
def xSmall : Expr := sub (c 1) (mul z vSmall)
def w : Expr := sub v (c (1 / 100000))
def wSmall : Expr := sub vSmall (c (1 / 100000))
def μ : Expr := mul z (.exp (neg z))

def correction : Expr :=
  mul
    (add
      (add
        (mul (c (-1 / 4)) z)
        (mul (c (2 / 25)) (Expr.pow z 2)))
      (mul (c (2 / 25)) (Expr.pow z 3)))
    (.exp (neg z))

def correctionSlope : Expr :=
  mul
    (sub
      (add
        (add (c (-1 / 4)) (mul (c (4 / 25)) z))
        (mul (c (6 / 25)) (Expr.pow z 2)))
      (add
        (add
          (mul (c (-1 / 4)) z)
          (mul (c (2 / 25)) (Expr.pow z 2)))
        (mul (c (2 / 25)) (Expr.pow z 3))))
    (.exp (neg z))

def book : Expr :=
  add
    (add
      (mul (add (c 1) z) (.log (add (c 1) z)))
      correction)
    (mul (c (1 / 2))
      (add
        (add (.log x) (neg (Expr.pow z 2)))
        (mul z (.log w))))

def bookSmall : Expr :=
  sub
    (add
      (add
        (mul (add (c 1) z) (.log (add (c 1) z)))
        correction)
      (mul (c (1 / 2))
        (add
          (add (.log xSmall) (neg (Expr.pow z 2)))
          (mul z (.log wSmall)))))
    (mul (c (1 / 10000)) z)

def blue : Expr :=
  add
    (add (.log (add (c 1) z)) correctionSlope)
    (add (.log (c (9999 / 10000))) (.log u))

def limit : Expr :=
  sub (.log p)
    (mul (sub (c 1) μ)
      (sub (.log x) (.log (sub (c 1) μ))))

def limitSmall : Expr :=
  sub
    (sub (.log p)
      (mul (sub (c 1) μ)
        (sub (.log xSmall) (.log (sub (c 1) μ)))))
    (mul (c (1 / 1000)) z)

def positiveBreakpoints : List ℚ :=
  (List.range 1200).map (fun n => (n + 301 : ℚ) / 100000) ++
    (List.range 9850).map (fun n => (n + 151 : ℚ) / 10000)

def bookBreakpoints₀ : List ℚ :=
  (List.range 300).map (fun n => (n + 1 : ℚ) / 100000)

def bookBreakpoints₁ : List ℚ :=
  (List.range 1200).map (fun n => (n + 301 : ℚ) / 100000) ++
    (List.range 850).map (fun n => (n + 151 : ℚ) / 10000)

def bookBreakpoints₂ : List ℚ :=
  (List.range 4000).map (fun n => (n + 1001 : ℚ) / 10000)

def bookBreakpoints₃ : List ℚ :=
  (List.range 5000).map (fun n => (n + 5001 : ℚ) / 10000)

def zeroBreakpoints : List ℚ :=
  (List.range 10000).map (fun n => (n + 1 : ℚ) / 10000)

def cfg : LeanCert.Engine.AffineConfig where
  taylorDepth := 10
  maxNoiseSymbols := 0

def coarseBreakpoints : List ℚ :=
  (List.range 1000).map (fun n => (n + 1 : ℚ) / 1000)

private lemma coeRange_ne (count : ℕ) (hc : count ≠ 0) :
    ((List.range count : List ℕ) : List ℚ) ≠ [] := by
  change (List.range count).flatMap (fun n : ℕ => [(n : ℚ)]) ≠ []
  cases count with
  | zero => exact (hc rfl).elim
  | succ n => simp [List.range_succ]

private lemma coeRange_getLast (count : ℕ) (hc : count ≠ 0)
    (h : ((List.range count : List ℕ) : List ℚ) ≠ []) :
    (((List.range count : List ℕ) : List ℚ)).getLast h =
      ((count - 1 : ℕ) : ℚ) := by
  change
    ((List.range count).flatMap (fun n : ℕ => [(n : ℚ)])).getLast h = _
  cases count with
  | zero => exact (hc rfl).elim
  | succ n => simp [List.range_succ]

private lemma mappedCoeRange_ne (f : ℚ → ℚ) (count : ℕ)
    (hc : count ≠ 0) :
    (((List.range count : List ℕ) : List ℚ).map f) ≠ [] := by
  rw [ne_eq, List.map_eq_nil_iff]
  exact coeRange_ne count hc

private lemma mappedCoeRange_getLast (f : ℚ → ℚ) (count : ℕ)
    (hc : count ≠ 0)
    (h : (((List.range count : List ℕ) : List ℚ).map f) ≠ []) :
    ((((List.range count : List ℕ) : List ℚ).map f)).getLast h =
      f ((count - 1 : ℕ) : ℚ) := by
  rw [List.getLast_map, coeRange_getLast count hc]

private lemma mappedCoeRange_getLast?_eq (f : ℚ → ℚ) (count : ℕ)
    (hc : count ≠ 0) :
    ((((List.range count : List ℕ) : List ℚ).map f)).getLast? =
      some (f ((count - 1 : ℕ) : ℚ)) := by
  rw [List.getLast?_eq_some_getLast (mappedCoeRange_ne f count hc)]
  congr 1
  exact mappedCoeRange_getLast f count hc _

lemma coarseBreakpoints_ne : coarseBreakpoints ≠ [] := by
  unfold coarseBreakpoints
  exact mappedCoeRange_ne _ 1000 (by norm_num)

lemma coarseBreakpoints_last :
    coarseBreakpoints.getLast coarseBreakpoints_ne = 1 := by
  rw [List.getLast_eq_iff_getLast?_eq_some]
  unfold coarseBreakpoints
  rw [mappedCoeRange_getLast?_eq _ 1000 (by norm_num)]
  norm_num

lemma positiveBreakpoints_ne : positiveBreakpoints ≠ [] := by
  unfold positiveBreakpoints
  apply List.append_ne_nil_of_right_ne_nil
  exact mappedCoeRange_ne _ 9850 (by norm_num)

lemma positiveBreakpoints_last :
    positiveBreakpoints.getLast positiveBreakpoints_ne = 1 := by
  unfold positiveBreakpoints
  have hr :=
    mappedCoeRange_ne (fun n : ℚ => (n + 151) / 10000)
      9850 (by norm_num)
  rw [List.getLast_append_of_right_ne_nil _ _ hr]
  rw [mappedCoeRange_getLast _ 9850 (by norm_num) hr]
  norm_num

lemma bookBreakpoints₀_ne : bookBreakpoints₀ ≠ [] := by
  unfold bookBreakpoints₀
  exact mappedCoeRange_ne _ 300 (by norm_num)

lemma bookBreakpoints₀_last :
    bookBreakpoints₀.getLast bookBreakpoints₀_ne = 3 / 1000 := by
  unfold bookBreakpoints₀
  rw [mappedCoeRange_getLast _ 300 (by norm_num) bookBreakpoints₀_ne]
  norm_num

lemma bookBreakpoints₁_ne : bookBreakpoints₁ ≠ [] := by
  unfold bookBreakpoints₁
  apply List.append_ne_nil_of_right_ne_nil
  exact mappedCoeRange_ne _ 850 (by norm_num)

lemma bookBreakpoints₁_last :
    bookBreakpoints₁.getLast bookBreakpoints₁_ne = 1 / 10 := by
  unfold bookBreakpoints₁
  have hr :=
    mappedCoeRange_ne (fun n : ℚ => (n + 151) / 10000)
      850 (by norm_num)
  rw [List.getLast_append_of_right_ne_nil _ _ hr]
  rw [mappedCoeRange_getLast _ 850 (by norm_num) hr]
  norm_num

lemma bookBreakpoints₂_ne : bookBreakpoints₂ ≠ [] := by
  unfold bookBreakpoints₂
  exact mappedCoeRange_ne _ 4000 (by norm_num)

lemma bookBreakpoints₂_last :
    bookBreakpoints₂.getLast bookBreakpoints₂_ne = 1 / 2 := by
  rw [List.getLast_eq_iff_getLast?_eq_some]
  unfold bookBreakpoints₂
  rw [mappedCoeRange_getLast?_eq _ 4000 (by norm_num)]
  norm_num

lemma bookBreakpoints₃_ne : bookBreakpoints₃ ≠ [] := by
  unfold bookBreakpoints₃
  exact mappedCoeRange_ne _ 5000 (by norm_num)

lemma bookBreakpoints₃_last :
    bookBreakpoints₃.getLast bookBreakpoints₃_ne = 1 := by
  rw [List.getLast_eq_iff_getLast?_eq_some]
  unfold bookBreakpoints₃
  rw [mappedCoeRange_getLast?_eq _ 5000 (by norm_num)]
  norm_num

lemma zeroBreakpoints_ne : zeroBreakpoints ≠ [] := by
  unfold zeroBreakpoints
  exact mappedCoeRange_ne _ 10000 (by norm_num)

lemma zeroBreakpoints_last :
    zeroBreakpoints.getLast zeroBreakpoints_ne = 1 := by
  rw [List.getLast_eq_iff_getLast?_eq_some]
  unfold zeroBreakpoints
  rw [mappedCoeRange_getLast?_eq _ 10000 (by norm_num)]
  norm_num

lemma book_supported : ExprSupportedCore book :=
  Expr.checkSupportedCore_correct (by decide)

lemma bookSmall_supported : ExprSupportedCore bookSmall :=
  Expr.checkSupportedCore_correct (by decide)

lemma blue_supported : ExprSupportedCore blue :=
  Expr.checkSupportedCore_correct (by decide)

lemma limit_supported : ExprSupportedCore limit :=
  Expr.checkSupportedCore_correct (by decide)

lemma limitSmall_supported : ExprSupportedCore limitSmall :=
  Expr.checkSupportedCore_correct (by decide)

lemma u_supported : ExprSupportedCore u :=
  Expr.checkSupportedCore_correct (by decide)

lemma v_supported : ExprSupportedCore v :=
  Expr.checkSupportedCore_correct (by decide)

lemma p_supported : ExprSupportedCore p :=
  Expr.checkSupportedCore_correct (by decide)

lemma x_supported : ExprSupportedCore x :=
  Expr.checkSupportedCore_correct (by decide)

lemma eval_u (t : ℝ) :
    Expr.eval (fun _ ↦ t) u = beta0U t := by
  simp [u, horner, z, c, add, mul, beta0U, Expr.eval]
  ring

lemma eval_v (t : ℝ) :
    Expr.eval (fun _ ↦ t) v = beta0VLarge t := by
  simp [v, vBase, horner, z, c, add, mul, neg, sub,
    beta0VLarge, Expr.eval]
  ring

lemma eval_book (t : ℝ) :
    Expr.eval (fun _ ↦ t) book =
      (1 + t) * Real.log (1 + t) + ramseyCorrection (2 / 25) t +
        (Real.log (1 - t * beta0VLarge t) - t ^ 2 +
          t * Real.log (beta0VLarge t - 1 / 100000)) / 2 := by
  simp [book, correction, x, w, z, c, add, mul, neg, sub,
    eval_v, ramseyCorrection, Expr.eval]
  ring_nf

lemma eval_bookSmall (t : ℝ) :
    Expr.eval (fun _ ↦ t) bookSmall =
      (1 + t) * Real.log (1 + t) + ramseyCorrection (2 / 25) t +
        (Real.log (1 - t * (461 / 200)) - t ^ 2 +
          t * Real.log ((461 / 200) - 1 / 100000)) / 2 -
        t / 10000 := by
  simp [bookSmall, vSmall, xSmall, wSmall, correction, z, c, add,
    mul, neg, sub, ramseyCorrection, Expr.eval]
  ring_nf

lemma eval_blue (t : ℝ) :
    Expr.eval (fun _ ↦ t) blue =
      beta0PolynomialBlueLogMargin t := by
  simp [blue, correctionSlope, z, c, add, mul, neg, sub,
    eval_u, beta0PolynomialBlueLogMargin, beta0CorrectionSlope,
    Expr.eval]
  ring

lemma eval_limit (t : ℝ) :
    Expr.eval (fun _ ↦ t) limit =
      Real.log (beta0PolynomialP t) -
        (1 - optimizationM t) *
          (Real.log (1 - t * beta0VLarge t) -
            Real.log (1 - optimizationM t)) := by
  simp [limit, p, x, μ, z, c, add, mul, neg, sub,
    eval_u, eval_v, beta0PolynomialP, optimizationM, Expr.eval]
  ring_nf

lemma eval_limitSmall (t : ℝ) :
    Expr.eval (fun _ ↦ t) limitSmall =
      Real.log (beta0PolynomialP t) -
        (1 - optimizationM t) *
          (Real.log (1 - t * (461 / 200)) -
            Real.log (1 - optimizationM t)) -
        t / 1000 := by
  simp [limitSmall, p, xSmall, vSmall, μ, z, c, add, mul, neg, sub,
    eval_u, beta0PolynomialP, optimizationM, Expr.eval]
  ring_nf

lemma eval_p (t : ℝ) :
    Expr.eval (fun _ ↦ t) p = beta0PolynomialP t := by
  simp [p, z, c, add, mul, neg, sub, eval_u,
    beta0PolynomialP, Expr.eval]
  ring

lemma eval_x (t : ℝ) :
    Expr.eval (fun _ ↦ t) x = 1 - t * beta0VLarge t := by
  simp [x, z, c, add, mul, neg, sub, eval_v,
    Expr.eval]
  ring

end Beta0Affine
end Arxiv2407_19026
