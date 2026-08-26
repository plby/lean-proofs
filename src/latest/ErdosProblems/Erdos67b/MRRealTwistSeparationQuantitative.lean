import ErdosProblems.Erdos67b.MRRealCompactTwistSeparation
import ErdosProblems.Erdos67b.MRRealPretentiousSymmetry
import ErdosProblems.Erdos67b.LSeriesSublinear

/-!
# An explicit all-height opposite-twist lower bound

This file retains the Riemann-zeta value in the finite Euler comparison.
Unlike the compact-annulus specialization, the theorem is uniform in the
height and has no asymptotic or desired-distance hypothesis.  It identifies
the exact quantitative zeta bound needed for a moving `c log log X`
separation threshold.
-/

open scoped BigOperators ComplexConjugate LSeries.notation
open Filter Set

namespace Erdos67b

noncomputable section

/-- The absolute loss in the finite Euler comparison for the level-one
opposite-twist distance. -/
def oppositeTwistEulerLoss : ℝ :=
  PrimeEstimates.mertensBound +
    8 * (Real.log 2 + primeLogIntervalMertensConstant) / Real.log 2 +
    polynomialHeightPrimePowerRemainderBound +
    polynomialHeightWeightRemovalBound

/-- Unconditional quantitative separation with the precise remaining zeta
factor displayed.  This is valid at every height, including heights growing
with the prime cutoff. -/
theorem log_log_sub_log_norm_riemannZeta_sub_loss_le_oppositeTwistDistSq
    {X : ℕ} (hX : 4 ≤ X) (t : ℝ) :
    Real.log (Real.log (X : ℝ)) -
        Real.log
          ‖riemannZeta
            (polynomialHeightEulerPoint X (-2 * t))‖ -
        oppositeTwistEulerLoss ≤
      pretentiousDistSq (archimedeanTwist t)
        (archimedeanTwist (-t)) X := by
  let chi : DirichletCharacter ℂ 1 := 1
  let v : ℝ := -2 * t
  let sigma : ℝ := 1 + (Real.log (X : ℝ))⁻¹
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hsigma : 1 < sigma := by
    dsimp only [sigma]
    linarith [inv_pos.mpr hlogX]
  have hpointRe : (polynomialHeightEulerPoint X v).re = sigma := by
    simp only [polynomialHeightEulerPoint, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
      sigma]
  have hLzeta : L ↗chi (polynomialHeightEulerPoint X v) =
      riemannZeta (polynomialHeightEulerPoint X v) := by
    dsimp only [chi]
    exact LSeries_dirichletCharacter_one_eq_riemannZeta
      (by rw [hpointRe]; exact hsigma)
  have hquot : quotientCharacter chi chi = chi := by
    dsimp only [chi]
    exact quotientCharacter_one_one
  have heuler := truncatedEulerLog_le_log_norm_LSeries_add_uniform
    chi v hX
  have hlinear := truncatedEulerLinear_le_log_add_remainder
    (Y := X) chi v (by omega)
  have hcorr := quotientCorrelation_le_eulerLinear_add_weightBound
    (Y := X) (q := 1) (q' := 1) (by norm_num) (by norm_num)
      chi chi v (by omega)
  rw [hquot] at hcorr
  have hcorrFinal :
      characterTwistPrimeCorrelation chi chi v X ≤
        Real.log ‖riemannZeta (polynomialHeightEulerPoint X v)‖ +
          (8 * (Real.log 2 + primeLogIntervalMertensConstant) /
            Real.log 2) +
          polynomialHeightPrimePowerRemainderBound +
          polynomialHeightWeightRemovalBound := by
    rw [hLzeta] at heuler
    linarith
  have hmass := characterTwistPrimeMass_mertens_lower
    (Y := X) (by omega)
  have hdist :
      Real.log (Real.log (X : ℝ)) -
          Real.log ‖riemannZeta (polynomialHeightEulerPoint X v)‖ -
          oppositeTwistEulerLoss ≤
        characterTwistDistSq chi chi v X := by
    rw [characterTwistDistSq_eq_mass_sub_correlation]
    dsimp only [oppositeTwistEulerLoss]
    linarith
  calc
    Real.log (Real.log (X : ℝ)) -
          Real.log
            ‖riemannZeta
              (polynomialHeightEulerPoint X (-2 * t))‖ -
          oppositeTwistEulerLoss ≤
        characterTwistDistSq chi chi v X := by
      simpa only [v] using hdist
    _ = characterTwistDistSq chi chi ((-t) - t) X := by
      congr 2
      dsimp only [v]
      ring
    _ = pretentiousDistSq
          (dirichletArchimedeanTwist chi t)
          (dirichletArchimedeanTwist chi (-t)) X :=
      characterTwistDistSq_eq_pretentiousDistSq chi chi t (-t) X
    _ = pretentiousDistSq (archimedeanTwist t)
          (archimedeanTwist (-t)) X := by
      rw [dirichletArchimedeanTwist_one_eq_archimedeanTwist_compact,
        dirichletArchimedeanTwist_one_eq_archimedeanTwist_compact]

/-- Real-valued consumer of the explicit zeta lower bound. -/
theorem one_fourth_log_log_sub_log_norm_riemannZeta_sub_loss_le_realDistSq
    {f : ℕ → ℂ}
    (hreal : ∀ n, 0 < n → conj (f n) = f n)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 4 ≤ X) (t : ℝ) :
    (Real.log (Real.log (X : ℝ)) -
        Real.log
          ‖riemannZeta
            (polynomialHeightEulerPoint X (-2 * t))‖ -
        oppositeTwistEulerLoss) / 4 ≤
      pretentiousDistSq f (archimedeanTwist t) X := by
  exact one_fourth_mul_le_pretentiousDistSq_of_real_of_twist_separation
    hreal hbound
    (log_log_sub_log_norm_riemannZeta_sub_loss_le_oppositeTwistDistSq hX t)

/-- Compact zeta bound down to imaginary height two.  The lower endpoint two
is the exact one produced by the branch `1 < |t|` after replacing `t` by
`-2t`. -/
theorem exists_uniform_norm_riemannZeta_compact_two
    (V : ℝ) (hV : 2 ≤ V) :
    ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, 1 ≤ sigma → sigma ≤ 2 →
        2 ≤ |t| → |t| ≤ V →
        ‖riemannZeta ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤ C := by
  let T : Set ℝ := Set.Icc (-V) (-2) ∪ Set.Icc 2 V
  let K : Set (ℝ × ℝ) := Set.Icc (1 : ℝ) 2 ×ˢ T
  let z : ℝ × ℝ → ℂ := fun x ↦
    (x.1 : ℂ) + Complex.I * (x.2 : ℂ)
  let F : ℝ × ℝ → ℝ := fun x ↦ ‖riemannZeta (z x)‖
  have hT : IsCompact T := isCompact_Icc.union isCompact_Icc
  have hK : IsCompact K := isCompact_Icc.prod hT
  have hKne : K.Nonempty := by
    refine ⟨(1, 2), ?_⟩
    exact ⟨⟨le_rfl, by norm_num⟩, Or.inr ⟨le_rfl, hV⟩⟩
  have hz_ne : ∀ x ∈ K, z x ≠ 1 := by
    intro x hx heq
    have him := congrArg Complex.im heq
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_re, one_mul,
      zero_add, Complex.one_im] at him
    rcases hx.2 with hxneg | hxpos
    · linarith [hxneg.2]
    · linarith [hxpos.1]
  have hF : ContinuousOn F K := by
    intro x hx
    have hzcont : ContinuousAt z x := by
      dsimp only [z]
      fun_prop
    have hzetacont : ContinuousAt riemannZeta (z x) :=
      (differentiableAt_riemannZeta (hz_ne x hx)).continuousAt
    exact (hzetacont.norm.comp hzcont).continuousWithinAt
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKne hF
  refine ⟨F x + 1, by dsimp only [F]; positivity, ?_⟩
  intro sigma t hsigma1 hsigma2 ht2 htV
  have htT : t ∈ T := by
    by_cases ht : 0 ≤ t
    · right
      rw [abs_of_nonneg ht] at ht2 htV
      exact ⟨ht2, htV⟩
    · left
      have ht' : t ≤ 0 := le_of_not_ge ht
      rw [abs_of_nonpos ht'] at ht2 htV
      constructor <;> linarith
  have hst : (sigma, t) ∈ K := ⟨⟨hsigma1, hsigma2⟩, htT⟩
  exact (hmax hst).trans (le_add_of_nonneg_right zero_le_one)

/-- The existing fixed-epsilon sublinear L-series estimate gives a moving
`(1/4) log log X` opposite-twist separation throughout a fixed polylogarithmic
height window.  Frequencies above this window are intended for the reciprocal
Halasz-error branch. -/
theorem eventually_quarter_log_log_le_oppositeTwistDistSq_polylog :
    ∀ᶠ X : ℕ in atTop, ∀ t : ℝ,
      1 < |t| → |t| ≤ (Real.log (X : ℝ)) ^ (4 : ℕ) →
        (1 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) ≤
          pretentiousDistSq (archimedeanTwist t)
            (archimedeanTwist (-t)) X := by
  obtain ⟨V₀, hV₀, hL⟩ :=
    LSeriesSublinear.boundedConductorLSeriesSublinear 1 1 zero_lt_one
  let V : ℝ := max 2 V₀
  obtain ⟨C, hC, hcompact⟩ :=
    exists_uniform_norm_riemannZeta_compact_two V (le_max_left _ _)
  have hloglog : Tendsto
      (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hcompactAbsorb : ∀ᶠ X : ℕ in atTop,
      Real.log C + oppositeTwistEulerLoss ≤
        (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) := by
    have h := hloglog.eventually
      (eventually_ge_atTop
        ((4 / 3 : ℝ) * (Real.log C + oppositeTwistEulerLoss)))
    filter_upwards [h] with X hX
    nlinarith
  have hlossAbsorb : ∀ᶠ X : ℕ in atTop,
      oppositeTwistEulerLoss ≤
        (1 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) := by
    have h := hloglog.eventually
      (eventually_ge_atTop (4 * oppositeTwistEulerLoss))
    filter_upwards [h] with X hX
    linarith
  have hlogLarge : ∀ᶠ X : ℕ in atTop,
      (17 : ℝ) ^ (4 : ℕ) ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop ((17 : ℝ) ^ (4 : ℕ)))
  filter_upwards [hcompactAbsorb, hlossAbsorb, hlogLarge,
      eventually_ge_atTop 4] with X hcompactX hlossX hlogXlarge hX
  intro t htLower htUpper
  let u : ℝ := Real.log (X : ℝ)
  let v : ℝ := -2 * t
  let sigma : ℝ := 1 + u⁻¹
  have hu : 0 < u := by
    dsimp only [u]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hsigma1 : 1 < sigma := by
    dsimp only [sigma]
    linarith [inv_pos.mpr hu]
  have hlogXone : 1 ≤ u := by
    have : (1 : ℝ) < 17 ^ (4 : ℕ) := by norm_num
    exact this.le.trans hlogXlarge
  have hsigma2 : sigma ≤ 2 := by
    dsimp only [sigma]
    have hinv : u⁻¹ ≤ 1 := (inv_le_one₀ hu).2 hlogXone
    linarith
  have hvabs : |v| = 2 * |t| := by
    dsimp only [v]
    rw [abs_mul]
    norm_num
  have hvTwo : 2 ≤ |v| := by
    rw [hvabs]
    linarith
  have hpoint :
      ((sigma : ℝ) : ℂ) + Complex.I * (v : ℂ) =
        polynomialHeightEulerPoint X v := rfl
  have hzetaNe : riemannZeta (polynomialHeightEulerPoint X v) ≠ 0 := by
    rw [← LSeries_dirichletCharacter_one_eq_riemannZeta (by
      rw [← hpoint]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
        sub_zero, add_zero]
      exact hsigma1)]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re
      (1 : DirichletCharacter ℂ 1) (by
        rw [← hpoint]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero,
          sub_zero, add_zero]
        exact hsigma1)
  have hlogNorm :
      Real.log ‖riemannZeta (polynomialHeightEulerPoint X v)‖ +
          oppositeTwistEulerLoss ≤
        (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) := by
    by_cases hvHigh : (V₀ : ℝ) ≤ |v|
    · have hLnorm :
          ‖riemannZeta (polynomialHeightEulerPoint X v)‖ ≤
            Real.log |v| := by
        rw [← hpoint,
          ← LSeries_dirichletCharacter_one_eq_riemannZeta (by
            simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
              Complex.I_re, zero_mul, Complex.I_im, Complex.ofReal_im,
              mul_zero, sub_zero, add_zero]
            exact hsigma1)]
        simpa only [one_mul] using
          hL 1 (by norm_num) (by norm_num)
            (1 : DirichletCharacter ℂ 1) sigma v hvHigh hsigma1 hsigma2
      have hvUpper : |v| ≤ 2 * u ^ (4 : ℕ) := by
        rw [hvabs]
        exact mul_le_mul_of_nonneg_left (by simpa only [u] using htUpper)
          (by norm_num)
      let w : ℝ := u ^ (1 / 4 : ℝ)
      have hw : 17 ≤ w := by
        have hmono := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 17 ^ (4 : ℕ))
          hlogXlarge (by norm_num : (0 : ℝ) ≤ 1 / 4)
        have hroot : ((17 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ) = 17 := by
          simpa only [Nat.cast_ofNat, one_div] using
            (Real.pow_rpow_inv_natCast (x := (17 : ℝ)) (n := 4)
              (by norm_num) (by norm_num))
        simpa only [w, hroot] using hmono
      have hlogu : Real.log u ≤ 4 * w := by
        have h := Real.log_le_rpow_div hu.le (by norm_num : (0 : ℝ) < 1 / 4)
        dsimp only [w]
        convert h using 1 <;> ring
      have hwSquare : w ^ (2 : ℕ) = Real.sqrt u := by
        rw [Real.sqrt_eq_rpow]
        dsimp only [w]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
        norm_num
      have hlogv : Real.log |v| ≤ Real.sqrt u := by
        calc
          Real.log |v| ≤ Real.log (2 * u ^ (4 : ℕ)) :=
            Real.log_le_log (by positivity) hvUpper
          _ = Real.log 2 + 4 * Real.log u := by
            rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
              (pow_ne_zero _ hu.ne'), Real.log_pow]
            norm_num
          _ ≤ 1 + 16 * w := by
            have hlogTwo : Real.log 2 ≤ 1 :=
              Real.log_two_lt_d9.le.trans (by norm_num)
            linarith
          _ ≤ w ^ (2 : ℕ) := by nlinarith
          _ = Real.sqrt u := hwSquare
      have hlogvPos : 0 < Real.log |v| :=
        Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hvTwo)
      have hloglogv : Real.log (Real.log |v|) ≤
          (1 / 2 : ℝ) * Real.log u := by
        calc
          Real.log (Real.log |v|) ≤ Real.log (Real.sqrt u) :=
            Real.log_le_log hlogvPos hlogv
          _ = (1 / 2 : ℝ) * Real.log u := by
            rw [Real.log_sqrt hu.le]
            ring
      have hzetaPos : 0 < ‖riemannZeta (polynomialHeightEulerPoint X v)‖ :=
        norm_pos_iff.mpr hzetaNe
      have hlogZeta :
          Real.log ‖riemannZeta (polynomialHeightEulerPoint X v)‖ ≤
            (1 / 2 : ℝ) * Real.log u := by
        exact (Real.log_le_log hzetaPos hLnorm).trans hloglogv
      dsimp only [u] at hlogZeta
      linarith
    · have hvV : |v| ≤ V := by
        dsimp only [V]
        exact (le_of_not_ge hvHigh).trans (le_max_right _ _)
      have hcompactNorm :
          ‖riemannZeta (polynomialHeightEulerPoint X v)‖ ≤ C := by
        rw [← hpoint]
        exact hcompact sigma v hsigma1.le hsigma2 hvTwo hvV
      have hzetaPos : 0 < ‖riemannZeta (polynomialHeightEulerPoint X v)‖ :=
        norm_pos_iff.mpr hzetaNe
      have hlogCompact := Real.log_le_log hzetaPos hcompactNorm
      linarith
  have hsep :=
    log_log_sub_log_norm_riemannZeta_sub_loss_le_oppositeTwistDistSq hX t
  dsimp only [v] at hlogNorm
  linarith

end

end Erdos67b
