import ErdosProblems.Erdos67.MRGSA10FixedHighTailoredPerron
import ErdosProblems.Erdos67.MRGSA10MovingPerronCanonicalBlocks
import ErdosProblems.Erdos67.MRGSA10TailoredPerronRectangle
import ErdosProblems.Erdos67.MRGSA9SourceHalaszPointWideLocal

/-!
# The fixed-high A.10 Perron contour after restoring the small Euler factors

The weighted-Schur argument in `MRGSA10FixedHighTailoredPerron` was first
packaged for the coefficient with all primes below `23` deleted.  For the
large canonical two-block schedule those primes lie in the common outside
band.  We may therefore restore their single finite Euler product on the
joined low/high factor, while retaining the two generalized-Mangoldt windows
inside one vertical Cauchy estimate.
-/

open scoped BigOperators LSeries.notation
open Complex

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The one fixed factor incurred when the primes below `23` are restored
before the weighted-Schur estimate for the two Lambda windows. -/
def gsA10RestoredFixedHighHalaszEnvelope (A X : ℕ) : ℝ :=
  gsA9SmallPrimeEulerBound * gsA10FixedHighHalaszEnvelope A X

theorem gsA9SmallPrimeEulerBound_nonneg_restored :
    0 ≤ gsA9SmallPrimeEulerBound := by
  have h := norm_gsA9SmallPrimeEulerProduct_le
    (f := fun _ : ℕ ↦ (0 : ℂ))
    (fun _ _ ↦ by simp) (sigma := (1 / 2 : ℝ)) (t := 0) (le_refl _)
  exact (norm_nonneg _).trans h

theorem gsA10RestoredFixedHighHalaszEnvelope_nonneg
    (A X : ℕ) (hX : 0 < X) :
    0 ≤ gsA10RestoredFixedHighHalaszEnvelope A X := by
  exact mul_nonneg gsA9SmallPrimeEulerBound_nonneg_restored
    (gsA10FixedHighHalaszEnvelope_nonneg A X hX)

/-- The complete explicit pointwise right-hand side of the restored
fixed-high weighted-Schur Perron theorem. -/
def gsA10RestoredFixedHighPerronBudget
    (Cβ : ℝ) (Q S y A X : ℕ) (beta T : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ((gsA10RestoredFixedHighHalaszEnvelope A X *
        gsA10FixedHighPerronKernelScale X) *
          (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
            (2 * beta) T) ^ ((1 : ℝ) / 2) *
        (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
          ((1 : ℝ) / 2) +
      2 * T *
        (gsA10RestoredFixedHighHalaszEnvelope A X *
          gsA10FixedHighPerronKernelScale X) *
        ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
          (2 * gsA10PrimeLambdaHarmonicBudget X *
              gsA10HigherPrimePowerGeometricMass y X +
            (gsA10HigherPrimePowerGeometricMass y X) ^ 2)))

/-- The restored weighted-Schur Perron budget is monotone in the auxiliary
`beta` shift.  This lets the whole source rectangle be bounded at its upper
edge without separating the two Lambda windows. -/
theorem gsA10RestoredFixedHighPerronBudget_mono_beta
    {Cβ : ℝ} {Q S y A X : ℕ} {beta eta T : ℝ}
    (hCβ : 1 ≤ Cβ) (hX : 2 ≤ X) (hy : 0 < y) (hyX : y ≤ X)
    (hT : 0 < T) (hbeta : beta ≤ eta) :
    gsA10RestoredFixedHighPerronBudget Cβ Q S y A X beta T ≤
      gsA10RestoredFixedHighPerronBudget Cβ Q S y A X eta T := by
  have hdivNat : 0 < X / y := Nat.div_pos hyX hy
  have hdiv : (1 : ℝ) ≤ ((X / y : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ X / y by omega)
  have hpow : ((X / y : ℕ) : ℝ) ^ (2 * (2 * beta)) ≤
      ((X / y : ℕ) : ℝ) ^ (2 * (2 * eta)) := by
    apply Real.rpow_le_rpow_of_exponent_le hdiv
    linarith
  have hrow0 : 0 ≤ gsA10PrimeGaussianRowBound Cβ Q S y X T :=
    gsA10PrimeGaussianRowBound_nonneg hCβ hX hT
  have hharm0 : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
    unfold gsA10PrimeLambdaHarmonicBudget
    positivity
  have hleft :
      gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y (2 * beta) T ≤
        gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y (2 * eta) T := by
    unfold gsA10PrimeLambdaLeftEnergyBound
    gcongr
  have hleftPow :
      (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y (2 * beta) T) ^
          ((1 : ℝ) / 2) ≤
        (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y (2 * eta) T) ^
          ((1 : ℝ) / 2) := by
    exact Real.rpow_le_rpow
      (by unfold gsA10PrimeLambdaLeftEnergyBound; positivity) hleft
      (by norm_num)
  have hM0 : 0 ≤ gsA10RestoredFixedHighHalaszEnvelope A X :=
    gsA10RestoredFixedHighHalaszEnvelope_nonneg A X (by omega)
  have hK0 : 0 ≤ gsA10FixedHighPerronKernelScale X :=
    gsA10FixedHighPerronKernelScale_nonneg X
  have hright0 : 0 ≤
      (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
        ((1 : ℝ) / 2) := Real.rpow_nonneg (by
          unfold gsA10PrimeLambdaRightEnergyBound
          positivity) _
  unfold gsA10RestoredFixedHighPerronBudget
  gcongr

/-- The auxiliary source rectangle of moving Perron integrals. -/
def gsA10TwoBlockMovingPerronIntegrated
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (eta T : ℝ) : ℂ :=
  2 * ∫ alpha in 0..eta, ∫ beta in 0..eta,
    gsA10TwoBlockMovingPerronIntegral
      f hmul P₁ P₂ y X alpha beta T

/-- Weighted-Schur Perron control for the actual, undeleted coefficient.
The small primes are restored once on the joined low/high factor; the two
Lambda windows are never separated pointwise.  Only a pretentious-distance
lower bound on the genuinely integrated window `|t| ≤ T` is required. -/
theorem exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
        {y A X Q S : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
        (hQ : 3 ≤ Q) (hQy : Q ≤ y) (hS : 101 ≤ S)
        (hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {alpha beta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
        (halpha0 : 0 ≤ alpha)
        (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (hbeta0 : 0 ≤ beta)
        (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
        (hT : 0 < T) (hTX : T ≤ X)
        (hdist : ∀ t : ℝ, |t| ≤ T →
          (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X),
        ‖gsA10TwoBlockMovingPerronIntegral
            f hmul P₁ P₂ y X alpha beta T‖ ≤
          (2 * Real.pi)⁻¹ *
            ((gsA10RestoredFixedHighHalaszEnvelope A X *
                gsA10FixedHighPerronKernelScale X) *
                  (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
                    (2 * beta) T) ^ ((1 : ℝ) / 2) *
                (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
                  ((1 : ℝ) / 2) +
              2 * T *
                (gsA10RestoredFixedHighHalaszEnvelope A X *
                  gsA10FixedHighPerronKernelScale X) *
                ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
                  (2 * gsA10PrimeLambdaHarmonicBudget X *
                      gsA10HigherPrimePowerGeometricMass y X +
                    (gsA10HigherPrimePowerGeometricMass y X) ^ 2))) := by
  obtain ⟨Cβ, hCβ, hvertical⟩ :=
    exists_norm_intervalIntegral_mul_gsA10LambdaWindow_fixedHigh_pair_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ hsmallOutside y A X Q S hy hX
    hQ hQy hS hlogCβ alpha beta T hlogy halpha0 halpha hbeta0 hbeta hT hTX
    hdist
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigma : ℝ := c₀ - alpha - 2 * beta
  let M : ℝ := gsA10RestoredFixedHighHalaszEnvelope A X
  let K : ℝ := gsA10FixedHighPerronKernelScale X
  let lowHigh : ℝ → ℂ := fun t ↦
    LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        ((sigma : ℂ) + I * (t : ℂ)) *
      LSeries (gsA9HighArithmetic f y)
        ((c₀ : ℂ) + I * (t : ℂ))
  let kernel : ℝ → ℂ := fun t ↦
    (X : ℂ) ^ ((sigma : ℂ) + I * (t : ℂ)) /
      ((sigma : ℂ) + I * (t : ℂ))
  let F : ℝ → ℂ := fun t ↦ lowHigh t * kernel t
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hcStrict : 1 < c₀ := by
    dsimp only [c₀]
    exact Erdos67.EulerResidue.one_lt_taoExponent (by omega)
  have hsigmaHalf : 1 / 2 ≤ sigma := by
    dsimp only [sigma]
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hsigma : 0 < sigma :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigmaHalf
  have hK : 0 ≤ K := gsA10FixedHighPerronKernelScale_nonneg X
  have hlowHighCont : Continuous lowHigh :=
    (continuous_LSeries_twoBlockAlternatingLow_vertical
      hmul hbound P₁ P₂ y hsigma).mul
      (continuous_LSeries_gsA9HighArithmetic_vertical hbound y hcStrict)
  have hsne : ∀ t : ℝ, (sigma : ℂ) + I * (t : ℂ) ≠ 0 := by
    intro t htzero
    have hre := congrArg Complex.re htzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, Complex.zero_re] at hre
    linarith
  have hkernelCont : Continuous kernel := by
    dsimp only [kernel]
    apply Continuous.div
    · have hline : Continuous (fun t : ℝ ↦
          (sigma : ℂ) + I * (t : ℂ)) := by fun_prop
      exact hline.const_cpow (Or.inl (by norm_cast; omega))
    · fun_prop
    · exact hsne
  have hFcont : Continuous F := hlowHighCont.mul hkernelCont
  have hlowHighBound : ∀ t, |t| ≤ T → ‖lowHigh t‖ ≤ M := by
    intro t ht
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    have hsigmaWide : 1 - 3 / Real.log (y : ℝ) ≤ sigma := by
      dsimp only [sigma]
      rw [show 3 / Real.log (y : ℝ) =
        3 * (Real.log (y : ℝ))⁻¹ by field_simp]
      linarith
    have hle : sigma ≤ c₀ := by dsimp only [sigma]; linarith
    have hgap : c₀ - sigma ≤ 3 / Real.log (y : ℝ) := by
      dsimp only [sigma]
      rw [show 3 / Real.log (y : ℝ) =
        3 * (Real.log (y : ℝ))⁻¹ by field_simp]
      linarith
    have hpoint :=
      norm_twoBlock_alternatingLow_mul_high_le_wideHalaszPoint_of_distance
        hmul hbound P₁ P₂ hy hsmallOutside (by omega) (hdist t ht)
        hsigmaHalf hle hsigmaWide hgap
    dsimp only [lowHigh, M, gsA10RestoredFixedHighHalaszEnvelope]
    rw [LSeries_gsA9HighArithmetic]
    simpa only [c₀, sigma, Erdos67.MRHalaszEuler.halaszPoint,
      gsA10FixedHighHalaszEnvelope] using hpoint
  have hM : 0 ≤ M := by
    have hzero := hlowHighBound 0 (by simpa using hT.le)
    exact (norm_nonneg _).trans hzero
  have hMK : 0 ≤ M * K := mul_nonneg hM hK
  have hpow : (X : ℝ) ^ sigma ≤ Real.exp 2 * X := by
    dsimp only [sigma, c₀]
    simpa only [sub_sub] using
      (rpow_sourcePerronLine_le_exp_two_mul hX halpha0
        (mul_nonneg (by norm_num) hbeta0 : 0 ≤ 2 * beta))
  have hkernelBound : ∀ t : ℝ, ‖kernel t‖ ≤ K := by
    intro t
    let s : ℂ := (sigma : ℂ) + I * (t : ℂ)
    have hsRe : s.re = sigma := by simp [s]
    have hsNorm : sigma ≤ ‖s‖ := by
      have hre := Complex.abs_re_le_norm s
      simpa only [hsRe, abs_of_pos hsigma] using hre
    have hsNormPos : 0 < ‖s‖ := hsigma.trans_le hsNorm
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hpowNorm : ‖(X : ℂ) ^ s‖ = (X : ℝ) ^ sigma := by
      have hcast : (X : ℂ) = ((X : ℝ) : ℂ) := by norm_num
      rw [hcast]
      simpa only [hsRe] using
        Complex.norm_cpow_eq_rpow_re_of_pos hXpos s
    dsimp only [kernel]
    change ‖(X : ℂ) ^ s / s‖ ≤ K
    rw [norm_div, hpowNorm]
    calc
      (X : ℝ) ^ sigma / ‖s‖ ≤ (Real.exp 2 * X) / ‖s‖ :=
        div_le_div_of_nonneg_right hpow hsNormPos.le
      _ ≤ (Real.exp 2 * X) / (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num)
          (hsigmaHalf.trans hsNorm)
      _ = K := by
        dsimp only [K, gsA10FixedHighPerronKernelScale]
        ring
  have hFbound : ∀ t, |t| ≤ T → ‖F t‖ ≤ M * K := by
    intro t ht
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul (hlowHighBound t ht) (hkernelBound t)
      (norm_nonneg _) hM
  have hraw := hvertical hmul hbound y X Q S beta T (M * K) F
    hX hQ hQy hS hlogCβ hbeta0 hT hMK hFcont hFbound
  have hsplit := gsA10LambdaVerticalSplitError_fixedHigh_le
    (y := y) (X := X) (show 1 ≤ X by omega) hlogyPos hbeta0 hbeta
  have hcorr :
      2 * T * (M * K) *
          gsA10LambdaVerticalSplitError y X (c₀ - 2 * beta) c₀ ≤
        2 * T * (M * K) *
          ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
            (2 * gsA10PrimeLambdaHarmonicBudget X *
                gsA10HigherPrimePowerGeometricMass y X +
              (gsA10HigherPrimePowerGeometricMass y X) ^ 2)) := by
    exact mul_le_mul_of_nonneg_left (by
      simpa only [c₀] using hsplit)
      (mul_nonneg (mul_nonneg (by norm_num) hT.le) hMK)
  have hverticalScalar := hraw.trans (add_le_add_right hcorr _)
  have hhigh : 1 < (c₀ - beta) + beta := by
    simpa only [sub_add_cancel] using hcStrict
  have hlow : 0 < c₀ - beta - alpha - beta := by
    dsimp only [sigma] at hsigma
    linarith
  have hfour := gsA10TwoBlockTailoredPerronIntegral_eq_fourFactors
    hmul hbound P₁ P₂ y X (c₀ - beta) alpha beta T hT.le hlow hhigh
  have hLowPoint (t : ℝ) :
      (((c₀ - beta - alpha - beta : ℝ) : ℂ) + (t : ℂ) * I) =
        (sigma : ℂ) + I * (t : ℂ) := by
    apply Complex.ext
    · simp [sigma]
      ring
    · simp
  have hHighPoint (t : ℝ) :
      (((c₀ - beta - alpha - beta : ℝ) : ℂ) + (t : ℂ) * I) +
          ((alpha + 2 * beta : ℝ) : ℂ) =
        (c₀ : ℂ) + I * (t : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, one_mul, add_zero, zero_add,
        sub_zero] <;> ring
  have hWindowLowPoint (t : ℝ) :
      (((c₀ - beta - alpha - beta : ℝ) : ℂ) + (t : ℂ) * I) +
          (alpha : ℂ) =
        ((c₀ - 2 * beta : ℝ) : ℂ) + I * (t : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, one_mul, add_zero, zero_add,
        sub_zero] <;> ring
  have hcontour :
      gsA10TwoBlockMovingPerronIntegral f hmul P₁ P₂ y X alpha beta T =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t in -T..T,
            F t *
              LSeries
                (gsA10LambdaWindow
                  (gsA9HighGeneralizedMangoldt hmul y) y X)
                (((c₀ - 2 * beta : ℝ) : ℂ) + I * (t : ℂ)) *
              LSeries
                (gsA10LambdaWindow
                  (gsA9HighGeneralizedMangoldt hmul y) y X)
                ((c₀ : ℂ) + I * (t : ℂ)) := by
    unfold gsA10TwoBlockMovingPerronIntegral
    rw [hfour]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp only
    rw [hHighPoint t, hWindowLowPoint t, hLowPoint t]
    dsimp only [F, lowHigh, kernel]
    ring
  rw [hcontour, norm_mul]
  have hscalar :
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hpi]
  rw [hscalar]
  exact mul_le_mul_of_nonneg_left (by
    simpa only [M, K, c₀] using hverticalScalar)
    (inv_nonneg.mpr (by positivity))

/-- The whole alpha--beta rectangle of actual moving Perron integrals is
controlled by one restored weighted-Schur budget at the upper beta edge.
This is generic in the selected two-block predicates. -/
theorem exists_norm_gsA10TwoBlockMovingPerronIntegrated_fixedHigh_restored_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
        {y A X Q S : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
        (hQ : 3 ≤ Q) (hQy : Q ≤ y) (hS : 101 ≤ S)
        (hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {eta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
        (heta0 : 0 ≤ eta)
        (heta : eta ≤ (Real.log (y : ℝ))⁻¹)
        (hT : 0 < T) (hTX : T ≤ X)
        (hdist : ∀ t : ℝ, |t| ≤ T →
          (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X),
        ‖gsA10TwoBlockMovingPerronIntegrated
            f hmul P₁ P₂ y X eta T‖ ≤
          2 * eta ^ 2 *
            gsA10RestoredFixedHighPerronBudget Cβ Q S y A X eta T := by
  obtain ⟨Cβ, hCβ, hpoint⟩ :=
    exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ hsmallOutside y A X Q S hy hyX hX
    hQ hQy hS hlogCβ eta T hlogy heta0 heta hT hTX hdist
  unfold gsA10TwoBlockMovingPerronIntegrated
  apply norm_two_mul_doubleIntervalIntegral_le_two_mul_sq_mul_of_bound heta0
  intro alpha halpha beta hbeta
  have hraw := hpoint hmul hbound P₁ P₂ hsmallOutside
    hy hX hQ hQy hS hlogCβ hlogy
    halpha.1 (halpha.2.trans heta) hbeta.1 (hbeta.2.trans heta) hT hTX
    hdist
  have hraw' :
      ‖gsA10TwoBlockMovingPerronIntegral
          f hmul P₁ P₂ y X alpha beta T‖ ≤
        gsA10RestoredFixedHighPerronBudget Cβ Q S y A X beta T := by
    simpa only [gsA10RestoredFixedHighPerronBudget] using hraw
  exact hraw'.trans
    (gsA10RestoredFixedHighPerronBudget_mono_beta
      hCβ hX (by omega) hyX hT hbeta.2)

/-- Canonical-large specialization of the restored weighted-Schur contour.
All primes below `23` are in the common outside predicate by construction. -/
theorem exists_norm_gsA10CanonicalLargeMovingPerronIntegral_fixedHigh_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        {K : ℕ} (hK : 5 ≤ K)
        {y A X Q S : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
        (hnonpret : MRArchimedeanNonpretentious f A X)
        (hQ : 3 ≤ Q) (hQy : Q ≤ y) (hS : 101 ≤ S)
        (hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {alpha beta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
        (halpha0 : 0 ≤ alpha)
        (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (hbeta0 : 0 ≤ beta)
        (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
        (hT : 0 < T) (hTX : T ≤ X),
        ‖gsA10TwoBlockMovingPerronIntegral f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta T‖ ≤
          (2 * Real.pi)⁻¹ *
            ((gsA10RestoredFixedHighHalaszEnvelope A X *
                gsA10FixedHighPerronKernelScale X) *
                  (gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
                    (2 * beta) T) ^ ((1 : ℝ) / 2) *
                (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X T) ^
                  ((1 : ℝ) / 2) +
              2 * T *
                (gsA10RestoredFixedHighHalaszEnvelope A X *
                  gsA10FixedHighPerronKernelScale X) *
                ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
                  (2 * gsA10PrimeLambdaHarmonicBudget X *
                      gsA10HigherPrimePowerGeometricMass y X +
                    (gsA10HigherPrimePowerGeometricMass y X) ^ 2))) := by
  obtain ⟨Cβ, hCβ, hbase⟩ :=
    exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound K hK y A X Q S hy hX hnonpret hQ hQy hS hlogCβ
    alpha beta T hlogy halpha0 halpha hbeta0 hbeta hT hTX
  have hsmall : ∀ p ∈ gsA9SmallPrimeFinset,
      mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
        (gsA10CanonicalLargeSecondBlock K) p := by
    intro p hp
    have hpRaw : p < 23 ∧ p.Prime := by
      simpa only [gsA9SmallPrimeFinset, Finset.mem_filter,
        Finset.mem_range] using hp
    have hpData : p.Prime ∧ p < 23 := ⟨hpRaw.2, hpRaw.1⟩
    exact Erdos67.mrTwoBlockOutside_gsA10CanonicalLarge_of_le_twentyThree
      hK hpData.1 hpData.2.le
  exact hbase hmul hbound
    (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
      (gsA10CanonicalLargeSecondBlock K))
    (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K)) hsmall
    hy hX hQ hQy hS hlogCβ hlogy
    halpha0 halpha hbeta0 hbeta hT hTX
    (fun t ht ↦ hnonpret t (ht.trans hTX))

/-- The canonical-large contour theorem with its numerical right-hand side
packaged as one transparent definition. -/
theorem exists_norm_gsA10CanonicalLargeMovingPerronIntegral_le_restoredBudget :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        {K : ℕ} (hK : 5 ≤ K)
        {y A X Q S : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
        (hnonpret : MRArchimedeanNonpretentious f A X)
        (hQ : 3 ≤ Q) (hQy : Q ≤ y) (hS : 101 ≤ S)
        (hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        {alpha beta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
        (halpha0 : 0 ≤ alpha)
        (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
        (hbeta0 : 0 ≤ beta)
        (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
        (hT : 0 < T) (hTX : T ≤ X),
        ‖gsA10TwoBlockMovingPerronIntegral f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta T‖ ≤
          gsA10RestoredFixedHighPerronBudget Cβ Q S y A X beta T := by
  obtain ⟨Cβ, hCβ, hbase⟩ :=
    exists_norm_gsA10CanonicalLargeMovingPerronIntegral_fixedHigh_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound K hK y A X Q S hy hX hnonpret hQ hQy hS hlogCβ
    alpha beta T hlogy halpha0 halpha hbeta0 hbeta hT hTX
  simpa only [gsA10RestoredFixedHighPerronBudget] using
    (hbase hmul hbound hK hy hX hnonpret hQ hQy hS hlogCβ
      hlogy halpha0 halpha hbeta0 hbeta hT hTX)

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le
#print axioms
  Erdos67.MRHalaszBands.gsA10RestoredFixedHighPerronBudget_mono_beta
#print axioms
  Erdos67.MRHalaszBands.exists_norm_gsA10TwoBlockMovingPerronIntegrated_fixedHigh_restored_le
#print axioms
  Erdos67.MRHalaszBands.exists_norm_gsA10CanonicalLargeMovingPerronIntegral_fixedHigh_le
#print axioms
  Erdos67.MRHalaszBands.exists_norm_gsA10CanonicalLargeMovingPerronIntegral_le_restoredBudget
