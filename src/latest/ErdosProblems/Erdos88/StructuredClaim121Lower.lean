import ErdosProblems.Erdos88.GaussianMatrixLower
import ErdosProblems.Erdos88.StructuredClaim121Nonuniform
import ErdosProblems.Erdos88.StructuredClaims

/-!
# The Gaussian lower input to KSSS Claim 12.1

The nonuniform Gaussian upper theorem and the signed ordered lower theorem
together give the local interval-ratio hypothesis actually consumed by the
reverse Esseen inequality.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace Erdos88.GaussianQuadratic

open BooleanSlices

attribute [local instance] Classical.propDecidable

/-- A quantitative continuity form of the elementary fact that a positive
average of a density forces a positive pointwise value.  The slightly larger
`R * eps` window is then flat enough that all density values differ by at
most a factor two.  This is the fixed-`K` input needed in the lower half of
Claim 12.1. -/
lemma densityRatioOn_two_of_holder_and_smallBall_lower
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (p : ℝ → ℝ)
    (hdens : Erdos88.Esseen.HasContinuousDensity mu p)
    {x eps R c L : ℝ} (heps : 0 < eps) (hR : 1 ≤ R)
    (hc : 0 < c) (hL : 0 ≤ L)
    (hholder : ∀ y z : ℝ,
      |p y - p z| ≤ L * |y - z| ^ (1 / 4 : ℝ))
    (hlower : c * eps ≤ Erdos88.Esseen.smallBall mu eps x)
    (hosc : L * ((R + 1) * eps) ^ (1 / 4 : ℝ) ≤ c / 8) :
    Erdos88.Esseen.DensityRatioOn p x eps R 2 := by
  have hwindowNonneg : 0 ≤ (R + 1) * eps := by positivity
  have hcentral (y : ℝ) (hy : y ∈ Set.Icc (x - eps) (x + eps)) :
      p y ≤ p x + c / 8 := by
    have hdist : |y - x| ≤ (R + 1) * eps := by
      rw [abs_le]
      constructor <;> nlinarith [hy.1, hy.2,
        mul_nonneg (by linarith : 0 ≤ R) heps.le]
    have hpow := Real.rpow_le_rpow (abs_nonneg (y - x)) hdist
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hmod : |p y - p x| ≤ c / 8 := by
      exact (hholder y x).trans
        ((mul_le_mul_of_nonneg_left hpow hL).trans hosc)
    linarith [le_abs_self (p y - p x)]
  have hint : (∫ y in (x - eps)..(x + eps), p y) ≤
      ∫ _y in (x - eps)..(x + eps), p x + c / 8 := by
    exact intervalIntegral.integral_mono_on (by linarith)
      (hdens.intervalIntegrable _ _) intervalIntegrable_const hcentral
  have hlowerInt : c * eps ≤ ∫ y in (x - eps)..(x + eps), p y := by
    simpa only [hdens.smallBall_eq_integral eps x heps.le] using hlower
  rw [intervalIntegral.integral_const] at hint
  simp only [smul_eq_mul] at hint
  have hpx : 3 * c / 8 ≤ p x := by
    have : c * eps ≤ (x + eps - (x - eps)) * (p x + c / 8) :=
      hlowerInt.trans hint
    nlinarith
  intro y z
  have hnear (u : Set.Icc (x - R * eps) (x + R * eps)) :
      |u.1 - x| ≤ (R + 1) * eps := by
    rw [abs_le]
    constructor <;> nlinarith [u.2.1, u.2.2, heps.le]
  have hvariation (u : Set.Icc (x - R * eps) (x + R * eps)) :
      |p u.1 - p x| ≤ c / 8 := by
    have hpow := Real.rpow_le_rpow (abs_nonneg (u.1 - x)) (hnear u)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    exact (hholder u.1 x).trans
      ((mul_le_mul_of_nonneg_left hpow hL).trans hosc)
  have hyUpper : p y.1 ≤ p x + c / 8 := by
    linarith [le_abs_self (p y.1 - p x), hvariation y]
  have hzLower : p x - c / 8 ≤ p z.1 := by
    linarith [neg_le_abs (p z.1 - p x), hvariation z]
  nlinarith

/-- Relative robust rank three supplies one density whose `1/4`-Hölder
constant depends only on the relative rank parameter, not on the center,
linear coefficients, dimension, or standard deviation. -/
theorem exists_holderDensity_gaussianQuadratic_of_relative_robustRankThree
    {rho : ℝ} (hrho : 0 < rho) {n : ℕ} (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (hrob : RobustRankAt 3 (rho * frobeniusSq F) F) :
    let L := threeSpectralQuarterMass (min rho 1 / 192) / Real.pi
    ∃ p : ℝ → ℝ,
      Erdos88.Esseen.HasContinuousDensity
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)) p ∧
        ∀ x y : ℝ, |p x - p y| ≤ L * |x - y| ^ (1 / 4 : ℝ) := by
  let a : Fin n → ℝ := fun i ↦ eigenLinearCoefficient hF f i / sigma
  let lam : Fin n → ℝ := fun i ↦ hF.eigenvalues i / sigma
  let s : ℝ := min rho 1 / 192
  let p : ℝ → ℝ :=
    inverseFourierDensityCandidate (diagonalCenteredCharProduct a lam)
  have hsum : totalVariance a lam = 1 :=
    totalVariance_normalized_eigenbasis hF f hsigma hsigmaSq
  have hrobTwo : RobustRankAt 2 (rho * frobeniusSq F) F :=
    robustRankAt_anti_rank (by norm_num) hrob
  have htail : ∀ S : Finset (Fin n), S.card ≤ 2 →
      rho * (∑ i, (lam i) ^ 2) ≤ ∑ i with i ∉ S, (lam i) ^ 2 := by
    intro S hS
    have hraw := robustRankAt_eigenvalue_tail hF hrobTwo S hS
    have hsigmaSqPos : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
    have htotal : (∑ i, (lam i) ^ 2) = frobeniusSq F / sigma ^ 2 := by
      dsimp only [lam]
      simp_rw [div_pow]
      rw [← Finset.sum_div, sum_sq_eigenvalues_eq_frobeniusSq]
    have hout : (∑ i with i ∉ S, (lam i) ^ 2) =
        (∑ i with i ∉ S, (hF.eigenvalues i) ^ 2) / sigma ^ 2 := by
      dsimp only [lam]
      simp_rw [div_pow]
      rw [← Finset.sum_div]
    rw [htotal, hout]
    calc
      rho * (frobeniusSq F / sigma ^ 2) =
          (rho * frobeniusSq F) / sigma ^ 2 := by rw [mul_div_assoc]
      _ ≤ (∑ i with i ∉ S, (hF.eigenvalues i) ^ 2) / sigma ^ 2 :=
        (div_le_div_iff_of_pos_right hsigmaSqPos).2 hraw
  have hs : 0 < s := by dsimp only [s]; positivity
  have hmod : ∀ t, diagonalCharModulus a lam t ≤
      threeSpectralEnvelope s t := by
    intro t
    exact diagonalCharModulus_le_relative_rankTwoEnvelope
      a lam hsum hrho htail t
  have hchar : Integrable (diagonalCenteredCharProduct a lam) :=
    diagonalCenteredCharProduct_integrable_of_modulus_le_threeEnvelope
      a lam hs hmod
  have hdensDiagonal : Erdos88.Esseen.HasContinuousDensity
      (diagonalCenteredLaw a lam) p := by
    letI : IsProbabilityMeasure (diagonalCenteredLaw a lam) :=
      diagonalCenteredLaw_isProbabilityMeasure a lam
    have h := hasContinuousDensity_inverseFourierDensityCandidate
      (diagonalCenteredLaw a lam) (by
        rw [charFun_diagonalCenteredLaw]
        exact hchar)
    simpa only [p, charFun_diagonalCenteredLaw] using h
  have hdens : Erdos88.Esseen.HasContinuousDensity
      ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)) p := by
    rw [gaussianQuadraticCenteredLaw_map_div_eq_diagonal f hF hsigma.ne']
    exact hdensDiagonal
  refine ⟨p, hdens, ?_⟩
  intro x y
  simpa only [s, p] using
    inverseFourierDensityCandidate_holder_of_modulus_le_threeEnvelope
      a lam hs hmod x y

/-- Full normalized Gaussian input for the lower half of Claim 12.1.  The
sign depends only on the quadratic matrix, while the ratio constant is
uniform in the center and in the interval radius. -/
theorem exists_sign_gaussian_smallBallRatioOn_of_nonuniform
    (h52 : KSSSGaussianNonuniformUpper)
    {rho : ℝ} (hrho : 0 < rho)
    {n : ℕ} [NeZero n] (f : Fin n → ℝ)
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian)
    {sigma M x eps R : ℝ} (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (hFpos : 0 < frobeniusSq F)
    (hrob : RobustRankAt 3 (rho * frobeniusSq F) F)
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (heps : 0 < eps) (hepsOne : eps ≤ 1) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        let nu := (gaussianQuadraticCenteredLaw f F).map
          (fun z ↦ z / sigma)
        orderedGaussianLowerConstant M * eps ≤
            Erdos88.Esseen.smallBall nu eps (s * x) ∧
          Erdos88.Esseen.SmallBallRatioOn nu (s * x) eps R
            ((1 / eta) / orderedGaussianLowerConstant M) := by
  obtain ⟨eta, heta, hetaOne, hupperRaw⟩ := h52 rho hrho
  have hupper : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          eps y ≤ (1 / eta) * eps := by
    intro y
    have hraw := hupperRaw f hF hsigma hsigmaSq hFpos hrob heps hepsOne y
    have hexp : Real.exp (-eta * |y|) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heta.le) (abs_nonneg y)
    calc
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          eps y ≤ (eps / eta) * Real.exp (-eta * |y|) := hraw
      _ ≤ eps / eta := by
        exact mul_le_of_le_one_right (div_nonneg heps.le heta.le) hexp
      _ = (1 / eta) * eps := by ring
  obtain ⟨s, hs, hlower, hratio⟩ :=
    exists_sign_gaussianQuadraticCenteredLaw_smallBallRatioOn
      f hF hsigma hsigmaSq hM hx hxM heps hepsOne
        (by positivity : 0 ≤ 1 / eta) hupper
  exact ⟨eta, heta, hetaOne, s, hs, hlower, hratio⟩

/-- Source-shaped lower half of Claim 12.1 at one fixed product slice, for a
fixed instance of the normalized Gaussian upper estimate. -/
theorem exists_sign_productSlice_lower_of_raw_fourier_and_gaussianUpper
    {n m : ℕ} [NeZero n]
    (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian)
    {sigma B M x R nuCut E eta : ℝ}
    (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (heta : 0 < eta) (hetaOne : eta < 1)
    (hupperRaw : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B / sigma) y ≤
        ((B / sigma) / eta) * Real.exp (-eta * |y|))
    (hB : 0 < B) (hBsigma : B ≤ sigma)
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (hR : 4 ≤ R) (hcut : 2 / B ≤ nuCut)
    (hraw : (∫ t in -nuCut..nuCut,
      ‖finiteCharacteristic
            (productSliceQuadratic P ell (-trace F) f F) t -
        gaussianQuadraticCharacteristic (-trace F) f F t‖) ≤ E) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      let c := orderedGaussianLowerConstant M
      let K := 1 + (1 / eta) / c
      (1 / 8 : ℝ) * (c * (B / sigma)) -
          Erdos88.Esseen.relativeEsseenConstant *
            ((((1 / eta) * (B / sigma)) / R) +
              (B / sigma) * (sigma * E)) ≤
        Erdos88.Esseen.smallBall
          (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
            (productSliceQuadratic P ell (-trace F) f F))
          ((10000 * K) * B) (sigma * (s * x)) := by
  let eps := B / sigma
  let law := (gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)
  let c := orderedGaussianLowerConstant M
  let K₀ := (1 / eta) / c
  let K := 1 + K₀
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hepsOne : eps ≤ 1 := by
    dsimp only [eps]
    exact (div_le_one hsigma).2 hBsigma
  have hc : 0 < c := by
    dsimp only [c]
    exact orderedGaussianLowerConstant_pos hM
  have hupper : ∀ y : ℝ,
      Erdos88.Esseen.smallBall law eps y ≤ (1 / eta) * eps := by
    intro y
    have hbase := hupperRaw y
    have hexp : Real.exp (-eta * |y|) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heta.le) (abs_nonneg y))
    calc
      Erdos88.Esseen.smallBall law eps y ≤
          (eps / eta) * Real.exp (-eta * |y|) := by
        simpa only [law] using hbase
      _ ≤ eps / eta :=
        mul_le_of_le_one_right (div_nonneg heps.le heta.le) hexp
      _ = (1 / eta) * eps := by ring
  obtain ⟨s, hs, hlower, hratio⟩ :=
    exists_sign_gaussianQuadraticCenteredLaw_smallBallRatioOn
      f hF hsigma hsigmaSq hM hx hxM heps hepsOne
        (by positivity : 0 ≤ 1 / eta) (by simpa only [law] using hupper)
  have hK₀0 : 0 ≤ K₀ := by
    dsimp only [K₀]
    positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  have hratioK : Erdos88.Esseen.SmallBallRatioOn law (s * x) eps R K := by
    intro y hy
    have hbase := hratio y hy
    calc
      Erdos88.Esseen.smallBall law eps y ≤
          K₀ * Erdos88.Esseen.smallBall law eps (s * x) := by
        simpa only [law, K₀, c] using hbase
      _ ≤ K * Erdos88.Esseen.smallBall law eps (s * x) := by
        apply mul_le_mul_of_nonneg_right _
          (Erdos88.Esseen.smallBall_nonneg law eps (s * x))
        dsimp only [K]
        linarith
  have hcut' : 2 / (eps * sigma) ≤ nuCut := by
    convert hcut using 1
    dsimp only [eps]
    field_simp [hsigma.ne']
  let mu := Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
    (fun w ↦ productSliceQuadratic P ell (-trace F) f F w / sigma)
  have hfourier : Erdos88.Esseen.fourierError mu law eps ≤ sigma * E := by
    calc
      Erdos88.Esseen.fourierError mu law eps ≤
          sigma * (∫ t in -nuCut..nuCut,
            ‖finiteCharacteristic
                  (productSliceQuadratic P ell (-trace F) f F) t -
              gaussianQuadraticCharacteristic (-trace F) f F t‖) := by
        dsimp only [mu, law]
        exact fourierError_productSlice_normalized_le_mul_raw
          P ell f F hsigma heps hcut'
      _ ≤ sigma * E := mul_le_mul_of_nonneg_left hraw hsigma.le
  have hcenter : sigma * (s * x) / sigma = s * x := by
    field_simp [hsigma.ne']
  have hratioRaw : Erdos88.Esseen.SmallBallRatioOn law
      (sigma * (s * x) / sigma) (B / sigma) R K := by
    rw [hcenter]
    simpa only [eps] using hratioK
  have htransfer :=
    smallBall_productSlice_ge_of_normalized_gaussianSmallBallRatio
      P ell f hsigma hB hK hR (sigma * (s * x)) hratioRaw (by
        simpa only [mu, law, eps] using hfourier)
  letI : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  letI : IsProbabilityMeasure law := by
    dsimp only [law]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hconc : Erdos88.Esseen.concentration law eps ≤
      (1 / eta) * eps :=
    Erdos88.Esseen.concentration_le_of_smallBall_le law hupper
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hnoise : Erdos88.Esseen.concentration law eps / R +
        eps * (sigma * E) ≤
      ((1 / eta) * eps) / R + eps * (sigma * E) := by
    exact add_le_add ((div_le_div_iff_of_pos_right hRpos).2 hconc) le_rfl
  have hlower' : c * eps ≤ Erdos88.Esseen.smallBall law eps (s * x) := by
    simpa only [law, c, eps] using hlower
  refine ⟨s, hs, ?_⟩
  dsimp only [c, K]
  have hmain :
      (1 / 8 : ℝ) * (c * eps) -
          Erdos88.Esseen.relativeEsseenConstant *
            (((1 / eta) * eps) / R + eps * (sigma * E)) ≤
        (1 / 8 : ℝ) * Erdos88.Esseen.smallBall law eps (s * x) -
          Erdos88.Esseen.relativeEsseenConstant *
            (Erdos88.Esseen.concentration law eps / R +
              eps * (sigma * E)) := by
    exact sub_le_sub
      (mul_le_mul_of_nonneg_left hlower' (by norm_num))
      (mul_le_mul_of_nonneg_left hnoise
        Erdos88.Esseen.relativeEsseenConstant_nonneg)
  apply hmain.trans
  simpa only [law, eps, c, K₀, K, hcenter] using htransfer

/-- Robust-rank wrapper around the fixed-Gaussian-upper Claim 12.1 lower
transfer. -/
theorem exists_sign_productSlice_lower_of_raw_fourier_and_gaussianNonuniform
    (h52 : KSSSGaussianNonuniformUpper)
    {rho : ℝ} (hrho : 0 < rho)
    {n m : ℕ} [NeZero n]
    (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian)
    {sigma B M x R nuCut E : ℝ}
    (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (hFpos : 0 < frobeniusSq F)
    (hrob : RobustRankAt 3 (rho * frobeniusSq F) F)
    (hB : 0 < B) (hBsigma : B ≤ sigma)
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (hR : 4 ≤ R) (hcut : 2 / B ≤ nuCut)
    (hraw : (∫ t in -nuCut..nuCut,
      ‖finiteCharacteristic
            (productSliceQuadratic P ell (-trace F) f F) t -
        gaussianQuadraticCharacteristic (-trace F) f F t‖) ≤ E) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        let c := orderedGaussianLowerConstant M
        let K := 1 + (1 / eta) / c
        (1 / 8 : ℝ) * (c * (B / sigma)) -
            Erdos88.Esseen.relativeEsseenConstant *
              ((((1 / eta) * (B / sigma)) / R) +
                (B / sigma) * (sigma * E)) ≤
          Erdos88.Esseen.smallBall
            (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
              (productSliceQuadratic P ell (-trace F) f F))
            ((10000 * K) * B) (sigma * (s * x)) := by
  obtain ⟨eta, heta, hetaOne, hupper⟩ := h52 rho hrho
  obtain ⟨s, hs, hbound⟩ :=
    exists_sign_productSlice_lower_of_raw_fourier_and_gaussianUpper
      P ell f hF hsigma hsigmaSq heta hetaOne
        (fun y ↦ hupper f hF hsigma hsigmaSq hFpos hrob
          (div_pos hB hsigma) ((div_le_one hsigma).2 hBsigma) y)
        hB hBsigma hM hx hxM hR hcut hraw
  exact ⟨eta, heta, hetaOne, s, hs, hbound⟩

/-- Positive fixed-slice form of the preceding estimate.  The comparison
window `R` is chosen after the Gaussian constant `eta`; the Fourier error is
small enough that the two reverse-Esseen losses consume at most half of the
Gaussian interval mass. -/
theorem exists_sign_productSlice_lower_positive_of_gaussianUpper
    {n m : ℕ} [NeZero n]
    (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian)
    {sigma B M x nuCut E eta : ℝ}
    (hsigma : 0 < sigma)
    (hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f)
    (heta : 0 < eta) (hetaOne : eta < 1)
    (hupperRaw : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B / sigma) y ≤
        ((B / sigma) / eta) * Real.exp (-eta * |y|))
    (hB : 0 < B) (hBsigma : B ≤ sigma)
    (hM : 0 ≤ M) (hx : 0 ≤ x) (hxM : x ≤ M)
    (hcut : 2 / B ≤ nuCut)
    (hraw : (∫ t in -nuCut..nuCut,
      ‖finiteCharacteristic
            (productSliceQuadratic P ell (-trace F) f F) t -
        gaussianQuadraticCharacteristic (-trace F) f F t‖) ≤ E)
    (herror : Erdos88.Esseen.relativeEsseenConstant * (sigma * E) ≤
      orderedGaussianLowerConstant M / 32) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      let c := orderedGaussianLowerConstant M
      let K := 1 + (1 / eta) / c
      c / 16 * (B / sigma) ≤
        Erdos88.Esseen.smallBall
          (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
            (productSliceQuadratic P ell (-trace F) f F))
          ((10000 * K) * B) (sigma * (s * x)) := by
  let c := orderedGaussianLowerConstant M
  let C₀ := Erdos88.Esseen.relativeEsseenConstant
  let R := max 4 (32 * C₀ / (c * eta))
  have hc : 0 < c := by
    dsimp only [c]
    exact orderedGaussianLowerConstant_pos hM
  have hC₀ : 0 ≤ C₀ := by
    dsimp only [C₀]
    exact Erdos88.Esseen.relativeEsseenConstant_nonneg
  have hR : 4 ≤ R := by dsimp only [R]; exact le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRratio : 32 * C₀ / (c * eta) ≤ R := by
    dsimp only [R]
    exact le_max_right _ _
  have hcross : 32 * C₀ ≤ R * (c * eta) := by
    exact (div_le_iff₀ (mul_pos hc heta)).1 hRratio
  have hcoef : C₀ * (1 / eta) / R ≤ c / 32 := by
    have hbefore : C₀ / eta ≤ c * R / 32 := by
      apply (div_le_iff₀ heta).2
      nlinarith
    calc
      C₀ * (1 / eta) / R = (C₀ / eta) / R := by ring
      _ ≤ (c * R / 32) / R :=
        div_le_div_of_nonneg_right hbefore hRpos.le
      _ = c / 32 := by field_simp [hRpos.ne']
  obtain ⟨s, hs, hbase⟩ :=
    exists_sign_productSlice_lower_of_raw_fourier_and_gaussianUpper
      P ell f hF hsigma hsigmaSq heta hetaOne hupperRaw
        hB hBsigma hM hx hxM hR hcut hraw
  refine ⟨s, hs, ?_⟩
  let eps := B / sigma
  have heps : 0 ≤ eps := by dsimp only [eps]; positivity
  have hnear : C₀ * (((1 / eta) * eps) / R) ≤
      c * eps / 32 := by
    calc
      C₀ * (((1 / eta) * eps) / R) =
          (C₀ * (1 / eta) / R) * eps := by ring
      _ ≤ (c / 32) * eps := mul_le_mul_of_nonneg_right hcoef heps
      _ = c * eps / 32 := by ring
  have hfar : C₀ * (eps * (sigma * E)) ≤ c * eps / 32 := by
    calc
      C₀ * (eps * (sigma * E)) =
          (C₀ * (sigma * E)) * eps := by ring
      _ ≤ (c / 32) * eps := by
        apply mul_le_mul_of_nonneg_right _ heps
        simpa only [C₀, c] using herror
      _ = c * eps / 32 := by ring
  have hloss : C₀ *
      ((((1 / eta) * eps) / R) + eps * (sigma * E)) ≤
        c * eps / 16 := by
    calc
      C₀ * ((((1 / eta) * eps) / R) + eps * (sigma * E)) =
          C₀ * (((1 / eta) * eps) / R) +
            C₀ * (eps * (sigma * E)) := by ring
      _ ≤ c * eps / 32 + c * eps / 32 := add_le_add hnear hfar
      _ = c * eps / 16 := by ring
  dsimp only [c] at hbase ⊢
  change orderedGaussianLowerConstant M / 16 * eps ≤ _
  apply le_trans ?_ hbase
  dsimp only [C₀, c] at hloss
  nlinarith

/-- Fixed-sign version of the positive Claim 12.1 transfer.  This is the
form needed for averaging: the Gaussian lower input can be supplied by a
sign chosen once from the quadratic matrix. -/
theorem productSlice_lower_positive_of_gaussianUpper_at_sign
    {n m : ℕ} [NeZero n]
    (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    {sigma B M x nuCut E eta s : ℝ}
    (hsigma : 0 < sigma)
    (hgaussianLower : orderedGaussianLowerConstant M * (B / sigma) ≤
      Erdos88.Esseen.smallBall
        ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
        (B / sigma) (s * x))
    (heta : 0 < eta)
    (hupperRaw : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B / sigma) y ≤
        ((B / sigma) / eta) * Real.exp (-eta * |y|))
    (hB : 0 < B) (hBsigma : B ≤ sigma)
    (hM : 0 ≤ M) (hcut : 2 / B ≤ nuCut)
    (hraw : (∫ t in -nuCut..nuCut,
      ‖finiteCharacteristic
            (productSliceQuadratic P ell (-trace F) f F) t -
        gaussianQuadraticCharacteristic (-trace F) f F t‖) ≤ E)
    (herror : Erdos88.Esseen.relativeEsseenConstant * (sigma * E) ≤
      orderedGaussianLowerConstant M / 32) :
    let c := orderedGaussianLowerConstant M
    let K := 1 + (1 / eta) / c
    c / 16 * (B / sigma) ≤
      Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F))
        ((10000 * K) * B) (sigma * (s * x)) := by
  let eps := B / sigma
  let law := (gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)
  let c := orderedGaussianLowerConstant M
  let C₀ := Erdos88.Esseen.relativeEsseenConstant
  let K₀ := (1 / eta) / c
  let K := 1 + K₀
  let R := max 4 (32 * C₀ / (c * eta))
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hc : 0 < c := by
    dsimp only [c]
    exact orderedGaussianLowerConstant_pos hM
  have hC₀ : 0 ≤ C₀ := by
    dsimp only [C₀]
    exact Erdos88.Esseen.relativeEsseenConstant_nonneg
  have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  have hR : 4 ≤ R := by dsimp only [R]; exact le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hRratio : 32 * C₀ / (c * eta) ≤ R := by
    dsimp only [R]
    exact le_max_right _ _
  have hcross : 32 * C₀ ≤ R * (c * eta) :=
    (div_le_iff₀ (mul_pos hc heta)).1 hRratio
  have hcoef : C₀ * (1 / eta) / R ≤ c / 32 := by
    have hbefore : C₀ / eta ≤ c * R / 32 := by
      apply (div_le_iff₀ heta).2
      nlinarith
    calc
      C₀ * (1 / eta) / R = (C₀ / eta) / R := by ring
      _ ≤ (c * R / 32) / R :=
        div_le_div_of_nonneg_right hbefore hRpos.le
      _ = c / 32 := by field_simp [hRpos.ne']
  have hupper : ∀ y : ℝ,
      Erdos88.Esseen.smallBall law eps y ≤ (1 / eta) * eps := by
    intro y
    have hbase := hupperRaw y
    have hexp : Real.exp (-eta * |y|) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heta.le) (abs_nonneg y))
    calc
      Erdos88.Esseen.smallBall law eps y ≤
          (eps / eta) * Real.exp (-eta * |y|) := by
        simpa only [law, eps] using hbase
      _ ≤ eps / eta :=
        mul_le_of_le_one_right (div_nonneg heps.le heta.le) hexp
      _ = (1 / eta) * eps := by ring
  have hratio : Erdos88.Esseen.SmallBallRatioOn law (s * x) eps R K := by
    intro y _hy
    calc
      Erdos88.Esseen.smallBall law eps y ≤ (1 / eta) * eps := hupper y
      _ = K₀ * (c * eps) := by
        dsimp only [K₀]
        field_simp [hc.ne']
      _ ≤ K₀ * Erdos88.Esseen.smallBall law eps (s * x) := by
        apply mul_le_mul_of_nonneg_left _ hK₀
        simpa only [law, eps, c] using hgaussianLower
      _ ≤ K * Erdos88.Esseen.smallBall law eps (s * x) := by
        apply mul_le_mul_of_nonneg_right _
          (Erdos88.Esseen.smallBall_nonneg law eps (s * x))
        dsimp only [K]
        linarith
  have hcut' : 2 / (eps * sigma) ≤ nuCut := by
    convert hcut using 1
    dsimp only [eps]
    field_simp [hsigma.ne']
  let mu := Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
    (fun w ↦ productSliceQuadratic P ell (-trace F) f F w / sigma)
  have hfourier : Erdos88.Esseen.fourierError mu law eps ≤ sigma * E := by
    calc
      Erdos88.Esseen.fourierError mu law eps ≤
          sigma * (∫ t in -nuCut..nuCut,
            ‖finiteCharacteristic
                  (productSliceQuadratic P ell (-trace F) f F) t -
              gaussianQuadraticCharacteristic (-trace F) f F t‖) := by
        dsimp only [mu, law]
        exact fourierError_productSlice_normalized_le_mul_raw
          P ell f F hsigma heps hcut'
      _ ≤ sigma * E := mul_le_mul_of_nonneg_left hraw hsigma.le
  have hcenter : sigma * (s * x) / sigma = s * x := by
    field_simp [hsigma.ne']
  have hratioRaw : Erdos88.Esseen.SmallBallRatioOn law
      (sigma * (s * x) / sigma) (B / sigma) R K := by
    rw [hcenter]
    simpa only [eps] using hratio
  have htransfer :=
    smallBall_productSlice_ge_of_normalized_gaussianSmallBallRatio
      P ell f hsigma hB hK hR (sigma * (s * x)) hratioRaw (by
        simpa only [mu, law, eps] using hfourier)
  letI : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  letI : IsProbabilityMeasure law := by
    dsimp only [law]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hconc : Erdos88.Esseen.concentration law eps ≤
      (1 / eta) * eps :=
    Erdos88.Esseen.concentration_le_of_smallBall_le law hupper
  have hnoise : Erdos88.Esseen.concentration law eps / R +
        eps * (sigma * E) ≤
      ((1 / eta) * eps) / R + eps * (sigma * E) :=
    add_le_add ((div_le_div_iff_of_pos_right hRpos).2 hconc) le_rfl
  have hnear : C₀ * (((1 / eta) * eps) / R) ≤ c * eps / 32 := by
    calc
      C₀ * (((1 / eta) * eps) / R) =
          (C₀ * (1 / eta) / R) * eps := by ring
      _ ≤ (c / 32) * eps :=
        mul_le_mul_of_nonneg_right hcoef heps.le
      _ = c * eps / 32 := by ring
  have hfar : C₀ * (eps * (sigma * E)) ≤ c * eps / 32 := by
    calc
      C₀ * (eps * (sigma * E)) = (C₀ * (sigma * E)) * eps := by ring
      _ ≤ (c / 32) * eps := by
        apply mul_le_mul_of_nonneg_right _ heps.le
        simpa only [C₀, c] using herror
      _ = c * eps / 32 := by ring
  have hloss : C₀ *
      (Erdos88.Esseen.concentration law eps / R + eps * (sigma * E)) ≤
        c * eps / 16 := by
    calc
      C₀ * (Erdos88.Esseen.concentration law eps / R + eps * (sigma * E)) ≤
          C₀ * (((1 / eta) * eps) / R + eps * (sigma * E)) :=
        mul_le_mul_of_nonneg_left hnoise hC₀
      _ = C₀ * (((1 / eta) * eps) / R) +
          C₀ * (eps * (sigma * E)) := by ring
      _ ≤ c * eps / 32 + c * eps / 32 := add_le_add hnear hfar
      _ = c * eps / 16 := by ring
  have hlower : c * eps ≤
      Erdos88.Esseen.smallBall law eps (s * x) := by
    simpa only [law, eps, c] using hgaussianLower
  dsimp only [c, K]
  have hmain : c / 16 * eps ≤
      (1 / 8 : ℝ) * Erdos88.Esseen.smallBall law eps (s * x) -
        C₀ * (Erdos88.Esseen.concentration law eps / R +
          eps * (sigma * E)) := by
    nlinarith
  apply hmain.trans
  simpa only [law, eps, c, C₀, K₀, K, hcenter] using htransfer

/-- Fixed-window version of the positive Claim 12.1 transfer.  The Gaussian
density is locally flat by a uniform Hölder estimate, so the ratio constant in
Lemma 6.3 is the absolute constant `2`.  The comparison radius may still
depend on the compact center range, but the resulting product-slice window is
always exactly `20000 * B`. -/
theorem productSlice_lower_positive_of_gaussianHolder_at_sign
    {n m : ℕ} [NeZero n]
    (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    {sigma B M x nuCut E eta s R L : ℝ} {p : ℝ → ℝ}
    (hsigma : 0 < sigma)
    (hgaussianLower : orderedGaussianLowerConstant M * (B / sigma) ≤
      Erdos88.Esseen.smallBall
        ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
        (B / sigma) (s * x))
    (hdens : Erdos88.Esseen.HasContinuousDensity
      ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)) p)
    (hL : 0 ≤ L)
    (hholder : ∀ y z : ℝ,
      |p y - p z| ≤ L * |y - z| ^ (1 / 4 : ℝ))
    (hosc : L * ((R + 1) * (B / sigma)) ^ (1 / 4 : ℝ) ≤
      orderedGaussianLowerConstant M / 8)
    (heta : 0 < eta)
    (hupperRaw : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B / sigma) y ≤
        ((B / sigma) / eta) * Real.exp (-eta * |y|))
    (hB : 0 < B) (hM : 0 ≤ M) (hR : 4 ≤ R)
    (hRratio : 32 * Erdos88.Esseen.relativeEsseenConstant /
      (orderedGaussianLowerConstant M * eta) ≤ R)
    (hcut : 2 / B ≤ nuCut)
    (hraw : (∫ t in -nuCut..nuCut,
      ‖finiteCharacteristic
            (productSliceQuadratic P ell (-trace F) f F) t -
        gaussianQuadraticCharacteristic (-trace F) f F t‖) ≤ E)
    (herror : Erdos88.Esseen.relativeEsseenConstant * (sigma * E) ≤
      orderedGaussianLowerConstant M / 32) :
    orderedGaussianLowerConstant M / 16 * (B / sigma) ≤
      Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F))
        (20000 * B) (sigma * (s * x)) := by
  let eps := B / sigma
  let law := (gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)
  let c := orderedGaussianLowerConstant M
  let C₀ := Erdos88.Esseen.relativeEsseenConstant
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hc : 0 < c := by
    dsimp only [c]
    exact orderedGaussianLowerConstant_pos hM
  have hC₀ : 0 ≤ C₀ := by
    dsimp only [C₀]
    exact Erdos88.Esseen.relativeEsseenConstant_nonneg
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  letI : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  letI : IsProbabilityMeasure law := by
    dsimp only [law]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hratioDensity : Erdos88.Esseen.DensityRatioOn p (s * x) eps R 2 := by
    apply densityRatioOn_two_of_holder_and_smallBall_lower
      law p hdens heps (by linarith) hc hL hholder
    · simpa only [law, eps, c] using hgaussianLower
    · simpa only [eps, c] using hosc
  have hratio : Erdos88.Esseen.SmallBallRatioOn law (s * x) eps R 2 :=
    Erdos88.Esseen.smallBallRatioOn_of_densityRatio
      law hdens heps (by linarith) hratioDensity
  have hupper : ∀ y : ℝ,
      Erdos88.Esseen.smallBall law eps y ≤ (1 / eta) * eps := by
    intro y
    have hbase := hupperRaw y
    have hexp : Real.exp (-eta * |y|) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heta.le) (abs_nonneg y))
    calc
      Erdos88.Esseen.smallBall law eps y ≤
          (eps / eta) * Real.exp (-eta * |y|) := by
        simpa only [law, eps] using hbase
      _ ≤ eps / eta :=
        mul_le_of_le_one_right (div_nonneg heps.le heta.le) hexp
      _ = (1 / eta) * eps := by ring
  have hconc : Erdos88.Esseen.concentration law eps ≤
      (1 / eta) * eps :=
    Erdos88.Esseen.concentration_le_of_smallBall_le law hupper
  have hcut' : 2 / (eps * sigma) ≤ nuCut := by
    convert hcut using 1
    dsimp only [eps]
    field_simp [hsigma.ne']
  let mu := Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
    (fun w ↦ productSliceQuadratic P ell (-trace F) f F w / sigma)
  have hfourier : Erdos88.Esseen.fourierError mu law eps ≤ sigma * E := by
    calc
      Erdos88.Esseen.fourierError mu law eps ≤
          sigma * (∫ t in -nuCut..nuCut,
            ‖finiteCharacteristic
                  (productSliceQuadratic P ell (-trace F) f F) t -
              gaussianQuadraticCharacteristic (-trace F) f F t‖) := by
        dsimp only [mu, law, eps]
        exact fourierError_productSlice_normalized_le_mul_raw
          P ell f F hsigma heps hcut'
      _ ≤ sigma * E := mul_le_mul_of_nonneg_left hraw hsigma.le
  have hcenter : sigma * (s * x) / sigma = s * x := by
    field_simp [hsigma.ne']
  have hratioRaw : Erdos88.Esseen.SmallBallRatioOn law
      (sigma * (s * x) / sigma) (B / sigma) R 2 := by
    rw [hcenter]
    simpa only [eps] using hratio
  have htransfer :=
    smallBall_productSlice_ge_of_normalized_gaussianSmallBallRatio
      P ell f hsigma hB (by norm_num : (1 : ℝ) ≤ 2) hR
        (sigma * (s * x)) hratioRaw (by
          simpa only [mu, law, eps] using hfourier)
  have hcross : 32 * C₀ ≤ R * (c * eta) := by
    exact (div_le_iff₀ (mul_pos hc heta)).1 (by
      simpa only [C₀, c] using hRratio)
  have hcoef : C₀ * (1 / eta) / R ≤ c / 32 := by
    have hbefore : C₀ / eta ≤ c * R / 32 := by
      apply (div_le_iff₀ heta).2
      nlinarith
    calc
      C₀ * (1 / eta) / R = (C₀ / eta) / R := by ring
      _ ≤ (c * R / 32) / R :=
        div_le_div_of_nonneg_right hbefore hRpos.le
      _ = c / 32 := by field_simp [hRpos.ne']
  have hnoise : Erdos88.Esseen.concentration law eps / R +
        eps * (sigma * E) ≤
      ((1 / eta) * eps) / R + eps * (sigma * E) :=
    add_le_add ((div_le_div_iff_of_pos_right hRpos).2 hconc) le_rfl
  have hnear : C₀ * (((1 / eta) * eps) / R) ≤ c * eps / 32 := by
    calc
      C₀ * (((1 / eta) * eps) / R) =
          (C₀ * (1 / eta) / R) * eps := by ring
      _ ≤ (c / 32) * eps :=
        mul_le_mul_of_nonneg_right hcoef heps.le
      _ = c * eps / 32 := by ring
  have hfar : C₀ * (eps * (sigma * E)) ≤ c * eps / 32 := by
    calc
      C₀ * (eps * (sigma * E)) = (C₀ * (sigma * E)) * eps := by ring
      _ ≤ (c / 32) * eps := by
        apply mul_le_mul_of_nonneg_right _ heps.le
        simpa only [C₀, c] using herror
      _ = c * eps / 32 := by ring
  have hloss : C₀ *
      (Erdos88.Esseen.concentration law eps / R + eps * (sigma * E)) ≤
        c * eps / 16 := by
    calc
      C₀ * (Erdos88.Esseen.concentration law eps / R +
          eps * (sigma * E)) ≤
          C₀ * (((1 / eta) * eps) / R + eps * (sigma * E)) :=
        mul_le_mul_of_nonneg_left hnoise hC₀
      _ = C₀ * (((1 / eta) * eps) / R) +
          C₀ * (eps * (sigma * E)) := by ring
      _ ≤ c * eps / 32 + c * eps / 32 := add_le_add hnear hfar
      _ = c * eps / 16 := by ring
  have hlower : c * eps ≤
      Erdos88.Esseen.smallBall law eps (s * x) := by
    simpa only [law, eps, c] using hgaussianLower
  have hmain : c / 16 * eps ≤
      (1 / 8 : ℝ) * Erdos88.Esseen.smallBall law eps (s * x) -
        C₀ * (Erdos88.Esseen.concentration law eps / R +
          eps * (sigma * E)) := by
    nlinarith
  apply hmain.trans
  have hwindow : (10000 : ℝ) * 2 * B = 20000 * B := by ring
  rw [hwindow] at htransfer
  simpa only [law, eps, c, C₀, hcenter] using htransfer

/-- One sign, selected from `F` before any product slice or linear part is
specified, works for every positive fixed-slice lower transfer. -/
theorem exists_sign_productSlice_lower_positive_uniform
    {n : ℕ} [NeZero n]
    {F : Matrix (Fin n) (Fin n) ℝ} (hF : F.IsHermitian) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ {m : ℕ} (P : BucketPartition (Fin n) (Fin m))
        (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
        (f : Fin n → ℝ) {sigma B M x nuCut E eta : ℝ},
        0 < sigma →
        sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f →
        0 < eta →
        (∀ y : ℝ,
          Erdos88.Esseen.smallBall
              ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
              (B / sigma) y ≤
            ((B / sigma) / eta) * Real.exp (-eta * |y|)) →
        0 < B → B ≤ sigma →
        0 ≤ M → 0 ≤ x → x ≤ M →
        2 / B ≤ nuCut →
        (∫ t in -nuCut..nuCut,
          ‖finiteCharacteristic
                (productSliceQuadratic P ell (-trace F) f F) t -
            gaussianQuadraticCharacteristic (-trace F) f F t‖) ≤ E →
        Erdos88.Esseen.relativeEsseenConstant * (sigma * E) ≤
          orderedGaussianLowerConstant M / 32 →
        let c := orderedGaussianLowerConstant M
        let K := 1 + (1 / eta) / c
        c / 16 * (B / sigma) ≤
          Erdos88.Esseen.smallBall
            (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
              (productSliceQuadratic P ell (-trace F) f F))
            ((10000 * K) * B) (sigma * (s * x)) := by
  obtain ⟨s, hs, hlower⟩ :=
    exists_sign_gaussianQuadraticCenteredLaw_smallBall_lower_uniform hF
  refine ⟨s, hs, ?_⟩
  intro m P ell _inst f sigma B M x nuCut E eta
    hsigma hsigmaSq heta hupper hB hBsigma hM hx hxM hcut hraw herror
  have heps : 0 ≤ B / sigma := (div_pos hB hsigma).le
  have hepsOne : B / sigma ≤ 1 := (div_le_one hsigma).2 hBsigma
  have hgaussian :=
    hlower f hsigma hsigmaSq hM hx hxM heps hepsOne
  exact productSlice_lower_positive_of_gaussianUpper_at_sign
    P ell f hsigma hgaussian heta hupper hB hBsigma hM hcut hraw herror

/-- Lower counterpart of the exact conditioning bridge in
`StructuredClaims`: a centered product-slice small-ball lower bound is the
same ambient graph-window lower bound after restoring its deterministic
conditional shift. -/
theorem conditionedProductSlice_window_lower_of_claim121_at
    {n k : ℕ} {d : Fin n → ℝ} {rho : ℝ}
    (D : RLCD.BucketDecomposition d k rho)
    (G : SimpleGraph (Fin n)) (e0 : ℝ) (cvec : Fin n → ℝ)
    {O : Finset (Fin n)} (hO : O ⊆ D.remainder)
    (hbucket : RobustRank.HasEqualBuckets D.finCoveredPartition.bucket)
    (ell : Fin (Fintype.card D.BlockIndex) → ℕ)
    [Nonempty (ProductSlicePoint D.finCoveredPartition ell)]
    {B K x : ℝ}
    (hlower :
      let Gc := D.finCoveredGraph G
      let cc := D.conditionedCoveredCoefficient G cvec O
      let E := GraphQuadratic.graphSliceConstant Gc
        (Probability.perturbedEdgePolynomial G e0 cvec O) cc
      let y := GraphQuadratic.graphEffectiveLinear Gc cc
      let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
        hbucket.choose Gc
      let f := Structured.wStar
        (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
        (RobustRank.graphAdjacencyMatrix Gc) y
        (productSliceDelta D.finCoveredPartition hbucket.choose ell)
      let shift := Structured.conditionalShift E
        (RobustRank.graphAdjacencyMatrix Gc) y
        (productSliceDelta D.finCoveredPartition hbucket.choose ell) + trace F
      K ≤ Esseen.smallBall
          (Esseen.finiteUniformLaw
            (ProductSlicePoint D.finCoveredPartition ell)
            (productSliceQuadratic D.finCoveredPartition ell
              (-trace F) f F)) B (x - shift)) :
    K ≤ Concentration.uniformProbability
      (fun S : ProductSlicePoint D.finCoveredPartition ell ↦
        |Probability.perturbedEdgePolynomial G e0 cvec
            (O ∪ D.finCoveredSubsetImage S.1) - x| ≤ B) := by
  classical
  let Gc := D.finCoveredGraph G
  let cc := D.conditionedCoveredCoefficient G cvec O
  let E := GraphQuadratic.graphSliceConstant Gc
    (Probability.perturbedEdgePolynomial G e0 cvec O) cc
  let y := GraphQuadratic.graphEffectiveLinear Gc cc
  let F := bucketCenteredAdjacency D.finCoveredPartition.bucket
    hbucket.choose Gc
  let f := Structured.wStar
    (bucketProjectionMatrix D.finCoveredPartition.bucket hbucket.choose)
    (RobustRank.graphAdjacencyMatrix Gc) y
    (productSliceDelta D.finCoveredPartition hbucket.choose ell)
  let shift := Structured.conditionalShift E
    (RobustRank.graphAdjacencyMatrix Gc) y
    (productSliceDelta D.finCoveredPartition hbucket.choose ell) + trace F
  have hpoly (S : ProductSlicePoint D.finCoveredPartition ell) :
      Probability.perturbedEdgePolynomial G e0 cvec
          (O ∪ D.finCoveredSubsetImage S.1) =
        shift + productSliceQuadratic D.finCoveredPartition ell
          (-trace F) f F S := by
    have hconditioned :=
      (D.sliceQuadratic_conditionedCovered_eq G e0 cvec hO S.1).symm
    have hslice :=
      sliceQuadratic_graph_eq_shift_add_productSlice_counts
        D.finCoveredPartition hbucket ell Gc
          (Probability.perturbedEdgePolynomial G e0 cvec O) cc S
    exact hconditioned.trans (by
      simpa only [Gc, cc, E, y, F, f, shift, add_assoc] using hslice)
  have hevent :
      (fun S : ProductSlicePoint D.finCoveredPartition ell ↦
        |Probability.perturbedEdgePolynomial G e0 cvec
            (O ∪ D.finCoveredSubsetImage S.1) - x| ≤ B) =
      (fun S ↦
        |productSliceQuadratic D.finCoveredPartition ell
            (-trace F) f F S - (x - shift)| ≤ B) := by
    funext S
    rw [hpoly S]
    congr 2 <;> ring
  rw [hevent]
  change K ≤ Fourier.finProbability
      (ProductSlicePoint D.finCoveredPartition ell)
        (fun S ↦
          |productSliceQuadratic D.finCoveredPartition ell
              (-trace F) f F S - (x - shift)| ≤ B)
  rw [← Esseen.smallBall_finiteUniformLaw]
  simpa only [Gc, cc, E, y, F, f, shift] using hlower

/-- The raw `n⁻⁶ᐟ⁵` Fourier error is negligible after multiplying by the
largest admissible Claim 12.1 standard deviation. -/
lemma eventually_claim121_lower_fourier_absorption
    {delta M : ℝ} (hdeltaSmall : delta < 3 / 400) (hM : 0 ≤ M) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * Erdos88.Esseen.relativeEsseenConstant *
          scale n (-1 / 5 + 3 * delta) ≤
        orderedGaussianLowerConstant M / 32 := by
  let c := orderedGaussianLowerConstant M
  let A := 64 * Erdos88.Esseen.relativeEsseenConstant / c
  have hc : 0 < c := by
    dsimp only [c]
    exact orderedGaussianLowerConstant_pos hM
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact div_nonneg
      (mul_nonneg (by norm_num)
        Erdos88.Esseen.relativeEsseenConstant_nonneg) hc.le
  have hexp : (-1 / 5 : ℝ) + 3 * delta < 0 := by
    linarith
  have hrate :=
    Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
      A (-1 / 5 + 3 * delta) 0 hA hexp
  filter_upwards [hrate] with n hn
  have hn' : A * scale n (-1 / 5 + 3 * delta) ≤ 1 := by
    simpa only [scale, Real.rpow_eq_pow, Real.rpow_zero] using hn
  calc
    2 * Erdos88.Esseen.relativeEsseenConstant *
          scale n (-1 / 5 + 3 * delta) =
        (c / 32) * (A * scale n (-1 / 5 + 3 * delta)) := by
      dsimp only [A]
      field_simp [hc.ne']
      ring
    _ ≤ (c / 32) * 1 :=
      mul_le_mul_of_nonneg_left hn' (div_nonneg hc.le (by norm_num))
    _ = orderedGaussianLowerConstant M / 32 := by
      simp only [mul_one, c]

/-- Eventual fixed-slice lower half of Claim 12.1 with the source quantifier
order: after the centered matrix is fixed, one sign works for every
near-balanced count vector, every admissible linear part, and every center
in the corresponding one-sided `M * sigma` window. -/
theorem exists_eventual_productSlice_claim121_lower_uniform
    (C delta M : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) (hM : 0 ≤ M) :
    ∃ B : ℝ, 0 < B ∧ ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {K : ℕ}
          (P : BucketPartition (Fin n) (Fin (K + 1)))
          (G : SimpleGraph (Fin n))
          (hbucket : RobustRank.HasEqualBuckets P.bucket),
          IsKSSSPartition delta P → RamseyFree C G →
          ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
            ∀ (ell : Fin (K + 1) → ℕ) (f : Fin n → ℝ),
              IsNearBalanced delta P ell →
              HasKSSSBalancedCoefficients delta P f
                (bucketCenteredAdjacency P.bucket hbucket.choose G) →
              ∃ hleft : Nonempty (ProductSlicePoint P ell),
                letI := hleft
                let F := bucketCenteredAdjacency P.bucket hbucket.choose G
                let sigma := Real.sqrt
                  (2 * frobeniusSq F + vectorSqNorm f)
                0 < sigma ∧ ∀ z : ℝ,
                  0 ≤ s * z → s * z ≤ M * sigma →
                  kappa / sigma ≤
                    Esseen.smallBall
                      (Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                        (productSliceQuadratic P ell (-trace F) f F)) B z := by
  obtain ⟨nu, hnu, _cFourier, _hcFourier, hfourier⟩ :=
    exists_eventual_productSlice_fourierL1_le
      C delta hC hdelta hdeltaSmall
  obtain ⟨rho, hrho, Nrob, hrob⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
      C delta 400 hC hdelta (by linarith)
  obtain ⟨eta, heta, _hetaOne, hgaussian⟩ :=
    ksssGaussianNonuniformUpper rho hrho
  let B0 : ℝ := 2 / nu
  let cLower : ℝ := orderedGaussianLowerConstant M
  let Klower : ℝ := 1 + (1 / eta) / cLower
  let B : ℝ := (10000 * Klower) * B0
  let kappa : ℝ := cLower * B0 / 16
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hcLower : 0 < cLower := by
    dsimp only [cLower]
    exact orderedGaussianLowerConstant_pos hM
  have hKlower : 0 < Klower := by
    dsimp only [Klower]
    positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  have hBsmall : ∀ᶠ n : ℕ in Filter.atTop,
      B0 ≤ Real.sqrt rho * (n : ℝ) := by
    have hrate :=
      Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
        (B0 / Real.sqrt rho) 0 1 (by positivity) (by norm_num)
    filter_upwards [hrate] with n hn
    have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
    have hn' : B0 / Real.sqrt rho ≤ (n : ℝ) := by
      simpa only [Real.rpow_zero, Real.rpow_one, mul_one] using hn
    calc
      B0 = Real.sqrt rho * (B0 / Real.sqrt rho) := by
        field_simp [hsqrt.ne']
      _ ≤ Real.sqrt rho * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hn' hsqrt.le
  have herrorRate :=
    eventually_claim121_lower_fourier_absorption hdeltaSmall hM
  refine ⟨B, hB, kappa, hkappa, ?_⟩
  filter_upwards [hfourier, hBsmall, herrorRate,
    Filter.eventually_ge_atTop (max Nrob 1)] with
      n hfourierN hBsmallN herrorRateN hn
  intro K P G hbucket hpart hRamsey
  have hnOne : 1 ≤ n := (le_max_right Nrob 1).trans hn
  have hnpos : 0 < n := by omega
  letI : NeZero n := ⟨by omega⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNrob : Nrob ≤ n := (le_max_left Nrob 1).trans hn
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  have hF : F.IsHermitian :=
    bucketCenteredAdjacency_isHermitian P.bucket hbucket.choose G
  have hrobF : RobustRankAt 400 (rho * (n : ℝ) ^ 2) F := by
    exact hrob n hNrob (K + 1) P.bucket G (by omega)
      hpart.2.1 hpart.2.2 hbucket hRamsey
  obtain ⟨s, hs, hlowerUniform⟩ :=
    exists_sign_productSlice_lower_positive_uniform hF
  refine ⟨s, hs, ?_⟩
  intro ell f hbalanced hcoeff
  let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
  obtain ⟨hleft, hraw⟩ :=
    hfourierN P ell G f hbucket hpart hbalanced hcoeff hRamsey
  letI := hleft
  have hFbound : frobeniusSq F ≤ (n : ℝ) ^ 2 := by
    have hrawBound := frobeniusSq_le F 1 (by norm_num) hcoeff.2.2.1
    simpa only [one_pow, mul_one] using hrawBound
  have hrobCost : rho * frobeniusSq F ≤ rho * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hFbound hrho.le
  have hrobThree : RobustRankAt 3 (rho * frobeniusSq F) F :=
    robustRankAt_mono_cost hrobCost
      (robustRankAt_anti_rank (by norm_num : 3 ≤ 400) hrobF)
  have hFrobLower : rho * (n : ℝ) ^ 2 ≤ frobeniusSq F := by
    have hzero := hrobF 0 (by simp)
    simpa only [sub_zero, frobenius_norm_sq_eq_frobeniusSq] using hzero
  have hFrobPos : 0 < frobeniusSq F := by
    exact (mul_pos hrho (sq_pos_of_pos hnR)).trans_le hFrobLower
  have hvecNonneg : 0 ≤ vectorSqNorm f := by
    unfold vectorSqNorm
    positivity
  have htargetNonneg : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f := by
    positivity
  have hsigmaSq : sigma ^ 2 =
      2 * frobeniusSq F + vectorSqNorm f := by
    dsimp only [sigma]
    exact Real.sq_sqrt htargetNonneg
  have hsigmaLower : Real.sqrt rho * (n : ℝ) ≤ sigma := by
    apply Erdos88.Structured.sigma_lower_bound (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) hnR.le
    rw [hsigmaSq, mul_pow, Real.sq_sqrt hrho.le]
    nlinarith [hFrobLower, hvecNonneg]
  have hsigma : 0 < sigma :=
    lt_of_lt_of_le (mul_pos (Real.sqrt_pos.2 hrho) hnR) hsigmaLower
  have hBsigma : B0 ≤ sigma := hBsmallN.trans hsigmaLower
  have htargetUpper :
      2 * frobeniusSq F + vectorSqNorm f ≤
        3 * scale n (2 + 6 * delta) :=
    gaussianVarianceTarget_le_ksss delta hdelta.le hnOne f F
      hcoeff.2.1 hcoeff.2.2.1
  have hscaleSq : scale n (1 + 3 * delta) ^ 2 =
      scale n (2 + 6 * delta) := by
    rw [scale_sq (Nat.zero_le n)]
    congr 1
    ring
  have hsigmaUpper : sigma ≤ 2 * scale n (1 + 3 * delta) := by
    apply Erdos88.Structured.sigma_upper_bound (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (scale_nonneg n _))
    rw [hsigmaSq]
    calc
      2 * frobeniusSq F + vectorSqNorm f ≤
          3 * scale n (2 + 6 * delta) := htargetUpper
      _ = 3 * scale n (1 + 3 * delta) ^ 2 := by rw [hscaleSq]
      _ ≤ (2 * scale n (1 + 3 * delta)) ^ 2 := by
        nlinarith [sq_nonneg (scale n (1 + 3 * delta))]
  have hcut : 2 / B0 ≤ nu := by
    dsimp only [B0]
    field_simp [hnu.ne'] <;> norm_num
  have heps : 0 < B0 / sigma := div_pos hB0 hsigma
  have hepsOne : B0 / sigma ≤ 1 := (div_le_one hsigma).2 hBsigma
  have hgauss : ∀ y : ℝ,
      Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B0 / sigma) y ≤
        ((B0 / sigma) / eta) * Real.exp (-eta * |y|) :=
    hgaussian f hF hsigma hsigmaSq hFrobPos hrobThree heps hepsOne
  have herror : Esseen.relativeEsseenConstant *
      (sigma * scale n (-6 / 5 : ℝ)) ≤
        orderedGaussianLowerConstant M / 32 := by
    calc
      Esseen.relativeEsseenConstant *
          (sigma * scale n (-6 / 5 : ℝ)) ≤
        Esseen.relativeEsseenConstant *
          ((2 * scale n (1 + 3 * delta)) * scale n (-6 / 5 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _
          Esseen.relativeEsseenConstant_nonneg
        exact mul_le_mul_of_nonneg_right hsigmaUpper (scale_nonneg n _)
      _ = 2 * Esseen.relativeEsseenConstant *
          (scale n (1 + 3 * delta) * scale n (-6 / 5 : ℝ)) := by ring
      _ = 2 * Esseen.relativeEsseenConstant *
          scale n ((1 + 3 * delta) + (-6 / 5 : ℝ)) := by
        rw [scale_mul hnpos]
      _ = 2 * Esseen.relativeEsseenConstant *
          scale n (-1 / 5 + 3 * delta) := by
        congr 2
        ring
      _ ≤ orderedGaussianLowerConstant M / 32 := herrorRateN
  refine ⟨hleft, hsigma, ?_⟩
  intro z hz0 hzM
  let x : ℝ := s * z / sigma
  have hsSq : s ^ 2 = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact div_nonneg hz0 hsigma.le
  have hxM : x ≤ M := by
    dsimp only [x]
    exact (div_le_iff₀ hsigma).2 hzM
  have hpoint := hlowerUniform P ell f hsigma hsigmaSq heta hgauss
    hB0 hBsigma hM hx hxM hcut hraw herror
  have hcenter : sigma * (s * x) = z := by
    dsimp only [x]
    rw [show s * (s * z / sigma) = (s ^ 2 * z) / sigma by ring,
      hsSq, one_mul]
    field_simp [hsigma.ne']
  calc
    kappa / sigma =
        orderedGaussianLowerConstant M / 16 * (B0 / sigma) := by
      dsimp only [kappa, cLower]
      ring
    _ ≤ Esseen.smallBall
        (Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F))
        ((10000 * (1 + (1 / eta) /
          orderedGaussianLowerConstant M)) * B0) (sigma * (s * x)) := by
      simpa only using hpoint
    _ = Esseen.smallBall
        (Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F)) B z := by
      rw [hcenter]

/-- Source-quantified lower half of Claim 12.1.  In contrast with the older
ratio-by-global-upper-bound wrapper above, the physical window is selected
before the compact center range `M`.  Relative robust rank gives a uniform
Hölder modulus for the normalized Gaussian density; because `sigma` grows
linearly in `n`, its oscillation on the comparison window eventually becomes
small enough to use the absolute density-ratio constant `2`. -/
theorem exists_fixedWindow_eventual_productSlice_claim121_lower_uniform
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ B : ℝ, 0 < B ∧ ∀ M : ℝ, 0 ≤ M →
      ∃ kappa : ℝ, 0 < kappa ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {K : ℕ}
          (P : BucketPartition (Fin n) (Fin (K + 1)))
          (G : SimpleGraph (Fin n))
          (hbucket : RobustRank.HasEqualBuckets P.bucket),
          IsKSSSPartition delta P → RamseyFree C G →
          ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
            ∀ (ell : Fin (K + 1) → ℕ) (f : Fin n → ℝ),
              IsNearBalanced delta P ell →
              HasKSSSBalancedCoefficients delta P f
                (bucketCenteredAdjacency P.bucket hbucket.choose G) →
              ∃ hleft : Nonempty (ProductSlicePoint P ell),
                letI := hleft
                let F := bucketCenteredAdjacency P.bucket hbucket.choose G
                let sigma := Real.sqrt
                  (2 * frobeniusSq F + vectorSqNorm f)
                0 < sigma ∧ ∀ z : ℝ,
                  0 ≤ s * z → s * z ≤ M * sigma →
                  kappa / sigma ≤
                    Esseen.smallBall
                      (Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                        (productSliceQuadratic P ell (-trace F) f F)) B z := by
  obtain ⟨nu, hnu, _cFourier, _hcFourier, hfourier⟩ :=
    exists_eventual_productSlice_fourierL1_le
      C delta hC hdelta hdeltaSmall
  obtain ⟨rho, hrho, Nrob, hrob⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
      C delta 400 hC hdelta (by linarith)
  obtain ⟨eta, heta, _hetaOne, hgaussian⟩ :=
    ksssGaussianNonuniformUpper rho hrho
  let B0 : ℝ := 2 / nu
  let B : ℝ := 20000 * B0
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro M hM
  let cLower : ℝ := orderedGaussianLowerConstant M
  let R : ℝ := max 4
    (32 * Esseen.relativeEsseenConstant / (cLower * eta))
  let L : ℝ :=
    threeSpectralQuarterMass (min rho 1 / 192) / Real.pi
  let A : ℝ := (R + 1) * B0 / Real.sqrt rho
  let D : ℝ := 8 * L * A ^ (1 / 4 : ℝ) / cLower
  let kappa : ℝ := cLower * B0 / 16
  have hcLower : 0 < cLower := by
    dsimp only [cLower]
    exact orderedGaussianLowerConstant_pos hM
  have hR : 4 ≤ R := by dsimp only [R]; exact le_max_left _ _
  have hRratio : 32 * Esseen.relativeEsseenConstant /
      (cLower * eta) ≤ R := by
    dsimp only [R]
    exact le_max_right _ _
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact div_nonneg
      (threeSpectralQuarterMass_nonneg (by positivity)) Real.pi_pos.le
  have hA : 0 < A := by dsimp only [A]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hkappa : 0 < kappa := by dsimp only [kappa]; positivity
  have hBsmall : ∀ᶠ n : ℕ in Filter.atTop,
      B0 ≤ Real.sqrt rho * (n : ℝ) := by
    have hrate :=
      Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
        (B0 / Real.sqrt rho) 0 1 (by positivity) (by norm_num)
    filter_upwards [hrate] with n hn
    have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
    have hn' : B0 / Real.sqrt rho ≤ (n : ℝ) := by
      simpa only [Real.rpow_zero, Real.rpow_one, mul_one] using hn
    calc
      B0 = Real.sqrt rho * (B0 / Real.sqrt rho) := by
        field_simp [hsqrt.ne']
      _ ≤ Real.sqrt rho * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hn' hsqrt.le
  have hholderRate : ∀ᶠ n : ℕ in Filter.atTop,
      D * scale n (-1 / 4 : ℝ) ≤ 1 := by
    have hrate :=
      Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
        D (-1 / 4) 0 hD (by norm_num)
    filter_upwards [hrate] with n hn
    simpa only [scale, Real.rpow_eq_pow, Real.rpow_zero] using hn
  have herrorRate :=
    eventually_claim121_lower_fourier_absorption hdeltaSmall hM
  refine ⟨kappa, hkappa, ?_⟩
  filter_upwards [hfourier, hBsmall, hholderRate, herrorRate,
    Filter.eventually_ge_atTop (max Nrob 1)] with
      n hfourierN hBsmallN hholderRateN herrorRateN hn
  intro K P G hbucket hpart hRamsey
  have hnOne : 1 ≤ n := (le_max_right Nrob 1).trans hn
  have hnpos : 0 < n := by omega
  letI : NeZero n := ⟨by omega⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNrob : Nrob ≤ n := (le_max_left Nrob 1).trans hn
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  have hF : F.IsHermitian :=
    bucketCenteredAdjacency_isHermitian P.bucket hbucket.choose G
  have hrobF : RobustRankAt 400 (rho * (n : ℝ) ^ 2) F := by
    exact hrob n hNrob (K + 1) P.bucket G (by omega)
      hpart.2.1 hpart.2.2 hbucket hRamsey
  obtain ⟨s, hs, hlowerUniform⟩ :=
    exists_sign_gaussianQuadraticCenteredLaw_smallBall_lower_uniform hF
  refine ⟨s, hs, ?_⟩
  intro ell f hbalanced hcoeff
  let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
  obtain ⟨hleft, hraw⟩ :=
    hfourierN P ell G f hbucket hpart hbalanced hcoeff hRamsey
  letI := hleft
  have hFbound : frobeniusSq F ≤ (n : ℝ) ^ 2 := by
    have hrawBound := frobeniusSq_le F 1 (by norm_num) hcoeff.2.2.1
    simpa only [one_pow, mul_one] using hrawBound
  have hrobCost : rho * frobeniusSq F ≤ rho * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hFbound hrho.le
  have hrobThree : RobustRankAt 3 (rho * frobeniusSq F) F :=
    robustRankAt_mono_cost hrobCost
      (robustRankAt_anti_rank (by norm_num : 3 ≤ 400) hrobF)
  have hFrobLower : rho * (n : ℝ) ^ 2 ≤ frobeniusSq F := by
    have hzero := hrobF 0 (by simp)
    simpa only [sub_zero, frobenius_norm_sq_eq_frobeniusSq] using hzero
  have hFrobPos : 0 < frobeniusSq F := by
    exact (mul_pos hrho (sq_pos_of_pos hnR)).trans_le hFrobLower
  have hvecNonneg : 0 ≤ vectorSqNorm f := by
    unfold vectorSqNorm
    positivity
  have htargetNonneg : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f := by
    positivity
  have hsigmaSq : sigma ^ 2 =
      2 * frobeniusSq F + vectorSqNorm f := by
    dsimp only [sigma]
    exact Real.sq_sqrt htargetNonneg
  have hsigmaLower : Real.sqrt rho * (n : ℝ) ≤ sigma := by
    apply Erdos88.Structured.sigma_lower_bound (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) hnR.le
    rw [hsigmaSq, mul_pow, Real.sq_sqrt hrho.le]
    nlinarith [hFrobLower, hvecNonneg]
  have hsigma : 0 < sigma :=
    lt_of_lt_of_le (mul_pos (Real.sqrt_pos.2 hrho) hnR) hsigmaLower
  have hBsigma : B0 ≤ sigma := hBsmallN.trans hsigmaLower
  have htargetUpper :
      2 * frobeniusSq F + vectorSqNorm f ≤
        3 * scale n (2 + 6 * delta) :=
    gaussianVarianceTarget_le_ksss delta hdelta.le hnOne f F
      hcoeff.2.1 hcoeff.2.2.1
  have hscaleSq : scale n (1 + 3 * delta) ^ 2 =
      scale n (2 + 6 * delta) := by
    rw [scale_sq (Nat.zero_le n)]
    congr 1
    ring
  have hsigmaUpper : sigma ≤ 2 * scale n (1 + 3 * delta) := by
    apply Erdos88.Structured.sigma_upper_bound (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (scale_nonneg n _))
    rw [hsigmaSq]
    calc
      2 * frobeniusSq F + vectorSqNorm f ≤
          3 * scale n (2 + 6 * delta) := htargetUpper
      _ = 3 * scale n (1 + 3 * delta) ^ 2 := by rw [hscaleSq]
      _ ≤ (2 * scale n (1 + 3 * delta)) ^ 2 := by
        nlinarith [sq_nonneg (scale n (1 + 3 * delta))]
  have hcut : 2 / B0 ≤ nu := by
    dsimp only [B0]
    field_simp [hnu.ne'] <;> norm_num
  have heps : 0 < B0 / sigma := div_pos hB0 hsigma
  have hepsOne : B0 / sigma ≤ 1 := (div_le_one hsigma).2 hBsigma
  have hgauss : ∀ y : ℝ,
      Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B0 / sigma) y ≤
        ((B0 / sigma) / eta) * Real.exp (-eta * |y|) :=
    hgaussian f hF hsigma hsigmaSq hFrobPos hrobThree heps hepsOne
  obtain ⟨p, hdens, hholder⟩ :=
    exists_holderDensity_gaussianQuadratic_of_relative_robustRankThree
      hrho f hF hsigma hsigmaSq hrobThree
  have hosc : L * ((R + 1) * (B0 / sigma)) ^ (1 / 4 : ℝ) ≤
      cLower / 8 := by
    have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
    have hden : 0 < Real.sqrt rho * (n : ℝ) := mul_pos hsqrt hnR
    have hdiv : B0 / sigma ≤ B0 / (Real.sqrt rho * (n : ℝ)) :=
      div_le_div_of_nonneg_left hB0.le hden hsigmaLower
    have hRone : 0 ≤ R + 1 := by linarith
    have hbase : (R + 1) * (B0 / sigma) ≤ A / (n : ℝ) := by
      calc
        (R + 1) * (B0 / sigma) ≤
            (R + 1) * (B0 / (Real.sqrt rho * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hdiv hRone
        _ = A / (n : ℝ) := by
          dsimp only [A]
          field_simp [hsqrt.ne', hnR.ne']
    have hpow := Real.rpow_le_rpow (by positivity) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hpowA : (A / (n : ℝ)) ^ (1 / 4 : ℝ) =
        A ^ (1 / 4 : ℝ) * scale n (-1 / 4 : ℝ) := by
      rw [Real.div_rpow hA.le hnR.le, div_eq_mul_inv,
        ← Real.rpow_neg hnR.le]
      simp only [scale, Real.rpow_eq_pow]
      congr 1
      ring
    calc
      L * ((R + 1) * (B0 / sigma)) ^ (1 / 4 : ℝ) ≤
          L * (A / (n : ℝ)) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow hL
      _ = (cLower / 8) * (D * scale n (-1 / 4 : ℝ)) := by
        rw [hpowA]
        dsimp only [D]
        field_simp [hcLower.ne']
      _ ≤ (cLower / 8) * 1 :=
        mul_le_mul_of_nonneg_left hholderRateN
          (div_nonneg hcLower.le (by norm_num))
      _ = cLower / 8 := by ring
  have herror : Esseen.relativeEsseenConstant *
      (sigma * scale n (-6 / 5 : ℝ)) ≤
        orderedGaussianLowerConstant M / 32 := by
    calc
      Esseen.relativeEsseenConstant *
          (sigma * scale n (-6 / 5 : ℝ)) ≤
        Esseen.relativeEsseenConstant *
          ((2 * scale n (1 + 3 * delta)) * scale n (-6 / 5 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _
          Esseen.relativeEsseenConstant_nonneg
        exact mul_le_mul_of_nonneg_right hsigmaUpper (scale_nonneg n _)
      _ = 2 * Esseen.relativeEsseenConstant *
          (scale n (1 + 3 * delta) * scale n (-6 / 5 : ℝ)) := by ring
      _ = 2 * Esseen.relativeEsseenConstant *
          scale n ((1 + 3 * delta) + (-6 / 5 : ℝ)) := by
        rw [scale_mul hnpos]
      _ = 2 * Esseen.relativeEsseenConstant *
          scale n (-1 / 5 + 3 * delta) := by
        congr 2
        ring
      _ ≤ orderedGaussianLowerConstant M / 32 := herrorRateN
  refine ⟨hleft, hsigma, ?_⟩
  intro z hz0 hzM
  let x : ℝ := s * z / sigma
  have hsSq : s ^ 2 = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact div_nonneg hz0 hsigma.le
  have hxM : x ≤ M := by
    dsimp only [x]
    exact (div_le_iff₀ hsigma).2 hzM
  have hgaussianLower :=
    hlowerUniform f hsigma hsigmaSq hM hx hxM heps.le hepsOne
  have hpoint := productSlice_lower_positive_of_gaussianHolder_at_sign
    P ell f hsigma hgaussianLower hdens hL hholder hosc heta hgauss
      hB0 hM hR hRratio hcut hraw herror
  have hcenter : sigma * (s * x) = z := by
    dsimp only [x]
    rw [show s * (s * z / sigma) = (s ^ 2 * z) / sigma by ring,
      hsSq, one_mul]
    field_simp [hsigma.ne']
  calc
    kappa / sigma =
        orderedGaussianLowerConstant M / 16 * (B0 / sigma) := by
      dsimp only [kappa, cLower]
      ring
    _ ≤ Esseen.smallBall
        (Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F))
        (20000 * B0) (sigma * (s * x)) := by
      simpa only [cLower, L] using hpoint
    _ = Esseen.smallBall
        (Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F)) B z := by
      rw [hcenter]

end Erdos88.GaussianQuadratic
