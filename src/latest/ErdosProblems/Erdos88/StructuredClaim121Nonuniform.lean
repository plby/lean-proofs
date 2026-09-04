import ErdosProblems.Erdos88.ProductSliceFourierAssembly

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace Erdos88.GaussianQuadratic

open BooleanSlices

/-- The normalized upper half of KSSS Theorem 5.2.  Writing the statement
for the variance-one pushforward makes the scale invariance explicit and is
the exact form consumed by Claim 12.1. -/
def KSSSGaussianNonuniformUpper : Prop :=
  ∀ rho : ℝ, 0 < rho →
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ {n : ℕ} (f : Fin n → ℝ)
        {F : Matrix (Fin n) (Fin n) ℝ}, F.IsHermitian →
        ∀ {sigma : ℝ}, 0 < sigma →
          sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f →
          0 < frobeniusSq F →
          RobustRankAt 3 (rho * frobeniusSq F) F →
          ∀ {eps : ℝ}, 0 < eps → eps ≤ 1 → ∀ x : ℝ,
            Erdos88.Esseen.smallBall
                ((gaussianQuadraticCenteredLaw f F).map
                  (fun z ↦ z / sigma)) eps x ≤
              (eps / eta) * Real.exp (-eta * |x|)

/-- The exact Lemma 6.2 transfer used in the upper half of Claim 12.1.
The product-slice and Gaussian quadratic laws are both normalized by their
common standard deviation.  The conclusion is then rewritten back in the
original scale. -/
theorem smallBall_productSlice_le_of_normalized_gaussianNonuniform
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    {sigma B eta E : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hBsigma : B ≤ sigma)
    (heta : 0 < eta) (hetaOne : eta < 1)
    (hgauss : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B / sigma) y ≤
        ((B / sigma) / eta) * Real.exp (-eta * |y|))
    (hfourier : Erdos88.Esseen.fourierError
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (fun w ↦ productSliceQuadratic P ell (-trace F) f F w / sigma))
        ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
        (B / sigma) ≤ E)
    (x : ℝ) :
    Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F)) B x ≤
      Erdos88.Esseen.relativeEsseenConstant *
        (B ^ 2 / (x ^ 2 + sigma ^ 2) +
          (B / (eta * sigma)) *
            Real.exp (-eta * |x| / (2 * sigma)) +
          (B / sigma) * E) := by
  let X := productSliceQuadratic P ell (-trace F) f F
  let mu := Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
    (fun w ↦ X w / sigma)
  let nu := (gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)
  let : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  let : IsProbabilityMeasure nu := by
    dsimp only [nu]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have heps : 0 < B / sigma := div_pos hB hsigma
  have hepsOne : B / sigma ≤ 1 :=
    (div_le_one hsigma).2 hBsigma
  have hgauss' : ∀ y : ℝ,
      Erdos88.Esseen.smallBall nu (B / sigma) y ≤
        ((B / sigma) / (eta * 1)) *
          Real.exp (-eta * |y| / 1) := by
    intro y
    simpa only [nu, mul_one, div_one] using hgauss y
  have hrelative := Erdos88.Esseen.relative_esseen_6_2
    mu nu heps heta hetaOne (by norm_num : (0 : ℝ) < 1)
      hepsOne hgauss' (x / sigma)
  have hfourier0 : 0 ≤ Erdos88.Esseen.fourierError mu nu (B / sigma) :=
    Erdos88.Esseen.fourierError_nonneg mu nu heps
  have hnormalized :
      Erdos88.Esseen.smallBall mu (B / sigma) (x / sigma) ≤
        Erdos88.Esseen.relativeEsseenConstant *
          ((B / sigma) ^ 2 / ((x / sigma) ^ 2 + 1 ^ 2) +
            ((B / sigma) / (eta * 1)) *
              Real.exp (-eta * |x / sigma| / (2 * 1)) +
            (B / sigma) * E) := by
    apply hrelative.trans
    apply mul_le_mul_of_nonneg_left _
      Erdos88.Esseen.relativeEsseenConstant_nonneg
    exact add_le_add_right
      (mul_le_mul_of_nonneg_left hfourier heps.le) _
  rw [← smallBall_finiteUniformLaw_div X hsigma]
  change Erdos88.Esseen.smallBall mu (B / sigma) (x / sigma) ≤ _
  calc
    Erdos88.Esseen.smallBall mu (B / sigma) (x / sigma) ≤
        Erdos88.Esseen.relativeEsseenConstant *
          ((B / sigma) ^ 2 / ((x / sigma) ^ 2 + 1 ^ 2) +
            ((B / sigma) / (eta * 1)) *
              Real.exp (-eta * |x / sigma| / (2 * 1)) +
            (B / sigma) * E) := hnormalized
    _ = Erdos88.Esseen.relativeEsseenConstant *
        (B ^ 2 / (x ^ 2 + sigma ^ 2) +
          (B / (eta * sigma)) *
            Real.exp (-eta * |x| / (2 * sigma)) +
          (B / sigma) * E) := by
      rw [abs_div, abs_of_pos hsigma]
      congr 1
      field_simp [hsigma.ne', heta.ne']
      <;> ring

/-- Raw Fourier-window form of the preceding transfer.  This is the form
fed by KSSS Lemma 11.1: a raw `L¹` comparison of size `E` becomes a
normalized Fourier error of size `sigma * E`, and hence contributes the
scale-free term `B * E` after Lemma 6.2. -/
theorem smallBall_productSlice_le_of_raw_fourier_and_gaussianNonuniform
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    {sigma B eta nu E : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hBsigma : B ≤ sigma)
    (heta : 0 < eta) (hetaOne : eta < 1) (hcut : 2 / B ≤ nu)
    (hgauss : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B / sigma) y ≤
        ((B / sigma) / eta) * Real.exp (-eta * |y|))
    (hraw : (∫ t in -nu..nu,
      ‖finiteCharacteristic
            (productSliceQuadratic P ell (-trace F) f F) t -
        gaussianQuadraticCharacteristic (-trace F) f F t‖) ≤ E)
    (x : ℝ) :
    Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F)) B x ≤
      Erdos88.Esseen.relativeEsseenConstant *
        (B ^ 2 / (x ^ 2 + sigma ^ 2) +
          (B / (eta * sigma)) *
            Real.exp (-eta * |x| / (2 * sigma)) + B * E) := by
  let X := productSliceQuadratic P ell (-trace F) f F
  let mu := Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
    (fun w ↦ X w / sigma)
  let nuLaw := (gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)
  have heps : 0 < B / sigma := div_pos hB hsigma
  have hcut' : 2 / ((B / sigma) * sigma) ≤ nu := by
    convert hcut using 1
    field_simp [hsigma.ne']
  have hfourier : Erdos88.Esseen.fourierError mu nuLaw (B / sigma) ≤
      sigma * E := by
    calc
      Erdos88.Esseen.fourierError mu nuLaw (B / sigma) ≤
          sigma * (∫ t in -nu..nu,
            ‖finiteCharacteristic X t -
              gaussianQuadraticCharacteristic (-trace F) f F t‖) := by
        dsimp only [mu, nuLaw, X]
        exact fourierError_productSlice_normalized_le_mul_raw
          P ell f F hsigma heps hcut'
      _ ≤ sigma * E := mul_le_mul_of_nonneg_left hraw hsigma.le
  have htransfer :=
    smallBall_productSlice_le_of_normalized_gaussianNonuniform
      P ell f hsigma hB hBsigma heta hetaOne hgauss hfourier x
  calc
    Erdos88.Esseen.smallBall
          (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
            (productSliceQuadratic P ell (-trace F) f F)) B x ≤
        Erdos88.Esseen.relativeEsseenConstant *
          (B ^ 2 / (x ^ 2 + sigma ^ 2) +
            (B / (eta * sigma)) *
              Real.exp (-eta * |x| / (2 * sigma)) +
            (B / sigma) * (sigma * E)) := htransfer
    _ = Erdos88.Esseen.relativeEsseenConstant *
        (B ^ 2 / (x ^ 2 + sigma ^ 2) +
          (B / (eta * sigma)) *
            Real.exp (-eta * |x| / (2 * sigma)) + B * E) := by
      field_simp [hsigma.ne']

/-- Claim 12.1's nonuniform product-slice upper bound, conditional only on
the genuinely Gaussian content of Theorem 5.2.  All graph, robust-rank,
Fourier-comparison, and normalization hypotheses are discharged here. -/
theorem exists_eventual_productSlice_claim121_nonuniform_upper_threshold
    (h52 : KSSSGaussianNonuniformUpper)
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ B : ℝ, B0 ≤ B →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {K : ℕ}
          (P : BucketPartition (Fin n) (Fin (K + 1)))
          (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
          (f : Fin n → ℝ)
          (hbucket : Erdos88.RobustRank.HasEqualBuckets P.bucket),
          IsKSSSPartition delta P → IsNearBalanced delta P ell →
          HasKSSSBalancedCoefficients delta P f
            (bucketCenteredAdjacency P.bucket hbucket.choose G) →
          RamseyFree C G →
          ∃ hleft : Nonempty (ProductSlicePoint P ell),
            letI := hleft
            let F := bucketCenteredAdjacency P.bucket hbucket.choose G
            let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
            0 < sigma ∧ ∀ x : ℝ,
              Erdos88.Esseen.smallBall
                  (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                    (productSliceQuadratic P ell (-trace F) f F)) B x ≤
                Erdos88.Esseen.relativeEsseenConstant *
                  (B ^ 2 / (x ^ 2 + sigma ^ 2) +
                    (B / (eta * sigma)) *
                      Real.exp (-eta * |x| / (2 * sigma)) +
                    B * scale n (-6 / 5 : ℝ)) := by
  obtain ⟨nu, hnu, _cFourier, _hcFourier, hfourier⟩ :=
    exists_eventual_productSlice_fourierL1_le
      C delta hC hdelta hdeltaSmall
  obtain ⟨rho, hrho, Nrob, hrob⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
      C delta 400 hC hdelta (by linarith)
  obtain ⟨eta, heta, hetaOne, hgaussian⟩ := h52 rho hrho
  let B0 : ℝ := 2 / nu
  have hB0 : 0 < B0 := by dsimp only [B0]; positivity
  refine ⟨B0, hB0, eta, heta, hetaOne, ?_⟩
  intro B hB0B
  have hB : 0 < B := hB0.trans_le hB0B
  have hBsmall : ∀ᶠ n : ℕ in Filter.atTop,
      B ≤ Real.sqrt rho * (n : ℝ) := by
    have hrate :=
      Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
        (B / Real.sqrt rho) 0 1 (by positivity) (by norm_num)
    filter_upwards [hrate] with n hn
    have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
    have hpow0 : (n : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero _
    have hpow1 : (n : ℝ) ^ (1 : ℝ) = n := Real.rpow_one _
    rw [hpow0, hpow1] at hn
    have hn' : B / Real.sqrt rho ≤ (n : ℝ) := by
      simpa only [mul_one] using hn
    calc
      B = Real.sqrt rho * (B / Real.sqrt rho) := by
        field_simp [hsqrt.ne']
      _ ≤ Real.sqrt rho * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hn' hsqrt.le
  filter_upwards [hfourier, hBsmall,
    Filter.eventually_ge_atTop (max Nrob 1)] with
      n hfourierN hBsmallN hn
  intro K P ell G f hbucket hpart hbalanced hcoeff hRamsey
  have hnOne : 1 ≤ n := (le_max_right Nrob 1).trans hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNrob : Nrob ≤ n := (le_max_left Nrob 1).trans hn
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
  obtain ⟨hleft, hraw⟩ :=
    hfourierN P ell G f hbucket hpart hbalanced hcoeff hRamsey
  let := hleft
  have hrobF : RobustRankAt 400 (rho * (n : ℝ) ^ 2) F := by
    exact hrob n hNrob (K + 1) P.bucket G (by omega)
      hpart.2.1 hpart.2.2 hbucket hRamsey
  have hF : F.IsHermitian :=
    bucketCenteredAdjacency_isHermitian P.bucket hbucket.choose G
  have hFbound : frobeniusSq F ≤ (n : ℝ) ^ 2 := by
    have hrawBound := frobeniusSq_le F 1 (by norm_num)
      hcoeff.2.2.1
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
    have hcostPos : 0 < rho * (n : ℝ) ^ 2 :=
      mul_pos hrho (sq_pos_of_pos hnR)
    exact hcostPos.trans_le hFrobLower
  have hFrobNonneg : 0 ≤ frobeniusSq F := hFrobPos.le
  have hvecNonneg : 0 ≤ vectorSqNorm f := by
    unfold vectorSqNorm
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have htargetNonneg : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f :=
    add_nonneg (mul_nonneg (by norm_num) hFrobNonneg) hvecNonneg
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
  have hBsigma : B ≤ sigma := hBsmallN.trans hsigmaLower
  have hcut : 2 / B ≤ nu := by
    calc
      2 / B ≤ 2 / B0 := by
        exact div_le_div_of_nonneg_left (by norm_num) hB0 hB0B
      _ = nu := by
        dsimp only [B0]
        field_simp [hnu.ne'] <;> norm_num
  have heps : 0 < B / sigma := div_pos hB hsigma
  have hepsOne : B / sigma ≤ 1 := (div_le_one hsigma).2 hBsigma
  have hgauss : ∀ y : ℝ,
      Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B / sigma) y ≤
        ((B / sigma) / eta) * Real.exp (-eta * |y|) :=
    hgaussian f hF hsigma hsigmaSq hFrobPos hrobThree heps hepsOne
  refine ⟨hleft, hsigma, ?_⟩
  intro x
  exact smallBall_productSlice_le_of_raw_fourier_and_gaussianNonuniform
    P ell f hsigma hB hBsigma heta hetaOne hcut hgauss hraw x

/-- Fixed-window consequence of the threshold form of Claim 12.1. -/
theorem exists_eventual_productSlice_claim121_nonuniform_upper
    (h52 : KSSSGaussianNonuniformUpper)
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ B : ℝ, 0 < B ∧ ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {K : ℕ}
          (P : BucketPartition (Fin n) (Fin (K + 1)))
          (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
          (f : Fin n → ℝ)
          (hbucket : Erdos88.RobustRank.HasEqualBuckets P.bucket),
          IsKSSSPartition delta P → IsNearBalanced delta P ell →
          HasKSSSBalancedCoefficients delta P f
            (bucketCenteredAdjacency P.bucket hbucket.choose G) →
          RamseyFree C G →
          ∃ hleft : Nonempty (ProductSlicePoint P ell),
            letI := hleft
            let F := bucketCenteredAdjacency P.bucket hbucket.choose G
            let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
            0 < sigma ∧ ∀ x : ℝ,
              Erdos88.Esseen.smallBall
                  (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                    (productSliceQuadratic P ell (-trace F) f F)) B x ≤
                Erdos88.Esseen.relativeEsseenConstant *
                  (B ^ 2 / (x ^ 2 + sigma ^ 2) +
                    (B / (eta * sigma)) *
                      Real.exp (-eta * |x| / (2 * sigma)) +
                    B * scale n (-6 / 5 : ℝ)) := by
  obtain ⟨B0, hB0, eta, heta, hetaOne, hthreshold⟩ :=
    exists_eventual_productSlice_claim121_nonuniform_upper_threshold
      h52 C delta hC hdelta hdeltaSmall
  exact ⟨B0, hB0, eta, heta, hetaOne, hthreshold B0 le_rfl⟩

/-- The exact Lemma 6.3 transfer used in the lower half of Claim 12.1,
stated with the interval-ratio hypothesis actually used in its proof. -/
theorem smallBall_productSlice_ge_of_normalized_gaussianSmallBallRatio
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    {sigma B R K E : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hK : 1 ≤ K) (hR : 4 ≤ R)
    (x : ℝ)
    (hratio : Erdos88.Esseen.SmallBallRatioOn
      ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)) (x / sigma)
      (B / sigma) R K)
    (hfourier : Erdos88.Esseen.fourierError
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (fun w ↦ productSliceQuadratic P ell (-trace F) f F w / sigma))
        ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
        (B / sigma) ≤ E) :
    (1 / 8 : ℝ) * Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B / sigma) (x / sigma) -
        Erdos88.Esseen.relativeEsseenConstant *
          (Erdos88.Esseen.concentration
              ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
              (B / sigma) / R + (B / sigma) * E) ≤
      Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F))
        ((10000 * K) * B) x := by
  let X := productSliceQuadratic P ell (-trace F) f F
  let mu := Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
    (fun w ↦ X w / sigma)
  let nu := (gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)
  let : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  let : IsProbabilityMeasure nu := by
    dsimp only [nu]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have heps : 0 < B / sigma := div_pos hB hsigma
  have hrelative := Erdos88.Esseen.relative_esseen_6_3_of_smallBallRatio
    mu nu heps hK hR hratio
  have herrorNonneg : 0 ≤ B / sigma := heps.le
  have hstep :
      (1 / 8 : ℝ) * Erdos88.Esseen.smallBall nu (B / sigma) (x / sigma) -
          Erdos88.Esseen.relativeEsseenConstant *
            (Erdos88.Esseen.concentration nu (B / sigma) / R +
              (B / sigma) * E) ≤
        Erdos88.Esseen.smallBall mu ((10000 * K) * (B / sigma)) (x / sigma) := by
    calc
      (1 / 8 : ℝ) * Erdos88.Esseen.smallBall nu (B / sigma) (x / sigma) -
          Erdos88.Esseen.relativeEsseenConstant *
            (Erdos88.Esseen.concentration nu (B / sigma) / R +
              (B / sigma) * E) ≤
        (1 / 8 : ℝ) * Erdos88.Esseen.smallBall nu (B / sigma) (x / sigma) -
          Erdos88.Esseen.relativeEsseenConstant *
            (Erdos88.Esseen.concentration nu (B / sigma) / R +
              (B / sigma) *
                Erdos88.Esseen.fourierError mu nu (B / sigma)) := by
          apply sub_le_sub_left
          apply mul_le_mul_of_nonneg_left _
            Erdos88.Esseen.relativeEsseenConstant_nonneg
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left hfourier herrorNonneg) _
      _ ≤ Erdos88.Esseen.smallBall mu ((10000 * K) * (B / sigma)) (x / sigma) :=
        hrelative
  change (1 / 8 : ℝ) * Erdos88.Esseen.smallBall nu (B / sigma) (x / sigma) -
      Erdos88.Esseen.relativeEsseenConstant *
        (Erdos88.Esseen.concentration nu (B / sigma) / R +
          (B / sigma) * E) ≤ _
  calc
    (1 / 8 : ℝ) * Erdos88.Esseen.smallBall nu (B / sigma) (x / sigma) -
        Erdos88.Esseen.relativeEsseenConstant *
          (Erdos88.Esseen.concentration nu (B / sigma) / R +
            (B / sigma) * E) ≤
      Erdos88.Esseen.smallBall mu ((10000 * K) * (B / sigma)) (x / sigma) := hstep
    _ = Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell) X)
          ((10000 * K) * B) x := by
      have hradius : (10000 * K) * (B / sigma) =
          ((10000 * K) * B) / sigma := by ring
      rw [hradius]
      simpa only [mu] using
        (smallBall_finiteUniformLaw_div X
          (sigma := sigma) (B := (10000 * K) * B) (x := x) hsigma)

/-- Density-ratio compatibility wrapper for the lower Claim 12.1 transfer. -/
theorem smallBall_productSlice_ge_of_normalized_gaussianDensityRatio
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    {sigma B R K E : ℝ}
    (hsigma : 0 < sigma) (hB : 0 < B) (hK : 1 ≤ K) (hR : 4 ≤ R)
    {p : ℝ → ℝ}
    (hdensity : Erdos88.Esseen.HasContinuousDensity
      ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)) p)
    (x : ℝ)
    (hratio : Erdos88.Esseen.DensityRatioOn p (x / sigma)
      (B / sigma) R K)
    (hfourier : Erdos88.Esseen.fourierError
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (fun w ↦ productSliceQuadratic P ell (-trace F) f F w / sigma))
        ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
        (B / sigma) ≤ E) :
    (1 / 8 : ℝ) * Erdos88.Esseen.smallBall
          ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
          (B / sigma) (x / sigma) -
        Erdos88.Esseen.relativeEsseenConstant *
          (Erdos88.Esseen.concentration
              ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma))
              (B / sigma) / R + (B / sigma) * E) ≤
      Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F))
        ((10000 * K) * B) x := by
  let : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  let : IsProbabilityMeasure
      ((gaussianQuadraticCenteredLaw f F).map (fun z ↦ z / sigma)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply smallBall_productSlice_ge_of_normalized_gaussianSmallBallRatio
    P ell f hsigma hB hK hR x _ hfourier
  exact Erdos88.Esseen.smallBallRatioOn_of_densityRatio
    _ hdensity (div_pos hB hsigma) (by linarith) hratio

end Erdos88.GaussianQuadratic
