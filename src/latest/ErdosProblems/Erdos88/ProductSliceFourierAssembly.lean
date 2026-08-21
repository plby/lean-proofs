import ErdosProblems.Erdos88.ProductSliceOuter
import ErdosProblems.Erdos88.AKSPrescribed
import ErdosProblems.Erdos88.SliceCouplingAsymptotic

open scoped BigOperators

namespace Erdos88.GaussianQuadratic

open Erdos88.BooleanSlices

lemma eventually_ksss_firstBucket_lemma81_conditions
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaSmall : delta < 3 / 400)
    (N : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ {K : ℕ}
        (P : BucketPartition (Fin n) (Fin (K + 1)))
        (ell : Fin (K + 1) → ℕ),
        IsKSSSPartition delta P → IsNearBalanced delta P ell →
          (n : ℝ) ^ (2 / 5 : ℝ) ≤ (P.fiber 0).card ∧
          N ≤ (P.fiber 0).card ∧
          0 < (P.fiber 0).card ∧
          (∀ k, ell k ≤ (P.fiber k).card) ∧
          (1 / 400 : ℝ) * (P.fiber 0).card ≤ ell 0 ∧
          (ell 0 : ℝ) ≤ (1 - (1 / 400 : ℝ)) * (P.fiber 0).card ∧
          ((P.fiber 0).card : ℝ) ^ (-1 + (1 / 400 : ℝ)) ≤
            (n : ℝ) ^ (-99 / 100 : ℝ) := by
  let a : ℝ := 1 - delta
  let eta : ℝ := 1 / 400
  let theta : ℝ := 2 / 5
  let z : ℝ := -1 + eta
  have ha : 0 < a := by dsimp only [a]; linarith
  have haHalf : 0 < a / 2 := div_pos ha (by norm_num)
  have htheta : theta < a := by dsimp only [theta, a]; linarith
  have hz : z < 0 := by dsimp only [z, eta]; norm_num
  have hexp : a * z < -99 / 100 := by
    dsimp only [a, z, eta]
    linarith
  have hsize :=
    Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
      2 theta a (by norm_num) htheta
  have hN :=
    Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
      (2 * N) 0 a (by positivity) ha
  have hlog := eventually_const_mul_log_le_scale 8 (a / 2)
    (by norm_num) haHalf
  have hfreq :=
    Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
      ((1 / 2 : ℝ) ^ z) (a * z) (-99 / 100)
      (Real.rpow_nonneg (by norm_num) _) hexp
  filter_upwards [Filter.eventually_ge_atTop 1, hsize, hN, hlog, hfreq]
    with n hn hsizeN hNN hlogN hfreqN
  intro K P ell hpart hbalanced
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hfiber := ksss_fiberCard_lower P delta hnpos
    hpart.2.2 hpart.1 (0 : Fin (K + 1))
  change (n : ℝ) ^ a / 2 ≤ ((P.fiber 0).card : ℝ) at hfiber
  have hsizeN' : 2 * (n : ℝ) ^ theta ≤ (n : ℝ) ^ a := by
    simpa only [theta, a] using hsizeN
  have hbucketTheta : (n : ℝ) ^ theta ≤ ((P.fiber 0).card : ℝ) := by
    linarith
  have hNreal : (N : ℝ) ≤ ((P.fiber 0).card : ℝ) := by
    have hNN' : (2 * N : ℝ) * (n : ℝ) ^ (0 : ℝ) ≤ (n : ℝ) ^ a := by
      simpa only [a] using hNN
    rw [Real.rpow_zero, mul_one] at hNN'
    have hhalf : (N : ℝ) ≤ (n : ℝ) ^ a / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      simpa only [mul_comm] using hNN'
    exact hhalf.trans hfiber
  have hNnat : N ≤ (P.fiber 0).card := by exact_mod_cast hNreal
  have hbucketPosReal : (0 : ℝ) < (P.fiber 0).card :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hnR theta) hbucketTheta
  have hbucketPos : 0 < (P.fiber 0).card := by exact_mod_cast hbucketPosReal
  have hscaleMul : scale n (a / 2) * scale n (a / 2) = scale n a := by
    rw [scale_mul hnpos]
    congr 1
    ring
  have hmargin :
      scale n ((1 - delta) / 2) * Real.log n ≤
        ((P.fiber 0).card : ℝ) / 4 := by
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have hscale0 : 0 ≤ scale n (a / 2) := scale_nonneg n _
    have hmul := mul_le_mul_of_nonneg_left hlogN hscale0
    have hW : scale n (a / 2) * Real.log n ≤ scale n a / 8 := by
      nlinarith [hscaleMul]
    have hquarter : scale n a / 8 ≤ ((P.fiber 0).card : ℝ) / 4 := by
      change (n : ℝ) ^ a / 8 ≤ ((P.fiber 0).card : ℝ) / 4
      linarith
    simpa only [a] using hW.trans hquarter
  have hbalanced0 := hbalanced (0 : Fin (K + 1))
  have habs :
      |(ell 0 : ℝ) - ((P.fiber 0).card : ℝ) / 2| ≤
        ((P.fiber 0).card : ℝ) / 4 :=
    hbalanced0.trans hmargin
  have hellLower :
      eta * ((P.fiber 0).card : ℝ) ≤ (ell 0 : ℝ) := by
    rw [abs_le] at habs
    dsimp only [eta]
    nlinarith [hbucketPosReal]
  have hellUpper :
      (ell 0 : ℝ) ≤ (1 - eta) * ((P.fiber 0).card : ℝ) := by
    rw [abs_le] at habs
    dsimp only [eta]
    nlinarith [hbucketPosReal]
  have hellFits : ∀ k, ell k ≤ (P.fiber k).card := by
    intro k
    have hcard : (P.fiber k).card = (P.fiber 0).card := hpart.1 k 0
    have hbalancedK := hbalanced k
    have hmarginK :
        scale n ((1 - delta) / 2) * Real.log n ≤
          ((P.fiber k).card : ℝ) / 4 := by
      rw [hcard]
      exact hmargin
    have habsK :
        |(ell k : ℝ) - ((P.fiber k).card : ℝ) / 2| ≤
          ((P.fiber k).card : ℝ) / 4 := hbalancedK.trans hmarginK
    have hkReal : (ell k : ℝ) ≤ ((P.fiber k).card : ℝ) := by
      rw [abs_le] at habsK
      nlinarith
    exact_mod_cast hkReal
  have hbasePos : 0 < (n : ℝ) ^ a / 2 := by positivity
  have hlocalFreq :
      ((P.fiber 0).card : ℝ) ^ z ≤ ((n : ℝ) ^ a / 2) ^ z :=
    Real.rpow_le_rpow_of_nonpos hbasePos hfiber hz.le
  have hbasePow :
      ((n : ℝ) ^ a / 2) ^ z =
        (1 / 2 : ℝ) ^ z * (n : ℝ) ^ (a * z) := by
    rw [show (n : ℝ) ^ a / 2 = (n : ℝ) ^ a * (1 / 2 : ℝ) by ring,
      Real.mul_rpow (Real.rpow_nonneg hnR.le _) (by norm_num),
      ← Real.rpow_mul hnR.le]
    ring
  refine ⟨?_, hNnat, hbucketPos, hellFits, ?_, ?_, ?_⟩
  · simpa only [theta] using hbucketTheta
  · simpa only [eta] using hellLower
  · simpa only [eta] using hellUpper
  · change ((P.fiber 0).card : ℝ) ^ z ≤ (n : ℝ) ^ (-99 / 100 : ℝ)
    calc
      ((P.fiber 0).card : ℝ) ^ z ≤ ((n : ℝ) ^ a / 2) ^ z := hlocalFreq
      _ = (1 / 2 : ℝ) ^ z * (n : ℝ) ^ (a * z) := hbasePow
      _ ≤ (n : ℝ) ^ (-99 / 100 : ℝ) := hfreqN

/-- Eventual source-scale Lemma 8.1 estimate for the full product slice.
The global Ramsey hypothesis is restricted to the first large bucket, and
the near-balanced window supplies the local slice hypotheses. -/
theorem exists_eventual_productSlice_lemma81_outer_two
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ nu : ℝ, 0 < nu ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {K s : ℕ}
          (P : BucketPartition (Fin n) (Fin (K + 1)))
          (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
          (f0 : ℝ) (f : Fin n → ℝ),
          IsKSSSPartition delta P → IsNearBalanced delta P ell →
          RamseyFree C G →
          ∃ hleft : Nonempty (ProductSlicePoint P ell),
            letI := hleft
            ∀ t : ℝ, (n : ℝ) ^ (-99 / 100 : ℝ) ≤ |t| → |t| ≤ nu →
              ‖finiteCharacteristic
                  (productSliceQuadratic P ell f0 f
                    (bucketCenteredAdjacency P.bucket s G)) t‖ ≤
                (n : ℝ) ^ (-2 : ℝ) := by
  have hClocal : 0 < C / (2 / 5 : ℝ) := by positivity
  obtain ⟨nu, hnu, N, houter⟩ :=
    exists_productSlice_lemma81_outer_two_bound
      (C / (2 / 5 : ℝ)) (1 / 400 : ℝ) hClocal
      (by norm_num) (by norm_num)
  have hconditions := eventually_ksss_firstBucket_lemma81_conditions
    delta hdelta hdeltaSmall N
  refine ⟨nu, hnu, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1, hconditions]
    with n hn hconditionsN
  intro K s P ell G f0 f hpart hbalanced hRamsey
  obtain ⟨hbucket, hN, hbucketPos, hellFits,
      hellLower, hellUpper, hfreq⟩ :=
    hconditionsN P ell hpart hbalanced
  let hleft : Nonempty (ProductSlicePoint P ell) :=
    productSlicePoint_nonempty P ell hellFits
  refine ⟨hleft, ?_⟩
  letI := hleft
  letI : ∀ k, Nonempty (BooleanSlicePoint (P.fiber k) (ell k)) :=
    fun k ↦ booleanSlicePoint_nonempty (hellFits k)
  have hInduced : RamseyFree (C / (2 / 5 : ℝ))
      (inducedOverFin G (P.fiber 0)) :=
    Erdos88.AKSGraph.ramseyFree_induce_overFin_of_rpow
      G (P.fiber 0) hC (by norm_num) hn hRamsey hbucket
  intro t htLower htUpper
  change ‖finiteCharacteristic
      (fun W : ProductSlicePoint P ell ↦
        sliceQuadratic f0 f (bucketCenteredAdjacency P.bucket s G) W.1) t‖ ≤
    (n : ℝ) ^ (-2 : ℝ)
  exact houter P ell G f0 f hn hbucket hbucketPos hN hInduced
    hellLower hellUpper t (hfreq.trans htLower) htUpper

/-- Concrete three-band Fourier comparison for the centered graph matrix on
a near-balanced KSSS product slice.  Lemma 11.1 controls the central band,
Lemma 8.1 controls the finite outer band, and Lemma 10.1 supplies Gaussian
robust rank 400. -/
theorem exists_eventual_productSlice_fourierL1_le
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ c : ℝ, 0 < c ∧
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
            (∫ t in -nu..nu,
              ‖finiteCharacteristic
                    (productSliceQuadratic P ell (-trace F) f F) t -
                gaussianQuadraticCharacteristic (-trace F) f F t‖) ≤
              (n : ℝ) ^ (-6 / 5 : ℝ) := by
  obtain ⟨nu, hnu, houter⟩ :=
    exists_eventual_productSlice_lemma81_outer_two
      C delta hC hdelta hdeltaSmall
  obtain ⟨c, hc, Nrob, hrob⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
      C delta 400 hC hdelta (by linarith)
  have hcentral := ksssLemma111 delta hdelta (by linarith)
  have hnumeric := eventually_three_band_rhs_outer_two_le
    (675 / 2) 6 ((c / 200) ^ (-100 : ℝ)) 1 nu delta
    (by norm_num) (by norm_num)
    (Real.rpow_nonneg (div_nonneg hc.le (by norm_num)) _)
    (by norm_num) hnu.le hdeltaSmall
  have hcutoff :=
    Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
      (1 / nu) (-99 / 100) 0 (by positivity) (by norm_num)
  refine ⟨nu, hnu, c, hc, ?_⟩
  filter_upwards [houter, hcentral, hnumeric, hcutoff,
    Filter.eventually_ge_atTop (max Nrob 1)]
    with n houterN hcentralN hnumericN hcutoffN hn
  intro K P ell G f hbucket hpart hbalanced hcoeff hRamsey
  have hnOne : 1 ≤ n := (le_max_right Nrob 1).trans hn
  have hNrob : Nrob ≤ n := (le_max_left Nrob 1).trans hn
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  obtain ⟨hleftOuter, hfinite⟩ :=
    houterN P ell G (-trace F) f hpart hbalanced hRamsey
  obtain ⟨_hleftCentral, _hmean, _hvariance, hlow⟩ :=
    hcentralN (K + 1) P ell (-trace F) f F hpart hbalanced hcoeff
  have hrobF : RobustRankAt 400 (c * (n : ℝ) ^ 2) F := by
    exact hrob n hNrob (K + 1) P.bucket G (by omega)
      hpart.2.1 hpart.2.2 hbucket hRamsey
  have hF : F.IsHermitian := by
    exact bucketCenteredAdjacency_isHermitian P.bucket hbucket.choose G
  have huT : (n : ℝ) ^ (-99 / 100 : ℝ) ≤ nu := by
    have hcutoffN' :
        (1 / nu) * (n : ℝ) ^ (-99 / 100 : ℝ) ≤ 1 := by
      simpa only [Real.rpow_zero] using hcutoffN
    calc
      (n : ℝ) ^ (-99 / 100 : ℝ) =
          nu * ((1 / nu) * (n : ℝ) ^ (-99 / 100 : ℝ)) := by
        field_simp [ne_of_gt hnu]
      _ ≤ nu * 1 := mul_le_mul_of_nonneg_left hcutoffN' hnu.le
      _ = nu := mul_one nu
  refine ⟨hleftOuter, ?_⟩
  letI := hleftOuter
  dsimp only
  exact fourierL1_le_rank400_of_outer_two_bounds
    (A := 675 / 2) (B := 6) (D := 1) (T := nu)
    (delta := delta) (c := c)
    (productSliceQuadratic P ell (-trace F) f F) f hF hc hnOne huT
    (by norm_num) (by norm_num) (by norm_num) hrobF
    (by
      intro t _ht
      change ‖finiteCharacteristic
            (productSliceQuadratic P ell (-trace F) f F) t -
          gaussianQuadraticCharacteristic (-trace F) f F t‖ ≤
        675 / 2 * |t| ^ 4 * scale n (3 + 12 * delta) +
          6 * |t| * scale n (3 / 4 + 4 * delta)
      exact hlow t)
    (by
      intro t htLower htUpper
      simpa only [one_mul] using hfinite t htLower htUpper)
    hnumericN

open Erdos88.BooleanSlices
open MeasureTheory ProbabilityTheory Real

lemma fourierError_productSlice_normalized_le_mul_raw
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    {sigma eps nu : ℝ} (hsigma : 0 < sigma) (heps : 0 < eps)
    (hcut : 2 / (eps * sigma) ≤ nu) :
    Erdos88.Esseen.fourierError
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (fun x ↦ productSliceQuadratic P ell (-trace F) f F x / sigma))
        ((gaussianQuadraticCenteredLaw f F).map (fun x ↦ x / sigma)) eps ≤
      sigma * (∫ t in -nu..nu,
        ‖finiteCharacteristic
              (productSliceQuadratic P ell (-trace F) f F) t -
          gaussianQuadraticCharacteristic (-trace F) f F t‖) := by
  let g : ℝ → ℝ := fun t ↦
    ‖finiteCharacteristic
          (productSliceQuadratic P ell (-trace F) f F) t -
      gaussianQuadraticCharacteristic (-trace F) f F t‖
  have hg : Continuous g :=
    continuous_norm.comp
      ((continuous_finiteCharacteristic
          (productSliceQuadratic P ell (-trace F) f F)).sub
        (continuous_gaussianQuadraticCharacteristic_centered f F))
  have hbound :
      (∫ t in -(2 / (eps * sigma))..(2 / (eps * sigma)), g t) ≤
        ∫ t in -nu..nu, g t := by
    apply intervalIntegral.integral_mono_interval
    · exact neg_le_neg hcut
    · linarith [div_pos (by norm_num : (0 : ℝ) < 2)
        (mul_pos heps hsigma)]
    · exact hcut
    · filter_upwards [] with t
      exact norm_nonneg _
    · exact hg.intervalIntegrable _ _
  rw [Erdos88.Esseen.fourierError]
  have hscale := intervalIntegral.integral_comp_div
    (f := g) (a := -(2 / eps)) (b := 2 / eps) (c := sigma) hsigma.ne'
  have heq :
      (∫ t in -(2 / eps)..(2 / eps), g (t / sigma)) =
        sigma * ∫ t in -(2 / (eps * sigma))..(2 / (eps * sigma)), g t := by
    simpa only [smul_eq_mul, div_div, neg_div] using hscale
  rw [show (fun t ↦
      ‖charFun
            (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
              (fun x ↦ productSliceQuadratic P ell (-trace F) f F x / sigma)) t -
        charFun ((gaussianQuadraticCenteredLaw f F).map
          (fun x ↦ x / sigma)) t‖) = fun t ↦ g (t / sigma) by
    funext t
    rw [charFun_finiteUniformLaw_eq_finiteCharacteristic,
      finiteCharacteristic_div,
      charFun_gaussianQuadraticCenteredLaw_map_div]]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hbound hsigma.le

lemma eventually_two_mul_scale_one_three_delta_mul_neg_six_fifths_le
    {delta : ℝ} (hdeltaSmall : delta < 3 / 400) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * scale n (1 + 3 * delta) * scale n (-6 / 5) ≤
        scale n (-1 / 6) := by
  have hexp : -1 / 5 + 3 * delta < -1 / 6 := by linarith
  have hrate := Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
    2 (-1 / 5 + 3 * delta) (-1 / 6) (by norm_num) hexp
  filter_upwards [hrate, Filter.eventually_ge_atTop 1] with n hrateN hn
  have hnpos : 0 < n := by omega
  calc
    2 * scale n (1 + 3 * delta) * scale n (-6 / 5) =
        2 * scale n (-1 / 5 + 3 * delta) := by
      rw [mul_assoc, scale_mul hnpos]
      congr 2
      ring
    _ ≤ scale n (-1 / 6) := hrateN

/-- The raw three-band estimate at Claim 12.1's fixed frequency scale,
after normalizing by the Gaussian standard deviation, is an actual Esseen
Fourier error of order `n⁻¹ᐟ⁶`. -/
theorem exists_eventual_productSlice_normalized_fourierError_le
    (C delta eps : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) (heps : 0 < eps) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ c : ℝ, 0 < c ∧
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
            0 < sigma ∧
              Real.sqrt c * (n : ℝ) ≤ sigma ∧
              sigma ≤ 2 * scale n (1 + 3 * delta) ∧
              Erdos88.Esseen.fourierError
                  (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                    (fun x ↦ productSliceQuadratic P ell
                      (-trace F) f F x / sigma))
                  ((gaussianQuadraticCenteredLaw f F).map
                    (fun x ↦ x / sigma)) eps ≤
                scale n (-1 / 6) := by
  obtain ⟨nu, hnu, _cFourier, _hcFourier, hfourier⟩ :=
    exists_eventual_productSlice_fourierL1_le
      C delta hC hdelta hdeltaSmall
  obtain ⟨c, hc, Nrob, hrob⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
      C delta 400 hC hdelta (by linarith)
  have hrate :=
    eventually_two_mul_scale_one_three_delta_mul_neg_six_fifths_le
      hdeltaSmall
  let A : ℝ := 2 / (eps * Real.sqrt c * nu)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcutRate :=
    Erdos88.QuadraticCancellation.eventually_const_mul_rpow_le_rpow
      A (-1) 0 hA (by norm_num)
  refine ⟨nu, hnu, c, hc, ?_⟩
  filter_upwards [hfourier, hrate, hcutRate,
    Filter.eventually_ge_atTop (max Nrob 1)] with
    n hfourierN hrateN hcutRateN hn
  intro K P ell G f hbucket hpart hbalanced hcoeff hRamsey
  have hnOne : 1 ≤ n := (le_max_right Nrob 1).trans hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNrob : Nrob ≤ n := (le_max_left Nrob 1).trans hn
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  let sigma := Real.sqrt (2 * frobeniusSq F + vectorSqNorm f)
  obtain ⟨hleft, hraw⟩ :=
    hfourierN P ell G f hbucket hpart hbalanced hcoeff hRamsey
  letI := hleft
  have hrobF : RobustRankAt 400 (c * (n : ℝ) ^ 2) F := by
    exact hrob n hNrob (K + 1) P.bucket G (by omega)
      hpart.2.1 hpart.2.2 hbucket hRamsey
  have hFrob : c * (n : ℝ) ^ 2 ≤ frobeniusSq F := by
    have hz := hrobF (0 : Matrix (Fin n) (Fin n) ℝ) (by simp)
    simpa only [sub_zero, frobenius_norm_sq_eq_frobeniusSq] using hz
  have hFrobNonneg : 0 ≤ frobeniusSq F := by
    unfold frobeniusSq
    exact Finset.sum_nonneg fun _ _ ↦
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hvecNonneg : 0 ≤ vectorSqNorm f := by
    unfold vectorSqNorm
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have htargetNonneg : 0 ≤ 2 * frobeniusSq F + vectorSqNorm f := by
    exact add_nonneg (mul_nonneg (by norm_num) hFrobNonneg) hvecNonneg
  have hsigmaSq : sigma ^ 2 = 2 * frobeniusSq F + vectorSqNorm f := by
    dsimp only [sigma]
    exact Real.sq_sqrt htargetNonneg
  have hsigmaLower : Real.sqrt c * (n : ℝ) ≤ sigma := by
    apply Erdos88.Structured.sigma_lower_bound (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _) hnR.le
    rw [hsigmaSq, mul_pow, Real.sq_sqrt hc.le]
    nlinarith
  have hsigma : 0 < sigma :=
    lt_of_lt_of_le (mul_pos (Real.sqrt_pos.2 hc) hnR) hsigmaLower
  have htargetUpper :
      2 * frobeniusSq F + vectorSqNorm f ≤
        3 * scale n (2 + 6 * delta) :=
    gaussianVarianceTarget_le_ksss delta hdelta.le hnOne f F
      hcoeff.2.1 hcoeff.2.2.1
  have hscaleSq : scale n (1 + 3 * delta) ^ 2 =
      scale n (2 + 6 * delta) := by
    rw [scale_sq hnpos.le]
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
  have hcutRateN : A * (n : ℝ) ^ (-1 : ℝ) ≤ 1 := by
    simpa only [Real.rpow_zero] using hcutRateN
  have hcut : 2 / (eps * sigma) ≤ nu := by
    have hdenLower : eps * (Real.sqrt c * (n : ℝ)) ≤ eps * sigma :=
      mul_le_mul_of_nonneg_left hsigmaLower heps.le
    calc
      2 / (eps * sigma) ≤ 2 / (eps * (Real.sqrt c * (n : ℝ))) :=
        div_le_div_of_nonneg_left (by norm_num)
          (mul_pos heps (mul_pos (Real.sqrt_pos.2 hc) hnR)) hdenLower
      _ = nu * (A * (n : ℝ) ^ (-1 : ℝ)) := by
        dsimp only [A]
        rw [Real.rpow_neg_one]
        field_simp [heps.ne', (Real.sqrt_pos.2 hc).ne', hnu.ne', hnR.ne']
      _ ≤ nu * 1 := mul_le_mul_of_nonneg_left hcutRateN hnu.le
      _ = nu := mul_one nu
  refine ⟨hleft, hsigma, hsigmaLower, hsigmaUpper, ?_⟩
  calc
    Erdos88.Esseen.fourierError
          (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
            (fun x ↦ productSliceQuadratic P ell (-trace F) f F x / sigma))
          ((gaussianQuadraticCenteredLaw f F).map
            (fun x ↦ x / sigma)) eps ≤
        sigma * (∫ t in -nu..nu,
          ‖finiteCharacteristic
                (productSliceQuadratic P ell (-trace F) f F) t -
            gaussianQuadraticCharacteristic (-trace F) f F t‖) :=
      fourierError_productSlice_normalized_le_mul_raw
        P ell f F hsigma heps hcut
    _ ≤ sigma * scale n (-6 / 5) :=
      mul_le_mul_of_nonneg_left hraw hsigma.le
    _ ≤ (2 * scale n (1 + 3 * delta)) * scale n (-6 / 5) :=
      mul_le_mul_of_nonneg_right hsigmaUpper (scale_nonneg n _)
    _ ≤ scale n (-1 / 6) := hrateN

lemma smallBall_finiteUniformLaw_div
    {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (X : Omega → ℝ) {sigma B x : ℝ} (hsigma : 0 < sigma) :
    Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw Omega (fun w ↦ X w / sigma))
        (B / sigma) (x / sigma) =
      Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw Omega X) B x := by
  rw [Erdos88.Esseen.smallBall_finiteUniformLaw,
    Erdos88.Esseen.smallBall_finiteUniformLaw]
  have hset :
      (Finset.univ.filter fun w : Omega ↦
        |X w / sigma - x / sigma| ≤ B / sigma) =
      (Finset.univ.filter fun w : Omega ↦ |X w - x| ≤ B) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show X w / sigma - x / sigma = (X w - x) / sigma by ring,
      abs_div, abs_of_pos hsigma, div_le_div_iff_of_pos_right hsigma]
  unfold Fourier.finProbability
  rw [hset]

/-- Deterministic upper half of Claim 12.1. A raw Fourier-window bound and
robust Gaussian rank imply a fixed raw-window small-ball estimate. -/
theorem smallBall_productSlice_le_of_raw_fourier_and_robustRank
    {n m r : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (ell : Fin m → ℕ) [Nonempty (ProductSlicePoint P ell)]
    (f : Fin n → ℝ) {F : Matrix (Fin n) (Fin n) ℝ}
    (hF : F.IsHermitian) {sigma s B nu E : ℝ}
    (hsigma : 0 < sigma) (hs : 0 < s) (hB : 0 < B)
    (hcut : 2 / B ≤ nu) (hrob : RobustRankAt r s F) (hr : 3 ≤ r)
    (hraw : (∫ t in -nu..nu,
      ‖finiteCharacteristic
            (productSliceQuadratic P ell (-trace F) f F) t -
        gaussianQuadraticCharacteristic (-trace F) f F t‖) ≤ E)
    (x : ℝ) :
    Erdos88.Esseen.smallBall
        (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
          (productSliceQuadratic P ell (-trace F) f F)) B x ≤
      (∑' k : ℤ, Erdos88.Esseen.kernelCellWeight k) *
        (2 * B / Real.sqrt s + B * E) := by
  let X := productSliceQuadratic P ell (-trace F) f F
  let mu := Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
    (fun w ↦ X w / sigma)
  let gamma := (gaussianQuadraticCenteredLaw f F).map (fun y ↦ y / sigma)
  letI : IsProbabilityMeasure (gaussianQuadraticCenteredLaw f F) := by
    unfold gaussianQuadraticCenteredLaw
    exact Measure.isProbabilityMeasure_map
      ((continuous_quadraticPolynomial 0 f F).sub continuous_const).aemeasurable
  letI : IsProbabilityMeasure gamma := by
    dsimp only [gamma]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have heps : 0 < B / sigma := div_pos hB hsigma
  have hcut' : 2 / ((B / sigma) * sigma) ≤ nu := by
    convert hcut using 1
    field_simp [hsigma.ne']
  have herr : Erdos88.Esseen.fourierError mu gamma (B / sigma) ≤ sigma * E := by
    calc
      Erdos88.Esseen.fourierError mu gamma (B / sigma) ≤
          sigma * (∫ t in -nu..nu,
            ‖finiteCharacteristic X t -
              gaussianQuadraticCharacteristic (-trace F) f F t‖) := by
        dsimp only [mu, gamma, X]
        exact fourierError_productSlice_normalized_le_mul_raw
          P ell f F hsigma heps hcut'
      _ ≤ sigma * E := mul_le_mul_of_nonneg_left hraw hsigma.le
  have hgauss : ∀ y : ℝ,
      Erdos88.Esseen.smallBall gamma (B / sigma) y ≤
        2 * (B / sigma) * sigma / Real.sqrt s := by
    intro y
    dsimp only [gamma]
    exact smallBall_gaussianQuadraticCenteredLaw_map_div_le_two_mul
      f hF hsigma hrob hr hs heps.le y
  have hconc : Erdos88.Esseen.concentration gamma (B / sigma) ≤
      2 * (B / sigma) * sigma / Real.sqrt s :=
    Erdos88.Esseen.concentration_le_of_smallBall_le gamma hgauss
  have hrel := Erdos88.Esseen.relative_esseen_6_1 mu gamma heps
  have hmass : 0 ≤ ∑' k : ℤ, Erdos88.Esseen.kernelCellWeight k :=
    tsum_nonneg Erdos88.Esseen.kernelCellWeight_nonneg
  rw [← smallBall_finiteUniformLaw_div X hsigma]
  calc
    Erdos88.Esseen.smallBall mu (B / sigma) (x / sigma) ≤
        Erdos88.Esseen.concentration mu (B / sigma) :=
      Erdos88.Esseen.smallBall_le_concentration _ _ _
    _ ≤ (∑' k : ℤ, Erdos88.Esseen.kernelCellWeight k) *
        (Erdos88.Esseen.concentration gamma (B / sigma) +
          (B / sigma) * Erdos88.Esseen.fourierError mu gamma (B / sigma)) := hrel
    _ ≤ (∑' k : ℤ, Erdos88.Esseen.kernelCellWeight k) *
        (2 * (B / sigma) * sigma / Real.sqrt s +
          (B / sigma) * (sigma * E)) := by
      apply mul_le_mul_of_nonneg_left _ hmass
      exact add_le_add hconc (mul_le_mul_of_nonneg_left herr heps.le)
    _ = (∑' k : ℤ, Erdos88.Esseen.kernelCellWeight k) *
        (2 * B / Real.sqrt s + B * E) := by
      field_simp [hsigma.ne']

/-- Eventual upper half of Claim 12.1 at a fixed raw window.  The window and
implicit constant depend only on the Ramsey and bucket-scale parameters. -/
theorem exists_eventual_productSlice_claim121_upper
    (C delta : ℝ) (hC : 0 < C) (hdelta : 0 < delta)
    (hdeltaSmall : delta < 3 / 400) :
    ∃ B : ℝ, 0 < B ∧ ∃ D : ℝ, 0 < D ∧
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
            ∀ x : ℝ,
              Erdos88.Esseen.smallBall
                  (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
                    (productSliceQuadratic P ell (-trace F) f F)) B x ≤
                D * scale n (-1) := by
  obtain ⟨nu, hnu, _cFourier, _hcFourier, hfourier⟩ :=
    exists_eventual_productSlice_fourierL1_le
      C delta hC hdelta hdeltaSmall
  obtain ⟨c, hc, Nrob, hrob⟩ :=
    exists_eventual_robustRankAt_bucketCenteredAdjacency_scaled
      C delta 400 hC hdelta (by linarith)
  let B : ℝ := 2 / nu
  let W : ℝ := ∑' k : ℤ, Erdos88.Esseen.kernelCellWeight k
  let D : ℝ := W * (2 * B / Real.sqrt c + B)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hW : 0 < W := by
    have h := Erdos88.Esseen.two_le_kernelCellWeightSum
    dsimp only [W]
    linarith
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos hW (add_pos (div_pos (mul_pos (by norm_num) hB)
      (Real.sqrt_pos.2 hc)) hB)
  refine ⟨B, hB, D, hD, ?_⟩
  filter_upwards [hfourier, Filter.eventually_ge_atTop (max Nrob 1)] with
    n hfourierN hn
  intro K P ell G f hbucket hpart hbalanced hcoeff hRamsey
  have hnOne : 1 ≤ n := (le_max_right Nrob 1).trans hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hNrob : Nrob ≤ n := (le_max_left Nrob 1).trans hn
  let F := bucketCenteredAdjacency P.bucket hbucket.choose G
  obtain ⟨hleft, hraw⟩ :=
    hfourierN P ell G f hbucket hpart hbalanced hcoeff hRamsey
  letI := hleft
  have hrobF : RobustRankAt 400 (c * (n : ℝ) ^ 2) F := by
    exact hrob n hNrob (K + 1) P.bucket G (by omega)
      hpart.2.1 hpart.2.2 hbucket hRamsey
  have hF : F.IsHermitian := by
    exact bucketCenteredAdjacency_isHermitian P.bucket hbucket.choose G
  have hs : 0 < c * (n : ℝ) ^ 2 := mul_pos hc (sq_pos_of_pos hnR)
  have hcut : 2 / B ≤ nu := by
    dsimp only [B]
    field_simp [hnu.ne'] <;> norm_num
  have hsqrt : Real.sqrt (c * (n : ℝ) ^ 2) =
      Real.sqrt c * (n : ℝ) := by
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq hnR.le]
  have hpow : scale n (-6 / 5 : ℝ) ≤ scale n (-1 : ℝ) :=
    scale_mono_exponent hnOne (by norm_num)
  have hscaleNegOne : scale n (-1) = (n : ℝ)⁻¹ := by
    unfold scale
    exact Real.rpow_neg_one _
  have hpowInv : scale n (-6 / 5 : ℝ) ≤ (n : ℝ)⁻¹ := by
    simpa only [hscaleNegOne] using hpow
  refine ⟨hleft, ?_⟩
  dsimp only
  intro x
  calc
    Erdos88.Esseen.smallBall
          (Erdos88.Esseen.finiteUniformLaw (ProductSlicePoint P ell)
            (productSliceQuadratic P ell (-trace F) f F)) B x ≤
        W * (2 * B / Real.sqrt (c * (n : ℝ) ^ 2) +
          B * scale n (-6 / 5 : ℝ)) := by
      dsimp only [W]
      exact smallBall_productSlice_le_of_raw_fourier_and_robustRank
        P ell f hF (sigma := 1) (s := c * (n : ℝ) ^ 2)
        (B := B) (nu := nu) (E := scale n (-6 / 5 : ℝ))
        (by norm_num) hs hB hcut hrobF (by norm_num) hraw x
    _ ≤ W * ((2 * B / Real.sqrt c) * scale n (-1) +
          B * scale n (-1)) := by
      apply mul_le_mul_of_nonneg_left _ hW.le
      rw [hsqrt, hscaleNegOne]
      apply add_le_add
      · field_simp [hnR.ne', (Real.sqrt_pos.2 hc).ne'] <;> norm_num
      · exact mul_le_mul_of_nonneg_left hpowInv hB.le
    _ = D * scale n (-1) := by
      dsimp only [D]
      ring

end Erdos88.GaussianQuadratic
