import ErdosProblems.Erdos88.GaussianQuadratic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

open scoped ENNReal NNReal Matrix.Norms.Frobenius
open MeasureTheory ProbabilityTheory Real Complex

namespace Erdos88
namespace GaussianQuadratic

noncomputable def centeredCoordinateLaw (a lam : ℝ) : Measure ℝ :=
  standardGaussian.map (centeredCoordinatePolynomial a lam)

lemma centeredCoordinateCharFactor_eq_charFun (a lam t : ℝ) :
    centeredCoordinateCharFactor a lam t =
      charFun (centeredCoordinateLaw a lam) t := by
  have hpoly : Measurable (centeredCoordinatePolynomial a lam) := by
    unfold centeredCoordinatePolynomial
    fun_prop
  rw [charFun_apply_real, centeredCoordinateLaw,
    integral_map hpoly.aemeasurable (by fun_prop)]
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  push_cast
  ring

lemma continuous_centeredCoordinateCharFactor (a lam : ℝ) :
    Continuous (centeredCoordinateCharFactor a lam) := by
  letI : IsFiniteMeasure (centeredCoordinateLaw a lam) :=
    Measure.isFiniteMeasure_map standardGaussian _
  have hfun : centeredCoordinateCharFactor a lam =
      charFun (centeredCoordinateLaw a lam) := by
    funext t
    exact centeredCoordinateCharFactor_eq_charFun a lam t
  rw [hfun]
  exact continuous_charFun

lemma continuous_diagonalCenteredCharProduct {ι : Type*} [Fintype ι]
    (a lam : ι → ℝ) :
    Continuous (diagonalCenteredCharProduct a lam) := by
  classical
  unfold diagonalCenteredCharProduct
  exact continuous_finsetProd _ fun i hi ↦
    continuous_centeredCoordinateCharFactor (a i) (lam i)

noncomputable def fourSpectralEnvelope (s t : ℝ) : ℝ :=
  (1 + 4 * s * t ^ 2)⁻¹

lemma fourSpectralEnvelope_nonneg {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    0 ≤ fourSpectralEnvelope s t := by
  unfold fourSpectralEnvelope
  positivity

lemma fourSpectralEnvelope_integrable {s : ℝ} (hs : 0 < s) :
    Integrable (fourSpectralEnvelope s) := by
  let R : ℝ := (2 * √s)⁻¹
  have hR : R ≠ 0 := by
    dsimp only [R]
    exact inv_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 hs).ne')
  have h := integrable_inv_one_add_sq.comp_div hR
  refine h.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  unfold fourSpectralEnvelope
  dsimp only [R]
  field_simp [Real.sqrt_pos.2 hs |>.ne']
  rw [Real.sq_sqrt hs.le]
  ring

theorem fourSpectralEnvelope_integral_Ioi_le {s K : ℝ}
    (hs : 0 < s) (hK : 0 < K) :
    ∫ t : ℝ in Set.Ioi K, fourSpectralEnvelope s t ≤ 1 / (4 * s * K) := by
  have hg : IntegrableOn (fun t : ℝ ↦ (4 * s)⁻¹ * t ^ (-2 : ℝ))
      (Set.Ioi K) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hK).const_mul (4 * s)⁻¹
  have hpoint : ∀ t ∈ Set.Ioi K,
      fourSpectralEnvelope s t ≤ (4 * s)⁻¹ * t ^ (-2 : ℝ) := by
    intro t ht
    have htpos : 0 < t := hK.trans ht
    rw [Real.rpow_neg_ofNat]
    unfold fourSpectralEnvelope
    field_simp [hs.ne', htpos.ne']
    nlinarith [sq_pos_of_pos htpos]
  have hf : IntegrableOn (fourSpectralEnvelope s) (Set.Ioi K) :=
    (fourSpectralEnvelope_integrable hs).integrableOn
  calc
    ∫ t : ℝ in Set.Ioi K, fourSpectralEnvelope s t ≤
        ∫ t : ℝ in Set.Ioi K, (4 * s)⁻¹ * t ^ (-2 : ℝ) :=
      setIntegral_mono_on hf hg measurableSet_Ioi hpoint
    _ = 1 / (4 * s * K) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hK]
      norm_num [Real.rpow_neg_natCast, zpow_neg, hK.ne']
      field_simp [hs.ne', hK.ne']
      rw [Real.rpow_neg_one]
      exact inv_mul_cancel₀ hK.ne'

theorem fourSpectralEnvelope_integral_twoSided_le {s K : ℝ}
    (hs : 0 < s) (hK : 0 < K) :
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K, fourSpectralEnvelope s t ≤
      1 / (2 * s * K) := by
  have hdisj : Disjoint (Set.Iic (-K)) (Set.Ioi K) := by
    rw [Set.disjoint_left]
    intro t htneg htpos
    change t ≤ -K at htneg
    change K < t at htpos
    linarith
  have heven (t : ℝ) :
      fourSpectralEnvelope s (-t) = fourSpectralEnvelope s t := by
    unfold fourSpectralEnvelope
    congr 1
    ring
  have hneg :
      ∫ t : ℝ in Set.Iic (-K), fourSpectralEnvelope s t =
        ∫ t : ℝ in Set.Ioi K, fourSpectralEnvelope s t := by
    simpa only [neg_neg, heven] using
      (integral_comp_neg_Iic (-K) (fourSpectralEnvelope s))
  have htail := fourSpectralEnvelope_integral_Ioi_le hs hK
  rw [setIntegral_union hdisj measurableSet_Ioi
    (fourSpectralEnvelope_integrable hs).integrableOn
    (fourSpectralEnvelope_integrable hs).integrableOn, hneg]
  calc
    (∫ t : ℝ in Set.Ioi K, fourSpectralEnvelope s t) +
        ∫ t : ℝ in Set.Ioi K, fourSpectralEnvelope s t ≤
        1 / (4 * s * K) + 1 / (4 * s * K) := add_le_add htail htail
    _ = 1 / (2 * s * K) := by
      field_simp [hs.ne', hK.ne']
      norm_num

theorem diagonalCharModulus_le_fourSpectralEnvelope
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : Fintype.card κ = 4)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 ≤ s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) (t : ℝ) :
    diagonalCharModulus a lam t ≤ fourSpectralEnvelope s t := by
  have h := diagonalCharModulus_le_of_spectralBlocks
    a lam B hdisj hs hblock t
  rw [hcard] at h
  norm_num [fourSpectralEnvelope, Real.rpow_neg_one] at h ⊢
  exact h

theorem diagonalCharModulus_le_fourSpectralEnvelope_of_four_le_card
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 ≤ s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) (t : ℝ) :
    diagonalCharModulus a lam t ≤ fourSpectralEnvelope s t := by
  have hdecay := diagonalCharModulus_le_of_spectralBlocks
    a lam B hdisj hs hblock t
  have hbase : 1 ≤ 1 + 4 * s * t ^ 2 := by
    nlinarith [mul_nonneg hs (sq_nonneg t)]
  have hcardReal : (4 : ℝ) ≤ Fintype.card κ := by
    exact_mod_cast hcard
  have hexp : (-(Fintype.card κ : ℝ) / 4 : ℝ) ≤ -1 := by
    linarith
  calc
    diagonalCharModulus a lam t ≤
        (1 + 4 * s * t ^ 2) ^ (-(Fintype.card κ : ℝ) / 4 : ℝ) := hdecay
    _ ≤ (1 + 4 * s * t ^ 2) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hbase hexp
    _ = fourSpectralEnvelope s t := by
      rw [Real.rpow_neg_one]
      rfl

theorem diagonalCenteredCharProduct_integrable_of_four_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : Fintype.card κ = 4)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) :
    Integrable (diagonalCenteredCharProduct a lam) := by
  apply (fourSpectralEnvelope_integrable hs).mono
  · exact (continuous_diagonalCenteredCharProduct a lam).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_diagonalCenteredCharProduct, Real.norm_eq_abs,
      abs_of_nonneg (fourSpectralEnvelope_nonneg hs.le t)]
    exact diagonalCharModulus_le_fourSpectralEnvelope
      a lam B hcard hdisj hs.le hblock t

theorem diagonalCenteredCharProduct_integrable_of_four_le_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s : ℝ} (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) :
    Integrable (diagonalCenteredCharProduct a lam) := by
  apply (fourSpectralEnvelope_integrable hs).mono
  · exact (continuous_diagonalCenteredCharProduct a lam).aestronglyMeasurable
  · filter_upwards [] with t
    rw [norm_diagonalCenteredCharProduct, Real.norm_eq_abs,
      abs_of_nonneg (fourSpectralEnvelope_nonneg hs.le t)]
    exact diagonalCharModulus_le_fourSpectralEnvelope_of_four_le_card
      a lam B hcard hdisj hs.le hblock t

theorem diagonalCharModulus_integral_twoSided_le_of_four_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : Fintype.card κ = 4)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) :
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K,
        diagonalCharModulus a lam t ≤ 1 / (2 * s * K) := by
  have hchar := diagonalCenteredCharProduct_integrable_of_four_spectralBlocks
    a lam B hcard hdisj hs hblock
  have hmod : Integrable (diagonalCharModulus a lam) :=
    hchar.norm.congr (Filter.Eventually.of_forall fun t ↦
      norm_diagonalCenteredCharProduct a lam t)
  calc
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K,
        diagonalCharModulus a lam t ≤
        ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K,
          fourSpectralEnvelope s t := by
      apply setIntegral_mono_on hmod.integrableOn
        (fourSpectralEnvelope_integrable hs).integrableOn
        (measurableSet_Iic.union measurableSet_Ioi)
      intro t ht
      exact diagonalCharModulus_le_fourSpectralEnvelope
        a lam B hcard hdisj hs.le hblock t
    _ ≤ 1 / (2 * s * K) :=
      fourSpectralEnvelope_integral_twoSided_le hs hK

theorem diagonalCharModulus_integral_twoSided_le_of_four_le_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2) :
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K,
        diagonalCharModulus a lam t ≤ 1 / (2 * s * K) := by
  have hchar := diagonalCenteredCharProduct_integrable_of_four_le_spectralBlocks
    a lam B hcard hdisj hs hblock
  have hmod : Integrable (diagonalCharModulus a lam) :=
    hchar.norm.congr (Filter.Eventually.of_forall fun t ↦
      norm_diagonalCenteredCharProduct a lam t)
  calc
    ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K,
        diagonalCharModulus a lam t ≤
        ∫ t : ℝ in Set.Iic (-K) ∪ Set.Ioi K,
          fourSpectralEnvelope s t := by
      apply setIntegral_mono_on hmod.integrableOn
        (fourSpectralEnvelope_integrable hs).integrableOn
        (measurableSet_Iic.union measurableSet_Ioi)
      intro t ht
      exact diagonalCharModulus_le_fourSpectralEnvelope_of_four_le_card
        a lam B hcard hdisj hs.le hblock t
    _ ≤ 1 / (2 * s * K) :=
      fourSpectralEnvelope_integral_twoSided_le hs hK

theorem standardNormal_hasInverseFourierDensity :
    HasInverseFourierDensity standardNormalDensity standardNormalChar := by
  intro u
  have hint :
      (∫ t : ℝ, standardNormalChar t *
          cexp (-(((t * u : ℝ) : ℂ) * I))) =
        (((2 * π : ℝ) : ℂ)) ^ (1 / 2 : ℂ) *
          cexp ((-(u ^ 2 / 2 : ℝ) : ℂ)) := by
    calc
      (∫ t : ℝ, standardNormalChar t *
          cexp (-(((t * u : ℝ) : ℂ) * I))) =
          ∫ t : ℝ, cexp (((-1 / 2 : ℂ) * (t : ℂ) ^ 2) +
            (-((u : ℂ) * I)) * (t : ℂ) + 0) := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [standardNormalChar, Complex.ofReal_exp]
        rw [← Complex.exp_add]
        apply congrArg cexp
        push_cast
        ring
      _ = ((π : ℂ) / -(-1 / 2 : ℂ)) ^ (1 / 2 : ℂ) *
          cexp (0 - (-((u : ℂ) * I)) ^ 2 / (4 * (-1 / 2 : ℂ))) := by
        exact integral_cexp_quadratic (by norm_num) (-((u : ℂ) * I)) 0
      _ = (((2 * π : ℝ) : ℂ)) ^ (1 / 2 : ℂ) *
          cexp ((-(u ^ 2 / 2 : ℝ) : ℂ)) := by
        congr 1
        · congr 1
          field_simp
          norm_cast
          ring
        · congr 1
          have hI : (-((u : ℂ) * I)) ^ 2 = -(u : ℂ) ^ 2 := by
            simp only [neg_sq, mul_pow, Complex.I_sq]
            ring
          rw [hI]
          push_cast
          ring
  rw [hint]
  unfold standardNormalDensity
  have hroot : (((2 * π : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
      ((√(2 * π) : ℝ) : ℂ) := by
    calc
      (((2 * π : ℝ) : ℂ)) ^ (1 / 2 : ℂ) =
          (((2 * π) ^ (1 / 2 : ℝ) : ℝ) : ℂ) :=
        by
          convert (Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * π)
            (1 / 2 : ℝ)).symm using 1 <;> norm_num
      _ = ((√(2 * π) : ℝ) : ℂ) := by rw [Real.sqrt_eq_rpow]
  rw [ofReal_div, ofReal_exp]
  rw [hroot]
  have hbase : (((2 * π : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hsqrt : ((√(2 * π) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
  field_simp [hbase, hsqrt]
  have hbaseEq : ((2 * π : ℝ) : ℂ) = ((√(2 * π) : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow]
    exact congrArg (fun x : ℝ ↦ (x : ℂ))
      (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * π) |>.symm)
  rw [hbaseEq]
  calc
    cexp (((-(u ^ 2 / 2) : ℝ) : ℂ)) * ((√(2 * π) : ℝ) : ℂ) ^ 2 =
        ((√(2 * π) : ℝ) : ℂ) ^ 2 *
          cexp (((-(u ^ 2 / 2) : ℝ) : ℂ)) := by ring
    _ = ((√(2 * π) : ℝ) : ℂ) ^ 2 *
          cexp (-(((u ^ 2 / 2 : ℝ) : ℂ))) := by
      congr 1
      apply congrArg cexp
      push_cast
      ring

/-- The four-block spectral form of the diagonal Gaussian local-CLT
comparison.  The spectral blocks discharge both characteristic-function
integrability and the full tail integral; the standard normal inversion is
also unconditional. -/
theorem diagonalDensityComparison_of_coordinateMoments_of_four_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : Fintype.card κ = 4)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {p : ℝ → ℝ} {s : ℝ}
    (hsum : totalVariance a lam = 1)
    (hlower : ∀ i, coordinateSigma (a i) (lam i) ^ 3 ≤
      coordinateThirdAbsMoment (a i) (lam i))
    (hupper : ∀ i, coordinateThirdAbsMoment (a i) (lam i) ≤
      8 * coordinateSigma (a i) (lam i) ^ 3)
    (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2)
    (hpInv : HasInverseFourierDensity p (diagonalCenteredCharProduct a lam))
    (hstandard : ∀ t : ℝ, |t| ≤ 1 / (4 * lyapunovL a lam) →
      ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
        16 * lyapunovL a lam * localCLTEnvelope t)
    (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ *
        (1280 / lyapunovGamma a lam +
          16 / (s * lyapunovGamma a lam)) := by
  have hGamma : 0 < lyapunovGamma a lam :=
    lyapunovGamma_pos_of_totalVariance_eq_one a lam hsum
  have hchar : Integrable (diagonalCenteredCharProduct a lam) :=
    diagonalCenteredCharProduct_integrable_of_four_spectralBlocks
      a lam B hcard hdisj hs hblock
  have htailRaw :=
    diagonalCharModulus_integral_twoSided_le_of_four_spectralBlocks
      a lam B hcard hdisj hs (show 0 < lyapunovGamma a lam / 32 by positivity)
        hblock
  have htail :
      ∫ t : ℝ in
          Set.Iic (-(lyapunovGamma a lam / 32)) ∪
            Set.Ioi (lyapunovGamma a lam / 32),
          diagonalCharModulus a lam t ≤
        16 / (s * lyapunovGamma a lam) := by
    calc
      ∫ t : ℝ in
          Set.Iic (-(lyapunovGamma a lam / 32)) ∪
            Set.Ioi (lyapunovGamma a lam / 32),
          diagonalCharModulus a lam t ≤
          1 / (2 * s * (lyapunovGamma a lam / 32)) := htailRaw
      _ = 16 / (s * lyapunovGamma a lam) := by
        field_simp [hs.ne', hGamma.ne']
        ring
  exact diagonalDensityComparison_of_coordinateMoments_of_inverseFourier
    a lam hsum hlower hupper hchar hpInv standardNormal_hasInverseFourierDensity
      hstandard htail u

/-- The source-shaped rank-`r` version used with the rank-400 block family in
KSSS Claim 12.1.  Four or more disjoint positive-mass spectral blocks suffice
for the same integrability and explicit tail estimate. -/
theorem diagonalDensityComparison_of_coordinateMoments_of_four_le_spectralBlocks
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a lam : ι → ℝ) (B : κ → Finset ι)
    (hcard : 4 ≤ Fintype.card κ)
    (hdisj : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset κ) : Set κ) B)
    {p : ℝ → ℝ} {s : ℝ}
    (hsum : totalVariance a lam = 1)
    (hlower : ∀ i, coordinateSigma (a i) (lam i) ^ 3 ≤
      coordinateThirdAbsMoment (a i) (lam i))
    (hupper : ∀ i, coordinateThirdAbsMoment (a i) (lam i) ≤
      8 * coordinateSigma (a i) (lam i) ^ 3)
    (hs : 0 < s)
    (hblock : ∀ j, s ≤ ∑ i ∈ B j, (lam i) ^ 2)
    (hpInv : HasInverseFourierDensity p (diagonalCenteredCharProduct a lam))
    (hstandard : ∀ t : ℝ, |t| ≤ 1 / (4 * lyapunovL a lam) →
      ‖diagonalCenteredCharProduct a lam t - standardNormalChar t‖ ≤
        16 * lyapunovL a lam * localCLTEnvelope t)
    (u : ℝ) :
    |p u - standardNormalDensity u| ≤
      (2 * π)⁻¹ *
        (1280 / lyapunovGamma a lam +
          16 / (s * lyapunovGamma a lam)) := by
  have hGamma : 0 < lyapunovGamma a lam :=
    lyapunovGamma_pos_of_totalVariance_eq_one a lam hsum
  have hchar : Integrable (diagonalCenteredCharProduct a lam) :=
    diagonalCenteredCharProduct_integrable_of_four_le_spectralBlocks
      a lam B hcard hdisj hs hblock
  have htailRaw :=
    diagonalCharModulus_integral_twoSided_le_of_four_le_spectralBlocks
      a lam B hcard hdisj hs (show 0 < lyapunovGamma a lam / 32 by positivity)
        hblock
  have htail :
      ∫ t : ℝ in
          Set.Iic (-(lyapunovGamma a lam / 32)) ∪
            Set.Ioi (lyapunovGamma a lam / 32),
          diagonalCharModulus a lam t ≤
        16 / (s * lyapunovGamma a lam) := by
    calc
      ∫ t : ℝ in
          Set.Iic (-(lyapunovGamma a lam / 32)) ∪
            Set.Ioi (lyapunovGamma a lam / 32),
          diagonalCharModulus a lam t ≤
          1 / (2 * s * (lyapunovGamma a lam / 32)) := htailRaw
      _ = 16 / (s * lyapunovGamma a lam) := by
        field_simp [hs.ne', hGamma.ne']
        ring
  exact diagonalDensityComparison_of_coordinateMoments_of_inverseFourier
    a lam hsum hlower hupper hchar hpInv standardNormal_hasInverseFourierDensity
      hstandard htail u

end GaussianQuadratic
end Erdos88
