import ErdosProblems.Erdos520.HarperBlockGaussian
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped Interval

namespace Erdos
namespace Problem520

/-!
# An Esseen smoothing layer

This file isolates the deterministic smoothing step in a one-dimensional
Esseen argument.  The Fourier inversion estimate for a chosen band-limited
kernel can be supplied separately: once the convolved distribution functions
are within `ε`, the theorem below transfers that estimate to the original
distribution functions.  The loss is explicit and contains the standard
absorption factor `1 - 2 * α`, where `α` is the mass of the smoothing kernel
outside its central window.
-/

/-! ## Kolmogorov distance for bounded real functions -/

/-- Supremum distance between two real-valued functions.  The useful API
below assumes an explicit common range bound, so the conditionally complete
supremum on `ℝ` is always applied to a bounded nonempty set. -/
noncomputable def harperKolmogorovDistance (F G : ℝ → ℝ) : ℝ :=
  sSup (Set.range fun x ↦ |F x - G x|)

theorem abs_sub_le_harperKolmogorovDistance
    {F G : ℝ → ℝ} {B : ℝ}
    (hB : ∀ x, |F x - G x| ≤ B) (x : ℝ) :
    |F x - G x| ≤ harperKolmogorovDistance F G := by
  unfold harperKolmogorovDistance
  apply le_csSup
  · exact ⟨B, by rintro _ ⟨y, rfl⟩; exact hB y⟩
  · exact ⟨x, rfl⟩

theorem harperKolmogorovDistance_le
    {F G : ℝ → ℝ} {B : ℝ}
    (hB : ∀ x, |F x - G x| ≤ B) :
    harperKolmogorovDistance F G ≤ B := by
  unfold harperKolmogorovDistance
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  exact hB x

theorem harperKolmogorovDistance_nonneg
    {F G : ℝ → ℝ} {B : ℝ}
    (hB : ∀ x, |F x - G x| ≤ B) :
    0 ≤ harperKolmogorovDistance F G := by
  exact (abs_nonneg (F 0 - G 0)).trans
    (abs_sub_le_harperKolmogorovDistance hB 0)

/-! ## Smoothing by an additive noise law -/

/-- Convolution of a real function with a smoothing probability law, written
in the orientation used for distribution functions. -/
noncomputable def harperSmooth (κ : Measure ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, F (x - y) ∂κ

private theorem integrable_comp_sub_of_mem_Icc
    {κ : Measure ℝ} [IsProbabilityMeasure κ]
    {F : ℝ → ℝ} (hFmeas : Measurable F)
    (hF : ∀ x, F x ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    Integrable (fun y ↦ F (x - y)) κ := by
  refine (integrable_const (μ := κ) (1 : ℝ)).mono
    (hFmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (hF (x - y)).1]
  simpa using! (hF (x - y)).2

private theorem integrable_indicator_real
    {κ : Measure ℝ} [IsProbabilityMeasure κ]
    {s : Set ℝ} (hs : MeasurableSet s) :
    Integrable (s.indicator (fun _ : ℝ ↦ (1 : ℝ))) κ := by
  exact (integrable_const (μ := κ) (1 : ℝ)).indicator hs

/-- The central deterministic estimate behind Esseen smoothing.  If `F` is
monotone, `G` is `M`-Lipschitz, both take values in `[0,1]`, and a smoothing
law has at most mass `α` outside `[-δ,δ]`, then a uniform smoothed error `ε`
implies the displayed self-improving bound for every point. -/
theorem abs_sub_le_of_smooth_le
    {F G : ℝ → ℝ} {κ : Measure ℝ} [IsProbabilityMeasure κ]
    {M δ α ε B : ℝ}
    (hFmono : Monotone F)
    (hFmeas : Measurable F) (hGmeas : Measurable G)
    (hF : ∀ x, F x ∈ Icc (0 : ℝ) 1)
    (hG : ∀ x, G x ∈ Icc (0 : ℝ) 1)
    (hGlip : ∀ x y, |G x - G y| ≤ M * |x - y|)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hglobal : ∀ x, |F x - G x| ≤ B)
    (htail : κ.real {y | δ < |y|} ≤ α)
    (hsmooth : ∀ x, |harperSmooth κ F x - harperSmooth κ G x| ≤ ε)
    (x : ℝ) :
    |F x - G x| ≤ ε + 2 * M * δ + 2 * B * α := by
  let bad : Set ℝ := {y | δ < |y|}
  have hbad : MeasurableSet bad := measurableSet_lt measurable_const measurable_abs
  have hFint (z : ℝ) : Integrable (fun y ↦ F (z - y)) κ :=
    integrable_comp_sub_of_mem_Icc hFmeas hF z
  have hGint (z : ℝ) : Integrable (fun y ↦ G (z - y)) κ :=
    integrable_comp_sub_of_mem_Icc hGmeas hG z
  have hind : Integrable (bad.indicator (fun _ : ℝ ↦ (1 : ℝ))) κ :=
    integrable_indicator_real hbad
  have hD := hglobal x
  have hupper : F x - G x ≤ ε + 2 * M * δ + 2 * B * α := by
    let z := x + δ
    have hpoint : ∀ y : ℝ,
        F x - G x - 2 * M * δ -
            2 * B * bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) y ≤
          F (z - y) - G (z - y) := by
      intro y
      by_cases hy : y ∈ bad
      · simp only [Set.indicator_of_mem hy, mul_one]
        have hzbound : -B ≤ F (z - y) - G (z - y) := by
          exact (neg_le_of_abs_le (hglobal (z - y)))
        have hxB : F x - G x ≤ B := le_trans (le_abs_self _) hD
        calc
          F x - G x - 2 * M * δ - 2 * B ≤ -B := by
            nlinarith [mul_nonneg hM hδ]
          _ ≤ F (z - y) - G (z - y) := hzbound
      · simp only [Set.indicator_of_notMem hy, mul_zero, sub_zero]
        have hyabs : |y| ≤ δ := le_of_not_gt hy
        have hylo : x ≤ z - y := by
          dsimp [z]
          have : y ≤ δ := le_trans (le_abs_self y) hyabs
          linarith
        have hyhi : z - y ≤ x + 2 * δ := by
          dsimp [z]
          have : -δ ≤ y := by
            exact (neg_le_of_abs_le hyabs)
          linarith
        have hFm : F x ≤ F (z - y) := hFmono hylo
        have hGdiff : G (z - y) - G x ≤ 2 * M * δ := by
          have hLip := hGlip (z - y) x
          have habsxy : |z - y - x| ≤ 2 * δ := by
            rw [abs_le]
            constructor <;> linarith
          calc
            G (z - y) - G x ≤ |G (z - y) - G x| := le_abs_self _
            _ ≤ M * |z - y - x| := hLip
            _ ≤ M * (2 * δ) := mul_le_mul_of_nonneg_left habsxy hM
            _ = 2 * M * δ := by ring
        linarith
    have hlower :
        F x - G x - 2 * M * δ - 2 * B * κ.real bad ≤
          harperSmooth κ F z - harperSmooth κ G z := by
      have hconstInt : Integrable
          (fun y : ℝ ↦ F x - G x - 2 * M * δ -
            2 * B * bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) y) κ := by
        fun_prop
      have hdiffInt := (hFint z).sub (hGint z)
      have hmono :
          (∫ y, F x - G x - 2 * M * δ -
              2 * B * bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) y ∂κ) ≤
            ∫ y, F (z - y) - G (z - y) ∂κ := by
        simpa only [Pi.sub_apply] using!
          (integral_mono hconstInt hdiffInt hpoint)
      have hleft :
          (∫ y, F x - G x - 2 * M * δ -
              2 * B * bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) y ∂κ) =
            F x - G x - 2 * M * δ - 2 * B * κ.real bad := by
        have hi :
            (∫ a, bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) a ∂κ) =
              κ.real bad := by
          simpa only using! (integral_indicator_one (μ := κ) hbad)
        rw [integral_sub (integrable_const _) (hind.const_mul (2 * B)),
          integral_const, probReal_univ, one_smul,
          integral_const_mul, hi]
      have hright :
          (∫ y, F (z - y) - G (z - y) ∂κ) =
            harperSmooth κ F z - harperSmooth κ G z := by
        rw [integral_sub (hFint z) (hGint z)]
        rfl
      rwa [hleft, hright] at hmono
    have hsmoothUpper :
        harperSmooth κ F z - harperSmooth κ G z ≤ ε :=
      le_trans (le_abs_self _) (hsmooth z)
    have htail' : κ.real bad ≤ α := by simpa [bad] using! htail
    calc
      F x - G x ≤ ε + 2 * M * δ + 2 * B * κ.real bad := by linarith
      _ ≤ ε + 2 * M * δ + 2 * B * α := by
        gcongr
  have hlower : -(ε + 2 * M * δ + 2 * B * α) ≤ F x - G x := by
    let z := x - δ
    have hpoint : ∀ y : ℝ,
        F (z - y) - G (z - y) ≤
          F x - G x + 2 * M * δ +
            2 * B * bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ bad
      · simp only [Set.indicator_of_mem hy, mul_one]
        have hzbound : F (z - y) - G (z - y) ≤ B :=
          le_trans (le_abs_self _) (hglobal (z - y))
        have hxB : -B ≤ F x - G x := neg_le_of_abs_le hD
        calc
          F (z - y) - G (z - y) ≤ B := hzbound
          _ ≤ F x - G x + 2 * M * δ + 2 * B := by
            nlinarith [mul_nonneg hM hδ]
      · simp only [Set.indicator_of_notMem hy, mul_zero, add_zero]
        have hyabs : |y| ≤ δ := le_of_not_gt hy
        have hylo : x - 2 * δ ≤ z - y := by
          dsimp [z]
          have : y ≤ δ := le_trans (le_abs_self y) hyabs
          linarith
        have hyhi : z - y ≤ x := by
          dsimp [z]
          have : -δ ≤ y := neg_le_of_abs_le hyabs
          linarith
        have hFm : F (z - y) ≤ F x := hFmono hyhi
        have hGdiff : G x - G (z - y) ≤ 2 * M * δ := by
          have hLip := hGlip x (z - y)
          have habsxy : |x - (z - y)| ≤ 2 * δ := by
            rw [abs_le]
            constructor <;> linarith
          calc
            G x - G (z - y) ≤ |G x - G (z - y)| := le_abs_self _
            _ ≤ M * |x - (z - y)| := hLip
            _ ≤ M * (2 * δ) := mul_le_mul_of_nonneg_left habsxy hM
            _ = 2 * M * δ := by ring
        linarith
    have hupperInt :
        harperSmooth κ F z - harperSmooth κ G z ≤
          F x - G x + 2 * M * δ + 2 * B * κ.real bad := by
      have hconstInt : Integrable
          (fun y : ℝ ↦ F x - G x + 2 * M * δ +
            2 * B * bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) y) κ := by
        fun_prop
      have hdiffInt := (hFint z).sub (hGint z)
      have hmono :
          (∫ y, F (z - y) - G (z - y) ∂κ) ≤
            ∫ y, F x - G x + 2 * M * δ +
              2 * B * bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) y ∂κ := by
        simpa only [Pi.sub_apply] using!
          (integral_mono hdiffInt hconstInt hpoint)
      have hleft :
          (∫ y, F (z - y) - G (z - y) ∂κ) =
            harperSmooth κ F z - harperSmooth κ G z := by
        rw [integral_sub (hFint z) (hGint z)]
        rfl
      have hright :
          (∫ y, F x - G x + 2 * M * δ +
              2 * B * bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) y ∂κ) =
            F x - G x + 2 * M * δ + 2 * B * κ.real bad := by
        have hi :
            (∫ a, bad.indicator (fun _ : ℝ ↦ (1 : ℝ)) a ∂κ) =
              κ.real bad := by
          simpa only using! (integral_indicator_one (μ := κ) hbad)
        rw [integral_add (integrable_const _) (hind.const_mul (2 * B)),
          integral_const, probReal_univ, one_smul,
          integral_const_mul, hi]
      rwa [hleft, hright] at hmono
    have hsmoothLower :
        -ε ≤ harperSmooth κ F z - harperSmooth κ G z :=
      (neg_le_of_abs_le (hsmooth z))
    have htail' : κ.real bad ≤ α := by simpa [bad] using! htail
    calc
      -(ε + 2 * M * δ + 2 * B * α) ≤
          -(ε + 2 * M * δ + 2 * B * κ.real bad) := by
        gcongr
      _ ≤ F x - G x := by linarith
  rw [abs_le]
  exact ⟨hlower, hupper⟩

/-- Absorbed form of the smoothing estimate.  The supremum error appearing
on the tail of the smoothing law is moved to the left, producing the
characteristic Esseen denominator `1 - 2 * α`. -/
theorem harperKolmogorovDistance_le_of_smooth_le
    {F G : ℝ → ℝ} {κ : Measure ℝ} [IsProbabilityMeasure κ]
    {M δ α ε : ℝ}
    (hFmono : Monotone F)
    (hFmeas : Measurable F) (hGmeas : Measurable G)
    (hF : ∀ x, F x ∈ Icc (0 : ℝ) 1)
    (hG : ∀ x, G x ∈ Icc (0 : ℝ) 1)
    (hGlip : ∀ x y, |G x - G y| ≤ M * |x - y|)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hαhalf : 2 * α < 1)
    (htail : κ.real {y | δ < |y|} ≤ α)
    (hsmooth : ∀ x, |harperSmooth κ F x - harperSmooth κ G x| ≤ ε) :
    harperKolmogorovDistance F G ≤
      (ε + 2 * M * δ) / (1 - 2 * α) := by
  have hOne : ∀ x, |F x - G x| ≤ (1 : ℝ) := by
    intro x
    rw [abs_le]
    constructor <;> linarith [(hF x).1, (hF x).2, (hG x).1, (hG x).2]
  let D := harperKolmogorovDistance F G
  have hD0 : 0 ≤ D := harperKolmogorovDistance_nonneg hOne
  have hD : ∀ x, |F x - G x| ≤ D :=
    abs_sub_le_harperKolmogorovDistance hOne
  have hpoint : ∀ x, |F x - G x| ≤
      ε + 2 * M * δ + 2 * D * α := by
    intro x
    exact abs_sub_le_of_smooth_le hFmono hFmeas hGmeas hF hG hGlip
      hM hδ hD0 hD htail hsmooth x
  have hself : D ≤ ε + 2 * M * δ + 2 * D * α :=
    harperKolmogorovDistance_le hpoint
  have hdenom : 0 < 1 - 2 * α := by linarith
  apply (le_div_iff₀ hdenom).2
  dsimp [D] at hself ⊢
  nlinarith

/-! ## Probability-measure specialization -/

/-- Kolmogorov distance between two real probability measures. -/
noncomputable def harperCDFDistance (μ ν : Measure ℝ) : ℝ :=
  harperKolmogorovDistance (cdf μ) (cdf ν)

theorem harperCDFDistance_le_of_smooth_le
    (μ ν κ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ]
    {M δ α ε : ℝ}
    (hνlip : ∀ x y, |cdf ν x - cdf ν y| ≤ M * |x - y|)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hαhalf : 2 * α < 1)
    (htail : κ.real {y | δ < |y|} ≤ α)
    (hsmooth : ∀ x,
      |harperSmooth κ (cdf μ) x - harperSmooth κ (cdf ν) x| ≤ ε) :
    harperCDFDistance μ ν ≤
      (ε + 2 * M * δ) / (1 - 2 * α) := by
  unfold harperCDFDistance
  exact harperKolmogorovDistance_le_of_smooth_le
    (monotone_cdf μ) (monotone_cdf μ).measurable
    (monotone_cdf ν).measurable
    (fun x ↦ ⟨cdf_nonneg μ x, cdf_le_one μ x⟩)
    (fun x ↦ ⟨cdf_nonneg ν x, cdf_le_one ν x⟩)
    hνlip hM hδ hαhalf htail hsmooth

/-- Explicit `O(1/T)` form.  A kernel concentrated at scale `c/T` and a
smoothed comparison of size `E/T` give a Kolmogorov comparison of size a
fixed constant times `1/T`. -/
theorem harperCDFDistance_le_inv_of_smooth_le
    (μ ν κ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure κ]
    {M c α E T : ℝ}
    (hνlip : ∀ x y, |cdf ν x - cdf ν y| ≤ M * |x - y|)
    (hM : 0 ≤ M) (hc : 0 ≤ c) (hT : 0 < T)
    (hαhalf : 2 * α < 1)
    (htail : κ.real {y | c / T < |y|} ≤ α)
    (hsmooth : ∀ x,
      |harperSmooth κ (cdf μ) x - harperSmooth κ (cdf ν) x| ≤ E / T) :
    harperCDFDistance μ ν ≤
      (E + 2 * M * c) / ((1 - 2 * α) * T) := by
  have hbase := harperCDFDistance_le_of_smooth_le μ ν κ hνlip hM
    (div_nonneg hc hT.le) hαhalf htail hsmooth
  calc
    harperCDFDistance μ ν ≤
        (E / T + 2 * M * (c / T)) / (1 - 2 * α) := hbase
    _ = (E + 2 * M * c) / ((1 - 2 * α) * T) := by
      field_simp

/-! ## The low-frequency Esseen integral -/

theorem continuous_harperTiltedLinearPrimeCharacteristic
    (p : ℕ) (t u : ℝ) :
    Continuous (fun v ↦ harperTiltedLinearPrimeCharacteristic p t u v) := by
  have hrepr :
      (fun v ↦ harperTiltedLinearPrimeCharacteristic p t u v) =
        fun v ↦ ∑ b : Bool,
          (harperTiltedCoin p t).real {b} •
            Complex.exp (harperCharacteristicExponent p t u v b) := by
    funext v
    rw [harperTiltedLinearPrimeCharacteristic,
      integral_fintype Integrable.of_finite]
  rw [hrepr]
  unfold harperCharacteristicExponent
  fun_prop

theorem continuous_harperTiltedLinearPrimeBlockCharacteristic
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    Continuous
      (fun v ↦ harperTiltedLinearPrimeBlockCharacteristic y S t u v) := by
  have hrepr :
      (fun v ↦ harperTiltedLinearPrimeBlockCharacteristic y S t u v) =
        fun v ↦ ∏ p ∈ S,
          harperTiltedLinearPrimeCharacteristic p.1 t u v := by
    funext v
    exact harperTiltedLinearPrimeBlockCharacteristic_eq_prod y S t u v
  rw [hrepr]
  exact continuous_finset_prod S fun p _ ↦
    continuous_harperTiltedLinearPrimeCharacteristic p.1 t u

theorem continuous_harperBlockGaussianCharacteristic
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    Continuous (fun v ↦
      Complex.exp
        (-((v ^ 2 * harperLinearBlockVariance y S t u / 2 : ℝ) : ℂ))) := by
  fun_prop

/-- The removable-singularity form of the standard Esseen integrand. -/
noncomputable def harperEsseenIntegrand
    (φ ψ : ℝ → ℂ) (t : ℝ) : ℝ :=
  if t = 0 then 0 else ‖φ t - ψ t‖ / |t|

theorem measurable_harperEsseenIntegrand
    {φ ψ : ℝ → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    Measurable (harperEsseenIntegrand φ ψ) := by
  unfold harperEsseenIntegrand
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    ((hφ.sub hψ).norm.div measurable_abs)

theorem harperEsseenIntegrand_nonneg
    (φ ψ : ℝ → ℂ) (t : ℝ) :
    0 ≤ harperEsseenIntegrand φ ψ t := by
  unfold harperEsseenIntegrand
  split_ifs
  · exact le_rfl
  · positivity

/-- A cubic-plus-quartic characteristic estimate loses one power after the
Esseen division by `|t|`. -/
theorem harperEsseenIntegrand_le_of_cubic_quartic
    {φ ψ : ℝ → ℂ} {A B T t : ℝ}
    (ht : |t| ≤ T)
    (hφψ : ‖φ t - ψ t‖ ≤ A * |t| ^ 3 + B * |t| ^ 4) :
    harperEsseenIntegrand φ ψ t ≤ A * |t| ^ 2 + B * |t| ^ 3 := by
  by_cases ht0 : t = 0
  · subst t
    simp [harperEsseenIntegrand]
  · have habs : 0 < |t| := abs_pos.mpr ht0
    rw [harperEsseenIntegrand, if_neg ht0]
    apply (div_le_iff₀ habs).2
    calc
      ‖φ t - ψ t‖ ≤ A * |t| ^ 3 + B * |t| ^ 4 := hφψ
      _ = (A * |t| ^ 2 + B * |t| ^ 3) * |t| := by ring

/-- The low-frequency discrepancy integral over `[-T,T]`. -/
noncomputable def harperEsseenIntegral
    (φ ψ : ℝ → ℂ) (T : ℝ) : ℝ :=
  ∫ t in Icc (-T) T, harperEsseenIntegrand φ ψ t

/-- Conservative explicit integration of a cubic-plus-quartic local
characteristic estimate.  Sharp constants are unnecessary here; the bound
`2T (A T² + B T³)` is deliberately robust. -/
theorem harperEsseenIntegral_le_of_cubic_quartic
    {φ ψ : ℝ → ℂ} {A B T : ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hT : 0 ≤ T)
    (hφψ : ∀ t, |t| ≤ T →
      ‖φ t - ψ t‖ ≤ A * |t| ^ 3 + B * |t| ^ 4) :
    harperEsseenIntegral φ ψ T ≤
      2 * T * (A * T ^ 2 + B * T ^ 3) := by
  let C := A * T ^ 2 + B * T ^ 3
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpoint : ∀ t ∈ Icc (-T) T,
      harperEsseenIntegrand φ ψ t ≤ C := by
    intro t ht
    have habs : |t| ≤ T := by
      rw [abs_le]
      exact ⟨by linarith [ht.1], ht.2⟩
    have hlocal := harperEsseenIntegrand_le_of_cubic_quartic habs
      (hφψ t habs)
    calc
      harperEsseenIntegrand φ ψ t ≤ A * |t| ^ 2 + B * |t| ^ 3 := hlocal
      _ ≤ A * T ^ 2 + B * T ^ 3 := by
        gcongr
  have hmeas : StronglyMeasurable (harperEsseenIntegrand φ ψ) :=
    (measurable_harperEsseenIntegrand hφ.measurable hψ.measurable).stronglyMeasurable
  have hInt : IntegrableOn (harperEsseenIntegrand φ ψ) (Icc (-T) T) := by
    rw [IntegrableOn]
    exact (integrable_const (μ := volume.restrict (Icc (-T) T)) C).mono'
      hmeas.aestronglyMeasurable.restrict
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [Real.norm_eq_abs,
          abs_of_nonneg (harperEsseenIntegrand_nonneg φ ψ t)]
        exact hpoint t ht)
  have hConst : IntegrableOn (fun _ : ℝ ↦ C) (Icc (-T) T) :=
    integrableOn_const (measure_Icc_lt_top.ne)
  have hmono := setIntegral_mono_on hInt hConst measurableSet_Icc hpoint
  unfold harperEsseenIntegral
  calc
    (∫ t in Icc (-T) T, harperEsseenIntegrand φ ψ t) ≤
        ∫ _t in Icc (-T) T, C := hmono
    _ = 2 * T * C := by
      rw [setIntegral_const, smul_eq_mul,
        Real.volume_real_Icc_of_le (by linarith)]
      ring
    _ = 2 * T * (A * T ^ 2 + B * T ^ 3) := rfl

/-! ## Direct interface to the Harper prime block -/

/-- The quartic coefficient obtained by summing the squares of the
one-prime Gaussian quadratic terms. -/
noncomputable def harperBlockGaussianQuarticBudget
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) : ℝ :=
  ∑ p ∈ S, (harperCenteredLinearPrimeVariance p.1 t u / 2) ^ 2

theorem harperBlockGaussianQuarticBudget_nonneg
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u : ℝ) :
    0 ≤ harperBlockGaussianQuarticBudget y S t u := by
  unfold harperBlockGaussianQuarticBudget
  positivity

theorem sum_harperPrimeGaussianQuadratic_sq_eq_quartic
    (y : ℕ) (S : Finset (HarperPrimeIndex y)) (t u v : ℝ) :
    (∑ p ∈ S, harperPrimeGaussianQuadratic p.1 t u v ^ 2) =
      |v| ^ 4 * harperBlockGaussianQuarticBudget y S t u := by
  unfold harperPrimeGaussianQuadratic harperBlockGaussianQuarticBudget
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← sq_abs v]
  ring

/-- Scheduled block characteristic estimate in the exact
cubic-plus-quartic shape consumed by `harperEsseenIntegral`. -/
theorem norm_harperScheduledBlockCharacteristic_sub_gaussian_le_cubic_quartic
    (y j : ℕ) (t u v : ℝ)
    (hsmall : ∀ p ∈ harperScheduledPrimeBlock y j,
      |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1)
    (hquad : ∀ p ∈ harperScheduledPrimeBlock y j,
      harperPrimeGaussianQuadratic p.1 t u v ≤ 1 / 2) :
    ‖harperTiltedLinearPrimeBlockCharacteristic y
          (harperScheduledPrimeBlock y j) t u v -
        Complex.exp
          (-((v ^ 2 * harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t u / 2 : ℝ) : ℂ))‖ ≤
      (16 * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * |v| ^ 3 +
        harperBlockGaussianQuarticBudget y
          (harperScheduledPrimeBlock y j) t u * |v| ^ 4 := by
  have hbase := norm_harperScheduledBlockCharacteristic_sub_gaussian_le
    y j t u v hsmall hquad
  rw [sum_harperPrimeGaussianQuadratic_sq_eq_quartic] at hbase
  nlinarith

/-- Fully checked low-frequency integral bound for a scheduled Harper block.
All remaining hypotheses are the same pointwise small-frequency conditions
already required by the characteristic estimate. -/
theorem harperScheduledBlockEsseenIntegral_le
    (y j : ℕ) (t u T : ℝ)
    (hT : 0 ≤ T)
    (hsmall : ∀ v, |v| ≤ T →
      ∀ p ∈ harperScheduledPrimeBlock y j,
        |v| * (2 * (Real.sqrt (p.1 : ℝ))⁻¹) ≤ 1)
    (hquad : ∀ v, |v| ≤ T →
      ∀ p ∈ harperScheduledPrimeBlock y j,
        harperPrimeGaussianQuadratic p.1 t u v ≤ 1 / 2) :
    harperEsseenIntegral
        (fun v ↦ harperTiltedLinearPrimeBlockCharacteristic y
          (harperScheduledPrimeBlock y j) t u v)
        (fun v ↦ Complex.exp
          (-((v ^ 2 * harperLinearBlockVariance y
            (harperScheduledPrimeBlock y j) t u / 2 : ℝ) : ℂ))) T ≤
      2 * T *
        ((16 * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹) * T ^ 2 +
          harperBlockGaussianQuarticBudget y
            (harperScheduledPrimeBlock y j) t u * T ^ 3) := by
  apply harperEsseenIntegral_le_of_cubic_quartic
    (continuous_harperTiltedLinearPrimeBlockCharacteristic y
      (harperScheduledPrimeBlock y j) t u)
    (continuous_harperBlockGaussianCharacteristic y
      (harperScheduledPrimeBlock y j) t u)
  · positivity
  · exact harperBlockGaussianQuarticBudget_nonneg y
      (harperScheduledPrimeBlock y j) t u
  · exact hT
  · intro v hv
    exact norm_harperScheduledBlockCharacteristic_sub_gaussian_le_cubic_quartic
      y j t u v (hsmall v hv) (hquad v hv)

end Problem520
end Erdos
