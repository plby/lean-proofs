import ErdosProblems.Erdos520.CaichLambda23Integral

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos
namespace Problem520

/-!
# The moving cutoffs in Caich's auxiliary lambda terms

For a test point `x`, smoothing parameter `X`, and real integration variable
`z`, the short prime interval is

`(x / (z * (1 + 1/X)), x / z]`.

This file records the natural floors, their measurability and ordering, and
the rounding-safe effective-PNT estimate.  The floor loss changes the clean
constant `2` in `ShortIntervalPrimes` to `3`; no asymptotic hypothesis is
introduced.
-/

/-- Natural height corresponding to a real summation cutoff. -/
noncomputable def caichLambdaHeight (z : ℝ) : ℕ := ⌊z⌋₊

/-- Upper largest-prime cutoff `floor (x/z)`. -/
noncomputable def caichLambdaUpperCutoff (x : ℕ) (z : ℝ) : ℕ :=
  ⌊(x : ℝ) / z⌋₊

/-- Lower largest-prime cutoff
`floor (x / (z * (1 + 1/X)))`. -/
noncomputable def caichLambdaLowerCutoff (x X : ℕ) (z : ℝ) : ℕ :=
  ⌊(x : ℝ) / (z * (1 + 1 / (X : ℝ)))⌋₊

theorem measurable_caichLambdaHeight : Measurable caichLambdaHeight := by
  exact Nat.measurable_floor

theorem measurable_caichLambdaUpperCutoff (x : ℕ) :
    Measurable (caichLambdaUpperCutoff x) := by
  exact Nat.measurable_floor.comp (measurable_const.div measurable_id)

theorem measurable_caichLambdaLowerCutoff (x X : ℕ) :
    Measurable (caichLambdaLowerCutoff x X) := by
  exact Nat.measurable_floor.comp
    (measurable_const.div
      (measurable_id.mul
        (measurable_const.add (measurable_const.div measurable_const))))

/-- The lower floor never exceeds the upper floor. -/
theorem caichLambdaLowerCutoff_le_upper
    (x X : ℕ) {z : ℝ} (hz : 0 < z) (hX : 1 ≤ X) :
    caichLambdaLowerCutoff x X z ≤ caichLambdaUpperCutoff x z := by
  unfold caichLambdaLowerCutoff caichLambdaUpperCutoff
  apply Nat.floor_mono
  have hXR : (0 : ℝ) < (X : ℝ) := by positivity
  have hfactor : 1 ≤ 1 + 1 / (X : ℝ) := by
    have : 0 ≤ 1 / (X : ℝ) := by positivity
    linarith
  have hden : z ≤ z * (1 + 1 / (X : ℝ)) := by
    nlinarith
  exact div_le_div_of_nonneg_left (by positivity) hz hden

/-- On a real interval above `3`, the natural height is at least `3`. -/
theorem three_le_caichLambdaHeight {z : ℝ} (hz : 3 ≤ z) :
    3 ≤ caichLambdaHeight z := by
  unfold caichLambdaHeight
  exact Nat.le_floor (by exact_mod_cast hz)

theorem caichLambdaHeight_cast_le {z : ℝ} (hz : 0 ≤ z) :
    (caichLambdaHeight z : ℝ) ≤ z := by
  exact Nat.floor_le hz

/-- The logarithm of the natural height is at most the logarithm of any
ambient real endpoint. -/
theorem log_caichLambdaHeight_le_log
    {z x : ℝ} (hz : 1 ≤ z) (hzx : z ≤ x) :
    Real.log (caichLambdaHeight z : ℝ) ≤ Real.log x := by
  have hfloorPos : (0 : ℝ) < (caichLambdaHeight z : ℝ) := by
    have : 1 ≤ caichLambdaHeight z := by
      unfold caichLambdaHeight
      exact Nat.le_floor (by simpa using! hz)
    positivity
  apply Real.log_le_log hfloorPos
  exact (caichLambdaHeight_cast_le (zero_le_one.trans hz)).trans hzx

/-! ## Rounding-safe width estimate -/

/-- Abstract floor-width calculation.  If `u = t/(1+1/X)` and the lower
floor is at least `2X`, then rounding enlarges the interval by at most a
factor two: `floor t - floor u ≤ 2 floor u / X`. -/
theorem natFloor_sub_le_two_mul_floor_div
    {t u : ℝ} {X : ℕ} (hX : 2 ≤ X)
    (hu : 0 ≤ u) (hut : u ≤ t)
    (hrelation : (X : ℝ) * t = ((X : ℝ) + 1) * u)
    (hlarge : 2 * X ≤ ⌊u⌋₊) :
    ((⌊t⌋₊ : ℕ) : ℝ) - ((⌊u⌋₊ : ℕ) : ℝ) ≤
      2 * ((⌊u⌋₊ : ℕ) : ℝ) / (X : ℝ) := by
  let a : ℕ := ⌊u⌋₊
  let b : ℕ := ⌊t⌋₊
  have ht : 0 ≤ t := hu.trans hut
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact Nat.floor_mono hut
  have hb : (b : ℝ) ≤ t := by
    dsimp only [b]
    exact Nat.floor_le ht
  have hua : u < (a : ℝ) + 1 := by
    dsimp only [a]
    simpa only [Nat.cast_add, Nat.cast_one] using! Nat.lt_floor_add_one u
  have hXa : (X : ℝ) + 1 ≤ (a : ℝ) := by
    have hlargeR : 2 * (X : ℝ) ≤ (a : ℝ) := by exact_mod_cast hlarge
    have hXone : (X : ℝ) + 1 ≤ 2 * X := by
      have : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
      linarith
    exact hXone.trans hlargeR
  have hscaled : (X : ℝ) * ((b : ℝ) - (a : ℝ)) ≤
      2 * (a : ℝ) := by
    have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
    calc
      (X : ℝ) * ((b : ℝ) - (a : ℝ)) ≤
          (X : ℝ) * (t - (a : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hb _) hXpos.le
      _ = ((X : ℝ) + 1) * u - (X : ℝ) * (a : ℝ) := by
        rw [mul_sub, hrelation]
      _ ≤ ((X : ℝ) + 1) * ((a : ℝ) + 1) -
          (X : ℝ) * (a : ℝ) := by
        exact sub_le_sub_right
          (mul_le_mul_of_nonneg_left hua.le (by positivity)) _
      _ = (a : ℝ) + (X : ℝ) + 1 := by ring
      _ ≤ 2 * (a : ℝ) := by linarith
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < (X : ℝ))).2 (by
    simpa only [mul_comm] using! hscaled)

/-- The actual Caich floors satisfy the rounding-safe relative-width bound. -/
theorem caichLambdaCutoff_width_le
    (x X : ℕ) {z : ℝ} (hz : 0 < z) (hX : 2 ≤ X)
    (hlarge : 2 * X ≤ caichLambdaLowerCutoff x X z) :
    ((caichLambdaUpperCutoff x z : ℝ) -
        (caichLambdaLowerCutoff x X z : ℝ)) ≤
      2 * (caichLambdaLowerCutoff x X z : ℝ) / (X : ℝ) := by
  let t : ℝ := (x : ℝ) / z
  let u : ℝ := (x : ℝ) / (z * (1 + 1 / (X : ℝ)))
  have hXR : (0 : ℝ) < (X : ℝ) := by positivity
  have hfactor : 0 < 1 + 1 / (X : ℝ) := by positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hut : u ≤ t := by
    dsimp only [u, t]
    have hden : z ≤ z * (1 + 1 / (X : ℝ)) := by
      have : (1 : ℝ) ≤ 1 + 1 / (X : ℝ) := by
        have : 0 ≤ 1 / (X : ℝ) := by positivity
        linarith
      nlinarith
    exact div_le_div_of_nonneg_left (by positivity) hz hden
  have hrelation : (X : ℝ) * t = ((X : ℝ) + 1) * u := by
    dsimp only [t, u]
    field_simp
  simpa only [caichLambdaUpperCutoff, caichLambdaLowerCutoff, t, u] using!
    natFloor_sub_le_two_mul_floor_div hX hu hut hrelation hlarge

/-! ## Effective PNT with the floor loss -/

/-- Version of the short-prime estimate allowing relative width `2/X`.
The extra unit of constant is exactly the harmless floor loss. -/
theorem freshReciprocalSum_le_three_div_X_log_of_effectivePNT
    {C c : ℝ} {N X y a b : ℕ}
    (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hPNT : EffectivePrimeCountingError C c N)
    (hNa : N ≤ a) (ha : 2 ≤ a) (hab : a ≤ b)
    (hX : 2 ≤ X) (hy : 2 ≤ y) (hya : y ≤ a)
    (hwidth : ((b : ℝ) - (a : ℝ)) ≤ 2 * (a : ℝ) / (X : ℝ))
    (hdom : 3 * C * (X : ℝ) * Real.log (y : ℝ) ≤
      Real.exp (c * Real.sqrt (Real.log (a : ℝ)))) :
    freshReciprocalSum a b ≤
      3 / ((X : ℝ) * Real.log (y : ℝ)) := by
  have haPos : 0 < (a : ℝ) := by positivity
  have hXR : 0 < (X : ℝ) := by positivity
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogA : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogMono : Real.log (y : ℝ) ≤ Real.log (a : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hya)
  have hwidthA : 2 * (a : ℝ) / (X : ℝ) ≤ (a : ℝ) := by
    apply (div_le_iff₀ hXR).2
    have hXRtwo : (2 : ℝ) ≤ X := by exact_mod_cast hX
    nlinarith
  have hbaR : (b : ℝ) ≤ 2 * (a : ℝ) := by linarith
  have hba : b ≤ 2 * a := by exact_mod_cast hbaR
  have hmain :
      ((b : ℝ) - (a : ℝ)) /
          ((a : ℝ) * Real.log (a : ℝ)) ≤
        2 / ((X : ℝ) * Real.log (y : ℝ)) := by
    calc
      ((b : ℝ) - (a : ℝ)) /
          ((a : ℝ) * Real.log (a : ℝ)) ≤
          (2 * (a : ℝ) / (X : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) := by gcongr
      _ = 2 / ((X : ℝ) * Real.log (a : ℝ)) := by field_simp
      _ ≤ 2 / ((X : ℝ) * Real.log (y : ℝ)) := by
        exact div_le_div_of_nonneg_left (by norm_num)
          (mul_pos hXR hlogY)
          (mul_le_mul_of_nonneg_left hlogMono hXR.le)
  have herr := effectivePrimeCountingError_le_reciprocalScale
    (show 1 ≤ X by omega) hy hdom
  calc
    freshReciprocalSum a b ≤
        ((b : ℝ) - (a : ℝ)) /
            ((a : ℝ) * Real.log (a : ℝ)) +
          3 * C * Real.exp (-c * Real.sqrt (Real.log (a : ℝ))) :=
      freshReciprocalSum_le_of_effectivePrimeCountingError
        hC hc hPNT hNa ha hab hba
    _ ≤ 2 / ((X : ℝ) * Real.log (y : ℝ)) +
          1 / ((X : ℝ) * Real.log (y : ℝ)) := add_le_add hmain herr
    _ = 3 / ((X : ℝ) * Real.log (y : ℝ)) := by ring

/-- Eventual floor-safe reciprocal-prime estimate, uniformly over all
cutoffs in the Caich regime. -/
theorem eventually_caichLambdaCutoff_reciprocal_le_of_effectiveStatement
    (hPNT : EffectivePrimeCountingStatement) (A : ℕ) :
    ∀ᶠ y : ℕ in atTop, ∀ {x X : ℕ} {z : ℝ},
      0 < z → 2 ≤ X →
      y ≤ caichLambdaLowerCutoff x X z →
      (X : ℝ) ≤ Real.log (y : ℝ) ^ A →
      2 * X ≤ caichLambdaLowerCutoff x X z →
      freshReciprocalSum (caichLambdaLowerCutoff x X z)
          (caichLambdaUpperCutoff x z) ≤
        3 / ((X : ℝ) * Real.log (y : ℝ)) := by
  obtain ⟨C, hC, c, hc, N, hN, herror⟩ := hPNT
  have hdom := eventually_effectivePNT_error_dominated_polylog hC.le hc A
  filter_upwards [hdom, eventually_ge_atTop (max N 2)] with
    y hdomY hy x X z hz hX hya hXpoly hlarge
  let a := caichLambdaLowerCutoff x X z
  let b := caichLambdaUpperCutoff x z
  have hya' : y ≤ a := by simpa only [a] using! hya
  have hNa : N ≤ a := ((le_max_left N 2).trans hy).trans hya'
  have ha : 2 ≤ a := ((le_max_right N 2).trans hy).trans hya'
  have hab : a ≤ b := by
    exact caichLambdaLowerCutoff_le_upper x X hz (by omega)
  have hwidth : ((b : ℝ) - (a : ℝ)) ≤
      2 * (a : ℝ) / (X : ℝ) := by
    exact caichLambdaCutoff_width_le x X hz hX hlarge
  exact freshReciprocalSum_le_three_div_X_log_of_effectivePNT
    hC.le hc.le herror hNa ha hab hX (by omega) hya' hwidth
      (hdomY (by omega) hya' hXpoly)

/-! ## Compact-interval integrability -/

/-- The inverse-square weighted kernel, its square after integration in
`z`, and its section `L²` norm are automatically integrable on every
positive compact interval.  The uniform bound is the exact cancellation
`z⁻² (2 floor(z))² ≤ 4`. -/
theorem caichLambdaKernel_compact_integrability
    {H : ℝ → Omega → ℝ}
    (hHmeas : Measurable (fun p : ℝ × Omega ↦ H p.1 p.2))
    (hHnonneg : ∀ z omega, 0 ≤ H z omega)
    (hHbound : ∀ z omega, H z omega ≤
      (2 * (caichLambdaHeight z : ℝ)) ^ 2)
    (hslice : ∀ z, Integrable (fun omega ↦ H z omega ^ 2) μ)
    {a b : ℝ} (ha : 0 < a) :
    (∀ omega, IntegrableOn (fun z : ℝ ↦ (z ^ 2)⁻¹ * H z omega) (Ioc a b)) ∧
    Integrable (fun omega ↦
      (∫ z in Ioc a b, (z ^ 2)⁻¹ * H z omega) ^ 2) μ ∧
    IntegrableOn (fun z : ℝ ↦ (z ^ 2)⁻¹ *
      (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ))) (Ioc a b) := by
  have hpoint : ∀ z ∈ Ioc a b, ∀ omega,
      ‖(z ^ 2)⁻¹ * H z omega‖ ≤ 4 := by
    intro z hz omega
    have hzpos : 0 < z := ha.trans hz.1
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (by positivity) (hHnonneg z omega))]
    calc
      (z ^ 2)⁻¹ * H z omega ≤
          (z ^ 2)⁻¹ * (2 * (caichLambdaHeight z : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left (hHbound z omega) (by positivity)
      _ ≤ (z ^ 2)⁻¹ * (2 * z) ^ 2 := by
        gcongr
        exact caichLambdaHeight_cast_le hzpos.le
      _ = 4 := by field_simp; norm_num
  have hinner : ∀ omega,
      IntegrableOn (fun z : ℝ ↦ (z ^ 2)⁻¹ * H z omega) (Ioc a b) := by
    intro omega
    apply IntegrableOn.of_bound measure_Ioc_lt_top
      (((by fun_prop : Measurable fun z : ℝ ↦ (z ^ 2)⁻¹).mul
        (hHmeas.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable) 4
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact hpoint z hz omega
  have hjoint : Measurable (fun p : ℝ × Omega ↦
      (p.1 ^ 2)⁻¹ * H p.1 p.2) :=
    ((by fun_prop : Measurable fun p : ℝ × Omega ↦ (p.1 ^ 2)⁻¹).mul hHmeas)
  have houterSM : StronglyMeasurable (fun omega ↦
      ∫ z in Ioc a b, (z ^ 2)⁻¹ * H z omega) := by
    exact (hjoint.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc a b))
  have houter : Integrable (fun omega ↦
      (∫ z in Ioc a b, (z ^ 2)⁻¹ * H z omega) ^ 2) μ := by
    apply Integrable.of_bound (houterSM.pow 2).aestronglyMeasurable
      ((4 * volume.real (Ioc a b)) ^ 2)
    exact ae_of_all μ fun omega ↦ by
      simp only [Pi.pow_apply, norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top
          (fun z hz ↦ hpoint z hz omega)) 2
  have hrootMeas : Measurable (fun z ↦
      (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ))) := by
    exact ((hHmeas.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.pow_const _
  have hrootBound : ∀ z ∈ Ioc a b,
      (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ)) ≤ (2 * z) ^ 2 := by
    intro z hz
    have hzpos : 0 < z := ha.trans hz.1
    have hHz : ∀ omega, H z omega ≤ (2 * z) ^ 2 := by
      intro omega
      exact (hHbound z omega).trans (by
        gcongr
        exact caichLambdaHeight_cast_le hzpos.le)
    have hInt : (∫ omega, H z omega ^ 2 ∂μ) ≤ (2 * z) ^ 4 := by
      calc
        (∫ omega, H z omega ^ 2 ∂μ) ≤
            ∫ _omega : Omega, (2 * z) ^ 4 ∂μ := by
          apply integral_mono (hslice z) (integrable_const _)
          intro omega
          calc
            H z omega ^ 2 ≤ ((2 * z) ^ 2) ^ 2 :=
              pow_le_pow_left₀ (hHnonneg z omega) (hHz omega) 2
            _ = (2 * z) ^ 4 := by ring
        _ = (2 * z) ^ 4 := by simp
    rw [← Real.sqrt_eq_rpow]
    calc
      √(∫ omega, H z omega ^ 2 ∂μ) ≤ √((2 * z) ^ 4) :=
        Real.sqrt_le_sqrt hInt
      _ = (2 * z) ^ 2 := by
        rw [show (2 * z) ^ 4 = ((2 * z) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (sq_nonneg _)]
  have hrhs : IntegrableOn (fun z : ℝ ↦ (z ^ 2)⁻¹ *
      (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ))) (Ioc a b) := by
    apply IntegrableOn.of_bound measure_Ioc_lt_top
      (((by fun_prop : Measurable fun z : ℝ ↦ (z ^ 2)⁻¹).mul
        hrootMeas).aestronglyMeasurable) 4
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hzpos : 0 < z := ha.trans hz.1
    change ‖(z ^ 2)⁻¹ * (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ))‖ ≤ 4
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg (integral_nonneg fun omega ↦ sq_nonneg _) _))]
    calc
      (z ^ 2)⁻¹ * (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ)) ≤
          (z ^ 2)⁻¹ * (2 * z) ^ 2 :=
        mul_le_mul_of_nonneg_left (hrootBound z hz) (by positivity)
      _ = 4 := by field_simp; norm_num
  exact ⟨hinner, houter, hrhs⟩

/-- A measurable nonnegative function with linear growth is integrable
after inverse-square weighting on every positive compact interval. -/
theorem integrableOn_inv_sq_mul_of_nonneg_le_linear
    {B : ℝ → ℝ} (hBmeas : Measurable B)
    (hBnonneg : ∀ z, 0 ≤ B z) {a b D : ℝ} (ha : 0 < a)
    (hlinear : ∀ z ∈ Ioc a b, B z ≤ D * z) :
    IntegrableOn (fun z : ℝ ↦ (z ^ 2)⁻¹ * B z) (Ioc a b) := by
  apply IntegrableOn.of_bound measure_Ioc_lt_top
    (((by fun_prop : Measurable fun z : ℝ ↦ (z ^ 2)⁻¹).mul
      hBmeas).aestronglyMeasurable) (|D| / a)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hzpos : 0 < z := ha.trans hz.1
  change ‖(z ^ 2)⁻¹ * B z‖ ≤ |D| / a
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (by positivity) (hBnonneg z))]
  calc
    (z ^ 2)⁻¹ * B z ≤ (z ^ 2)⁻¹ * (D * z) :=
      mul_le_mul_of_nonneg_left (hlinear z hz) (by positivity)
    _ = D / z := by field_simp
    _ ≤ |D| / z := by
      exact div_le_div_of_nonneg_right (le_abs_self D) hzpos.le
    _ ≤ |D| / a := by
      exact div_le_div_of_nonneg_left (abs_nonneg D) ha hz.1.le

/-- Measurability of the concrete deterministic terminal root budget. -/
theorem measurable_caichLambdaTerminalRootBudget (x X : ℕ) :
    Measurable (fun z : ℝ ↦ caichLambdaTerminalRootBudget
      caichLambdaHeight (caichLambdaLowerCutoff x X)
      (caichLambdaUpperCutoff x) z) := by
  have hrecipBase : Measurable (fun q : ℕ × ℕ ↦
      freshReciprocalSum q.1 q.2) := measurable_of_countable _
  have hrecip : Measurable (fun z : ℝ ↦
      freshReciprocalSum (caichLambdaLowerCutoff x X z)
        (caichLambdaUpperCutoff x z)) :=
    hrecipBase.comp ((measurable_caichLambdaLowerCutoff x X).prodMk
      (measurable_caichLambdaUpperCutoff x))
  have hheight : Measurable (fun z : ℝ ↦ (caichLambdaHeight z : ℝ)) := by
    exact (MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
      measurable_caichLambdaHeight
  exact (((measurable_const.mul hheight).mul
    ((measurable_const.mul
      (Real.measurable_log.comp hheight)).pow_const 2)).mul hrecip)

/-! ## Concrete block integrals -/

/-- The real `z` interval attached to a prime block `(yPrev,y]`. -/
def caichLambdaInterval (x yPrev y : ℕ) : Set ℝ :=
  Set.Ioc ((x : ℝ) / (y : ℝ)) ((x : ℝ) / (yPrev : ℝ))

/-- Caich's `lambda^(2)` majorant on one test point and one prime block.
The inclusive largest-prime path dominates the source's strict intermediate
cutoff and has the same terminal value. -/
noncomputable def caichLambda2Block
    (x X yPrev y : ℕ) (omega : Omega) : ℝ :=
  caichLambdaWeighted
    (volume.restrict (caichLambdaInterval x yPrev y))
    (Real.log (y : ℝ))⁻¹ (fun z : ℝ ↦ (z ^ 2)⁻¹)
    (caichLambda2Kernel caichLambdaHeight
      (caichLambdaLowerCutoff x X) (caichLambdaUpperCutoff x)) omega

/-- Caich's `lambda^(3)` on one test point and one prime block. -/
noncomputable def caichLambda3Block
    (x X yPrev y : ℕ) (omega : Omega) : ℝ :=
  caichLambdaWeighted
    (volume.restrict (caichLambdaInterval x yPrev y))
    (Real.log (y : ℝ))⁻¹ (fun z : ℝ ↦ (z ^ 2)⁻¹)
    (caichLambda3Kernel caichLambdaHeight
      (caichLambdaLowerCutoff x X) (caichLambdaUpperCutoff x)) omega

theorem caichLambda2Block_nonneg
    (x X yPrev y : ℕ) (hy : 1 ≤ y) (omega : Omega) :
    0 ≤ caichLambda2Block x X yPrev y omega := by
  unfold caichLambda2Block caichLambdaWeighted
  apply mul_nonneg
  · exact inv_nonneg.mpr
      (Real.log_nonneg (by exact_mod_cast hy))
  · exact integral_nonneg fun z ↦ mul_nonneg (by positivity)
      (caichLambda2Kernel_nonneg _ _ _ _ _)

theorem caichLambda3Block_nonneg
    (x X yPrev y : ℕ) (hy : 1 ≤ y) (omega : Omega) :
    0 ≤ caichLambda3Block x X yPrev y omega := by
  unfold caichLambda3Block caichLambdaWeighted
  apply mul_nonneg
  · exact inv_nonneg.mpr
      (Real.log_nonneg (by exact_mod_cast hy))
  · exact integral_nonneg fun z ↦ mul_nonneg (by positivity)
      (caichLambda3Kernel_nonneg _ _ _ _ _)

/-- Fully assembled outer-integral estimate for one `lambda^(2)` block. -/
theorem caichLambda2Block_secondMoment_sqrt_le
    {x X yPrev y : ℕ} {L R : ℝ}
    (hX : 1 ≤ X) (hy : 2 ≤ y)
    (hleft : 3 ≤ (x : ℝ) / (y : ℝ))
    (hinterval : (x : ℝ) / (y : ℝ) ≤
      (x : ℝ) / (yPrev : ℝ))
    (hlog : ∀ z ∈ caichLambdaInterval x yPrev y,
      Real.log (caichLambdaHeight z : ℝ) ≤ L)
    (hrecip : ∀ z ∈ caichLambdaInterval x yPrev y,
      freshReciprocalSum (caichLambdaLowerCutoff x X z)
        (caichLambdaUpperCutoff x z) ≤ R) :
    (∫ omega, caichLambda2Block x X yPrev y omega ^ 2 ∂μ) ^
        (1 / (2 : ℝ)) ≤
      (Real.log (y : ℝ))⁻¹ *
        (6 * (2 * L) ^ 2 * R *
          Real.log (((x : ℝ) / (yPrev : ℝ)) /
            ((x : ℝ) / (y : ℝ)))) := by
  let s := caichLambdaInterval x yPrev y
  let H := caichLambda2Kernel caichLambdaHeight
    (caichLambdaLowerCutoff x X) (caichLambdaUpperCutoff x)
  let B : ℝ → ℝ := fun z ↦
    2 * caichLambdaTerminalRootBudget caichLambdaHeight
      (caichLambdaLowerCutoff x X) (caichLambdaUpperCutoff x) z
  have hHmeas : Measurable (fun p : ℝ × Omega ↦ H p.1 p.2) := by
    exact measurable_caichLambda2Kernel measurable_caichLambdaHeight
      (measurable_caichLambdaLowerCutoff x X)
      (measurable_caichLambdaUpperCutoff x)
  have ha : 0 < (x : ℝ) / (y : ℝ) := by linarith
  have hslice : ∀ z, Integrable (fun omega ↦ H z omega ^ 2) μ :=
    fun z ↦ integrable_sq_caichLambda2Kernel measurable_caichLambdaHeight
      (measurable_caichLambdaLowerCutoff x X)
      (measurable_caichLambdaUpperCutoff x) z
  obtain ⟨hinner, houter, hrhs⟩ :=
    caichLambdaKernel_compact_integrability (H := H) hHmeas
      (fun z omega ↦ caichLambda2Kernel_nonneg _ _ _ z omega)
      (fun z omega ↦ caichLambda2Kernel_le_height _ _ _ z omega)
      hslice (a := (x : ℝ) / (y : ℝ))
        (b := (x : ℝ) / (yPrev : ℝ)) ha
  have hc : 0 ≤ (Real.log (y : ℝ))⁻¹ :=
    inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))
  have hsection : ∀ᵐ z ∂(volume.restrict s),
      (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ)) ≤ B z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hzpos : 0 < z := lt_trans (by norm_num : (0 : ℝ) < 3)
      (hleft.trans_lt hz.1)
    exact caichLambda2Kernel_secondMoment_sqrt_le _ _ _ z
      (three_le_caichLambdaHeight (hleft.trans hz.1.le))
      (caichLambdaLowerCutoff_le_upper x X hzpos hX)
  have hlinearB : ∀ z ∈ s, B z ≤ (6 * (2 * L) ^ 2 * R) * z := by
    intro z hz
    have hznonneg : 0 ≤ z := (by
      have := hleft.trans_lt hz.1
      positivity)
    have hroot := caichLambdaTerminalRootBudget_le_linear
      caichLambdaHeight (caichLambdaLowerCutoff x X)
      (caichLambdaUpperCutoff x) (fun z : ℝ ↦ z) z
      (caichLambdaHeight_cast_le hznonneg) hznonneg (hlog z hz) (hrecip z hz)
    dsimp only [B]
    nlinarith
  have hBmeas : Measurable B := by
    dsimp only [B]
    exact measurable_const.mul (measurable_caichLambdaTerminalRootBudget x X)
  have hBnonneg : ∀ z, 0 ≤ B z := by
    intro z
    exact mul_nonneg (by norm_num)
      (caichLambdaTerminalRootBudget_nonneg _ _ _ z)
  have hBint : IntegrableOn (fun z : ℝ ↦ (z ^ 2)⁻¹ * B z) s := by
    exact integrableOn_inv_sq_mul_of_nonneg_le_linear hBmeas hBnonneg
      (a := (x : ℝ) / (y : ℝ))
      (b := (x : ℝ) / (yPrev : ℝ))
      (D := 6 * (2 * L) ^ 2 * R) ha hlinearB
  have hmain := caichLambdaWeighted_secondMoment_sqrt_le_budget
    hHmeas (by fun_prop : Measurable fun z : ℝ ↦ (z ^ 2)⁻¹)
    (caichLambda2Kernel_nonneg _ _ _)
    (fun z ↦ by positivity) hc hinner houter hslice hrhs hBint hsection
  have hint := setIntegral_inv_sq_mul_le_mul_log_div
    (a := (x : ℝ) / (y : ℝ))
    (b := (x : ℝ) / (yPrev : ℝ))
    (D := 6 * (2 * L) ^ 2 * R)
    (by linarith) hinterval hBint hlinearB
  unfold caichLambda2Block
  simpa only [s, H, B, caichLambdaInterval] using!
    hmain.trans (mul_le_mul_of_nonneg_left hint hc)

/-- Fully assembled outer-integral estimate for one `lambda^(3)` block. -/
theorem caichLambda3Block_secondMoment_sqrt_le
    {x X yPrev y : ℕ} {L R : ℝ}
    (hX : 1 ≤ X) (hy : 2 ≤ y)
    (hleft : 3 ≤ (x : ℝ) / (y : ℝ))
    (hinterval : (x : ℝ) / (y : ℝ) ≤
      (x : ℝ) / (yPrev : ℝ))
    (hlog : ∀ z ∈ caichLambdaInterval x yPrev y,
      Real.log (caichLambdaHeight z : ℝ) ≤ L)
    (hrecip : ∀ z ∈ caichLambdaInterval x yPrev y,
      freshReciprocalSum (caichLambdaLowerCutoff x X z)
        (caichLambdaUpperCutoff x z) ≤ R) :
    (∫ omega, caichLambda3Block x X yPrev y omega ^ 2 ∂μ) ^
        (1 / (2 : ℝ)) ≤
      (Real.log (y : ℝ))⁻¹ *
        (3 * (2 * L) ^ 2 * R *
          Real.log (((x : ℝ) / (yPrev : ℝ)) /
            ((x : ℝ) / (y : ℝ)))) := by
  let s := caichLambdaInterval x yPrev y
  let H := caichLambda3Kernel caichLambdaHeight
    (caichLambdaLowerCutoff x X) (caichLambdaUpperCutoff x)
  let B : ℝ → ℝ := fun z ↦
    caichLambdaTerminalRootBudget caichLambdaHeight
      (caichLambdaLowerCutoff x X) (caichLambdaUpperCutoff x) z
  have hHmeas : Measurable (fun p : ℝ × Omega ↦ H p.1 p.2) := by
    exact measurable_caichLambda3Kernel measurable_caichLambdaHeight
      (measurable_caichLambdaLowerCutoff x X)
      (measurable_caichLambdaUpperCutoff x)
  have ha : 0 < (x : ℝ) / (y : ℝ) := by linarith
  have hslice : ∀ z, Integrable (fun omega ↦ H z omega ^ 2) μ :=
    fun z ↦ integrable_sq_caichLambda3Kernel measurable_caichLambdaHeight
      (measurable_caichLambdaLowerCutoff x X)
      (measurable_caichLambdaUpperCutoff x) z
  obtain ⟨hinner, houter, hrhs⟩ :=
    caichLambdaKernel_compact_integrability (H := H) hHmeas
      (fun z omega ↦ caichLambda3Kernel_nonneg _ _ _ z omega)
      (fun z omega ↦ caichLambda3Kernel_le_height _ _ _ z omega)
      hslice (a := (x : ℝ) / (y : ℝ))
        (b := (x : ℝ) / (yPrev : ℝ)) ha
  have hc : 0 ≤ (Real.log (y : ℝ))⁻¹ :=
    inv_nonneg.mpr (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega)))
  have hsection : ∀ᵐ z ∂(volume.restrict s),
      (∫ omega, H z omega ^ 2 ∂μ) ^ (1 / (2 : ℝ)) ≤ B z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hzpos : 0 < z := lt_trans (by norm_num : (0 : ℝ) < 3)
      (hleft.trans_lt hz.1)
    exact caichLambda3Kernel_secondMoment_sqrt_le _ _ _ z
      (three_le_caichLambdaHeight (hleft.trans hz.1.le))
      (caichLambdaLowerCutoff_le_upper x X hzpos hX)
  have hlinearB : ∀ z ∈ s, B z ≤ (3 * (2 * L) ^ 2 * R) * z := by
    intro z hz
    have hznonneg : 0 ≤ z := (by
      have := hleft.trans_lt hz.1
      positivity)
    have hroot := caichLambdaTerminalRootBudget_le_linear
        caichLambdaHeight (caichLambdaLowerCutoff x X)
        (caichLambdaUpperCutoff x) (fun z : ℝ ↦ z) z
        (caichLambdaHeight_cast_le hznonneg) hznonneg (hlog z hz) (hrecip z hz)
    dsimp only [B]
    calc
      caichLambdaTerminalRootBudget caichLambdaHeight
          (caichLambdaLowerCutoff x X) (caichLambdaUpperCutoff x) z ≤
          3 * z * (2 * L) ^ 2 * R := hroot
      _ = (3 * (2 * L) ^ 2 * R) * z := by ring
  have hBmeas : Measurable B := by
    dsimp only [B]
    exact measurable_caichLambdaTerminalRootBudget x X
  have hBnonneg : ∀ z, 0 ≤ B z := by
    intro z
    exact caichLambdaTerminalRootBudget_nonneg _ _ _ z
  have hBint : IntegrableOn (fun z : ℝ ↦ (z ^ 2)⁻¹ * B z) s := by
    exact integrableOn_inv_sq_mul_of_nonneg_le_linear hBmeas hBnonneg
      (a := (x : ℝ) / (y : ℝ))
      (b := (x : ℝ) / (yPrev : ℝ))
      (D := 3 * (2 * L) ^ 2 * R) ha hlinearB
  have hmain := caichLambdaWeighted_secondMoment_sqrt_le_budget
    hHmeas (by fun_prop : Measurable fun z : ℝ ↦ (z ^ 2)⁻¹)
    (caichLambda3Kernel_nonneg _ _ _)
    (fun z ↦ by positivity) hc hinner houter hslice hrhs hBint hsection
  have hint := setIntegral_inv_sq_mul_le_mul_log_div
    (a := (x : ℝ) / (y : ℝ))
    (b := (x : ℝ) / (yPrev : ℝ))
    (D := 3 * (2 * L) ^ 2 * R)
    (by linarith) hinterval hBint hlinearB
  unfold caichLambda3Block
  simpa only [s, H, B, caichLambdaInterval] using!
    hmain.trans (mul_le_mul_of_nonneg_left hint hc)

end Problem520
end Erdos
