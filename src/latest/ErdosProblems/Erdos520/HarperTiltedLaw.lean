import ErdosProblems.Erdos520.HarperEulerProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# The finite tilted Rademacher product law

At a fixed height `t`, Harper tilts the fair Rademacher law by the squared
Euler product.  Since the product contains only finitely many prime
coordinates, the tilted law is again an explicit product law: the coin at
`p` has mass proportional to the one-prime squared Euler factor.

This file constructs that finite product measure and proves its exact
change-of-measure identity.  No asymptotic or prime-number input is used.
-/

/-- The squared Euler factor evaluated at a single Boolean sign. -/
noncomputable def harperCoordinateFactor (p : ℕ) (t : ℝ) (b : Bool) : ℝ :=
  harperEulerFactor (fun _ ↦ b) p t

theorem harperCoordinateFactor_nonneg (p : ℕ) (t : ℝ) (b : Bool) :
    0 ≤ harperCoordinateFactor p t b :=
  harperEulerFactor_nonneg (fun _ ↦ b) p t

/-- Averaging the two signs gives the exact one-prime normalizer. -/
theorem harperCoordinateFactor_false_add_true (p : ℕ) (t : ℝ) :
    harperCoordinateFactor p t false + harperCoordinateFactor p t true =
      2 * (1 + (p : ℝ)⁻¹) := by
  by_cases hp : p = 0
  · subst p
    norm_num [harperCoordinateFactor, harperEulerFactor, ε]
  · have hp0 : 0 < p := Nat.pos_of_ne_zero hp
    rw [harperCoordinateFactor, harperCoordinateFactor,
      harperEulerFactor_eq (fun _ ↦ false) hp0,
      harperEulerFactor_eq (fun _ ↦ true) hp0]
    simp [ε]
    ring

/-- The tilted mass of one Boolean sign at the prime `p`. -/
noncomputable def harperTiltedCoinWeight (p : ℕ) (t : ℝ) (b : Bool) : ℝ :=
  harperCoordinateFactor p t b / (2 * (1 + (p : ℝ)⁻¹))

theorem harperTiltedCoinWeight_nonneg (p : ℕ) (t : ℝ) (b : Bool) :
    0 ≤ harperTiltedCoinWeight p t b := by
  unfold harperTiltedCoinWeight
  exact div_nonneg (harperCoordinateFactor_nonneg p t b) (by positivity)

theorem harperTiltedCoinWeight_false_add_true (p : ℕ) (t : ℝ) :
    harperTiltedCoinWeight p t false + harperTiltedCoinWeight p t true = 1 := by
  unfold harperTiltedCoinWeight
  rw [← add_div, harperCoordinateFactor_false_add_true]
  field_simp

/-- The tilted mass as a nonnegative real, for use as a measure scalar. -/
noncomputable def harperTiltedCoinWeightNNReal
    (p : ℕ) (t : ℝ) (b : Bool) : ℝ≥0 :=
  ⟨harperTiltedCoinWeight p t b, harperTiltedCoinWeight_nonneg p t b⟩

@[simp] theorem coe_harperTiltedCoinWeightNNReal
    (p : ℕ) (t : ℝ) (b : Bool) :
    (harperTiltedCoinWeightNNReal p t b : ℝ) =
      harperTiltedCoinWeight p t b := rfl

theorem harperTiltedCoinWeightNNReal_false_add_true (p : ℕ) (t : ℝ) :
    harperTiltedCoinWeightNNReal p t false +
        harperTiltedCoinWeightNNReal p t true = 1 := by
  ext
  exact harperTiltedCoinWeight_false_add_true p t

/-- The normalized one-coordinate law obtained by tilting a fair sign by its
squared Euler factor. -/
noncomputable def harperTiltedCoin (p : ℕ) (t : ℝ) : Measure Bool :=
  (harperTiltedCoinWeightNNReal p t false : ℝ≥0∞) • Measure.dirac false +
    (harperTiltedCoinWeightNNReal p t true : ℝ≥0∞) • Measure.dirac true

instance harperTiltedCoin_isProbabilityMeasure (p : ℕ) (t : ℝ) :
    IsProbabilityMeasure (harperTiltedCoin p t) where
  measure_univ := by
    simp [harperTiltedCoin]
    rw [← ENNReal.coe_add, harperTiltedCoinWeightNNReal_false_add_true]
    simp

@[simp] theorem harperTiltedCoin_apply_singleton
    (p : ℕ) (t : ℝ) (b : Bool) :
    harperTiltedCoin p t {b} =
      (harperTiltedCoinWeightNNReal p t b : ℝ≥0∞) := by
  cases b <;> simp [harperTiltedCoin] <;>
    rw [ENNReal.smul_def, smul_eq_mul, mul_one]

@[simp] theorem harperTiltedCoin_real_singleton
    (p : ℕ) (t : ℝ) (b : Bool) :
    (harperTiltedCoin p t).real {b} =
      harperTiltedCoinWeight p t b := by
  rw [Measure.real, harperTiltedCoin_apply_singleton]
  simp

/-- Expectation under one tilted coin is the explicitly biased two-point
average. -/
theorem integral_harperTiltedCoin (p : ℕ) (t : ℝ) (g : Bool → ℝ) :
    (∫ b, g b ∂harperTiltedCoin p t) =
      harperTiltedCoinWeight p t false * g false +
        harperTiltedCoinWeight p t true * g true := by
  rw [integral_fintype (Integrable.of_finite :
    Integrable g (harperTiltedCoin p t))]
  simp [smul_eq_mul]
  ring

theorem integral_coin_bool (g : Bool → ℝ) :
    (∫ b, g b ∂coin) = (g false + g true) / 2 := by
  have hgfalse : Integrable g
      ((1 / 2 : ℝ≥0∞) • Measure.dirac false) :=
    (integrable_dirac (f := g) (by simp)).smul_measure (by norm_num)
  have hgtrue : Integrable g
      ((1 / 2 : ℝ≥0∞) • Measure.dirac true) :=
    (integrable_dirac (f := g) (by simp)).smul_measure (by norm_num)
  rw [coin, integral_add_measure hgfalse hgtrue,
    integral_smul_measure, integral_smul_measure]
  norm_num
  ring

/-- One-coordinate change of measure relative to the fair coin. -/
theorem integral_harperTiltedCoin_eq_coin
    (p : ℕ) (t : ℝ) (g : Bool → ℝ) :
    (∫ b, g b ∂harperTiltedCoin p t) =
      ∫ b,
        (harperCoordinateFactor p t b / (1 + (p : ℝ)⁻¹)) * g b
        ∂coin := by
  rw [integral_harperTiltedCoin, integral_coin_bool]
  unfold harperTiltedCoinWeight
  have hnormalizer : 1 + (p : ℝ)⁻¹ ≠ 0 := by positivity
  field_simp

/-- Bias of the sign at `p` under Harper's tilted law. -/
noncomputable def harperTiltBias (p : ℕ) (t : ℝ) : ℝ :=
  2 * Real.cos (t * Real.log (p : ℝ)) /
    (Real.sqrt (p : ℝ) * (1 + (p : ℝ)⁻¹))

theorem harperCoordinateFactor_true_sub_false (p : ℕ) (t : ℝ) :
    harperCoordinateFactor p t true - harperCoordinateFactor p t false =
      4 * Real.cos (t * Real.log (p : ℝ)) / Real.sqrt (p : ℝ) := by
  by_cases hp : p = 0
  · subst p
    norm_num [harperCoordinateFactor, harperEulerFactor, ε]
  · have hp0 : 0 < p := Nat.pos_of_ne_zero hp
    rw [harperCoordinateFactor, harperCoordinateFactor,
      harperEulerFactor_eq (fun _ ↦ true) hp0,
      harperEulerFactor_eq (fun _ ↦ false) hp0]
    simp [ε]
    ring

theorem harperTiltedCoinWeight_true_sub_false (p : ℕ) (t : ℝ) :
    harperTiltedCoinWeight p t true - harperTiltedCoinWeight p t false =
      harperTiltBias p t := by
  by_cases hp : p = 0
  · subst p
    norm_num [harperTiltedCoinWeight, harperCoordinateFactor,
      harperEulerFactor, harperTiltBias, ε]
  · have hp0 : 0 < p := Nat.pos_of_ne_zero hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
    have hsqrt : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hpR).ne'
    have hnormalizer : 1 + (p : ℝ)⁻¹ ≠ 0 := by positivity
    unfold harperTiltedCoinWeight harperTiltBias
    rw [← sub_div, harperCoordinateFactor_true_sub_false]
    field_simp
    ring

/-- Exact mean of one Rademacher sign under the tilted coin. -/
theorem integral_cubeSign_harperTiltedCoin (p : ℕ) (t : ℝ) :
    (∫ b, cubeSign b ∂harperTiltedCoin p t) = harperTiltBias p t := by
  rw [integral_harperTiltedCoin]
  change harperTiltedCoinWeight p t false * (-1) +
      harperTiltedCoinWeight p t true * 1 = harperTiltBias p t
  rw [mul_neg, mul_one, mul_one]
  linarith [harperTiltedCoinWeight_true_sub_false p t]

/-- The finite type of prime coordinates through `y`. -/
abbrev HarperPrimeIndex (y : ℕ) := {p : ℕ // p ∈ (y + 1).primesBelow}

/-- Boolean assignments to all prime coordinates through `y`. -/
abbrev HarperPrimeCube (y : ℕ) := HarperPrimeIndex y → Bool

/-- Product of the independently tilted prime-coordinate laws. -/
noncomputable def harperTiltedCubeLaw (y : ℕ) (t : ℝ) :
    Measure (HarperPrimeCube y) :=
  Measure.pi fun p : HarperPrimeIndex y ↦ harperTiltedCoin p.1 t

instance harperTiltedCubeLaw_isProbabilityMeasure (y : ℕ) (t : ℝ) :
    IsProbabilityMeasure (harperTiltedCubeLaw y t) := by
  unfold harperTiltedCubeLaw
  infer_instance

/-- The Euler density on the finite prime cube, before normalization. -/
noncomputable def harperCubeDensity
    (y : ℕ) (t : ℝ) (eta : HarperPrimeCube y) : ℝ :=
  ∏ p : HarperPrimeIndex y, harperCoordinateFactor p.1 t (eta p)

theorem harperCubeDensity_nonneg
    (y : ℕ) (t : ℝ) (eta : HarperPrimeCube y) :
    0 ≤ harperCubeDensity y t eta := by
  unfold harperCubeDensity
  exact Finset.prod_nonneg fun p _ ↦
    harperCoordinateFactor_nonneg p.1 t (eta p)

/-- The normalized density on the finite prime cube. -/
noncomputable def normalizedHarperCubeDensity
    (y : ℕ) (t : ℝ) (eta : HarperPrimeCube y) : ℝ :=
  harperCubeDensity y t eta / primeEnergyNormalizer y

theorem normalizedHarperCubeDensity_nonneg
    (y : ℕ) (t : ℝ) (eta : HarperPrimeCube y) :
    0 ≤ normalizedHarperCubeDensity y t eta := by
  exact div_nonneg (harperCubeDensity_nonneg y t eta)
    (primeEnergyNormalizer_pos y).le

theorem harperTiltedCoinWeight_eq_normalized_mul_half
    (p : ℕ) (t : ℝ) (b : Bool) :
    harperTiltedCoinWeight p t b =
      (harperCoordinateFactor p t b / (1 + (p : ℝ)⁻¹)) * (1 / 2 : ℝ) := by
  unfold harperTiltedCoinWeight
  have hnormalizer : 1 + (p : ℝ)⁻¹ ≠ 0 := by positivity
  field_simp

/-- The product of the one-prime normalizers is the repository's exact
energy normalizer. -/
theorem prod_harperCoordinateNormalizer (y : ℕ) :
    (∏ p : HarperPrimeIndex y, (1 + (p.1 : ℝ)⁻¹)) =
      primeEnergyNormalizer y := by
  unfold primeEnergyNormalizer
  exact Finset.prod_coe_sort ((y + 1).primesBelow)
    (fun p ↦ 1 + (p : ℝ)⁻¹)

/-- Product factorization of the tilted point mass into the normalized Euler
density and the corresponding fair-cube point mass. -/
theorem prod_harperTiltedCoinWeight_eq
    (y : ℕ) (t : ℝ) (eta : HarperPrimeCube y) :
    (∏ p : HarperPrimeIndex y, harperTiltedCoinWeight p.1 t (eta p)) =
      normalizedHarperCubeDensity y t eta *
        ∏ _p : HarperPrimeIndex y, (1 / 2 : ℝ) := by
  simp_rw [harperTiltedCoinWeight_eq_normalized_mul_half]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib,
    prod_harperCoordinateNormalizer]
  rfl

@[simp] theorem harperTiltedCubeLaw_real_singleton
    (y : ℕ) (t : ℝ) (eta : HarperPrimeCube y) :
    (harperTiltedCubeLaw y t).real {eta} =
      ∏ p : HarperPrimeIndex y, harperTiltedCoinWeight p.1 t (eta p) := by
  rw [Measure.real, harperTiltedCubeLaw, Measure.pi_singleton,
    ENNReal.toReal_prod]
  simp

theorem fairHarperCubeLaw_real_singleton
    (y : ℕ) (eta : HarperPrimeCube y) :
    (Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)).real {eta} =
      ∏ _p : HarperPrimeIndex y, (1 / 2 : ℝ) := by
  rw [Measure.real, Measure.pi_singleton]
  have hcoin (p : HarperPrimeIndex y) :
      coin {eta p} = (1 / 2 : ℝ≥0∞) := by
    cases eta p <;> simp [coin]
  simp_rw [hcoin]
  rw [ENNReal.toReal_prod]
  simp

/-- Exact point-mass Radon--Nikodym identity on the finite cube. -/
theorem harperTiltedCubeLaw_real_singleton_eq
    (y : ℕ) (t : ℝ) (eta : HarperPrimeCube y) :
    (harperTiltedCubeLaw y t).real {eta} =
      normalizedHarperCubeDensity y t eta *
        (Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)).real {eta} := by
  rw [harperTiltedCubeLaw_real_singleton,
    fairHarperCubeLaw_real_singleton,
    prod_harperTiltedCoinWeight_eq]

/-- Change of measure from the fair finite cube to Harper's tilted product
law. -/
theorem integral_harperTiltedCubeLaw_eq
    (y : ℕ) (t : ℝ) (g : HarperPrimeCube y → ℝ) :
    (∫ eta, g eta ∂harperTiltedCubeLaw y t) =
      ∫ eta, normalizedHarperCubeDensity y t eta * g eta
        ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) := by
  rw [integral_fintype (Integrable.of_finite :
      Integrable g (harperTiltedCubeLaw y t)),
    integral_fintype (Integrable.of_finite :
      Integrable (fun eta ↦ normalizedHarperCubeDensity y t eta * g eta)
        (Measure.pi (fun _ : HarperPrimeIndex y ↦ coin)))]
  apply Finset.sum_congr rfl
  intro eta heta
  rw [harperTiltedCubeLaw_real_singleton_eq]
  simp only [smul_eq_mul]
  ring

/-- The tilted coordinates remain independent because the tilted measure is
an explicit finite product. -/
theorem iIndepFun_harperTiltedCube_coordinates (y : ℕ) (t : ℝ) :
    iIndepFun
      (fun p : HarperPrimeIndex y ↦
        fun eta : HarperPrimeCube y ↦ eta p)
      (harperTiltedCubeLaw y t) := by
  unfold harperTiltedCubeLaw
  exact iIndepFun_pi
    (X := fun _ : HarperPrimeIndex y ↦ id)
    (fun _ ↦ aemeasurable_id)

/-- Each coordinate projection has exactly its corresponding tilted coin as
its marginal law. -/
theorem measurePreserving_harperTiltedCube_eval
    (y : ℕ) (t : ℝ) (p : HarperPrimeIndex y) :
    MeasurePreserving
      (fun eta : HarperPrimeCube y ↦ eta p)
      (harperTiltedCubeLaw y t) (harperTiltedCoin p.1 t) := by
  unfold harperTiltedCubeLaw
  exact measurePreserving_eval
    (fun q : HarperPrimeIndex y ↦ harperTiltedCoin q.1 t) p

/-- Expectations of products of one-coordinate observables factor exactly
under the tilted law. -/
theorem integral_prod_harperTiltedCubeLaw
    (y : ℕ) (t : ℝ)
    (g : HarperPrimeIndex y → Bool → ℝ) :
    (∫ eta, ∏ p : HarperPrimeIndex y, g p (eta p)
        ∂harperTiltedCubeLaw y t) =
      ∏ p : HarperPrimeIndex y,
        ∫ b, g p b ∂harperTiltedCoin p.1 t := by
  let X : HarperPrimeIndex y → HarperPrimeCube y → ℝ :=
    fun p eta ↦ g p (eta p)
  have hbase := iIndepFun_harperTiltedCube_coordinates y t
  have hX : iIndepFun X (harperTiltedCubeLaw y t) := by
    have hcomp := hbase.comp g (fun _ ↦ measurable_of_finite _)
    simpa only [X, Function.comp_apply] using! hcomp
  have hprod := hX.integral_fun_prod_eq_prod_integral
    (fun p ↦ (measurable_of_finite (X p)).aestronglyMeasurable)
  calc
    (∫ eta, ∏ p : HarperPrimeIndex y, g p (eta p)
        ∂harperTiltedCubeLaw y t) =
        ∏ p : HarperPrimeIndex y,
          ∫ eta, g p (eta p) ∂harperTiltedCubeLaw y t := by
      simpa only [X] using! hprod
    _ = ∏ p : HarperPrimeIndex y,
        ∫ b, g p b ∂harperTiltedCoin p.1 t := by
      apply Finset.prod_congr rfl
      intro p hp
      have hmp := measurePreserving_harperTiltedCube_eval y t p
      calc
        (∫ eta, g p (eta p) ∂harperTiltedCubeLaw y t) =
            ∫ b, g p b ∂Measure.map
              (fun eta : HarperPrimeCube y ↦ eta p)
              (harperTiltedCubeLaw y t) := by
          symm
          exact integral_map
            (hmp.measurable.aemeasurable)
            (measurable_of_finite (g p)).aestronglyMeasurable
        _ = ∫ b, g p b ∂harperTiltedCoin p.1 t := by
          rw [hmp.map_eq]

/-- Replace the prime coordinates through `y`, leaving the exterior
configuration frozen. -/
def spliceHarperCube
    (y : ℕ) (old : Omega) (eta : HarperPrimeCube y) : Omega :=
  Function.updateFinset old ((y + 1).primesBelow) eta

theorem harperCoordinateFactor_eq_spliceHarperCube
    (y : ℕ) (old : Omega) (eta : HarperPrimeCube y)
    (p : HarperPrimeIndex y) (t : ℝ) :
    harperCoordinateFactor p.1 t (eta p) =
      harperEulerFactor (spliceHarperCube y old eta) p.1 t := by
  unfold harperCoordinateFactor harperEulerFactor spliceHarperCube ε
  simp [Function.updateFinset, p.property]

/-- On every fiber, the finite cube density is the actual Euler-product
density. -/
theorem harperCubeDensity_eq_spliceHarperCube
    (y : ℕ) (old : Omega) (eta : HarperPrimeCube y) (t : ℝ) :
    harperCubeDensity y t eta =
      harperEulerDensity y (spliceHarperCube y old eta) t := by
  unfold harperCubeDensity harperEulerDensity
  calc
    (∏ p : HarperPrimeIndex y, harperCoordinateFactor p.1 t (eta p)) =
        ∏ p : HarperPrimeIndex y,
          harperEulerFactor (spliceHarperCube y old eta) p.1 t := by
      apply Finset.prod_congr rfl
      intro p hp
      exact harperCoordinateFactor_eq_spliceHarperCube y old eta p t
    _ = ∏ p ∈ (y + 1).primesBelow,
          harperEulerFactor (spliceHarperCube y old eta) p t :=
      Finset.prod_coe_sort ((y + 1).primesBelow)
        (fun p ↦ harperEulerFactor (spliceHarperCube y old eta) p t)

theorem normalizedHarperCubeDensity_eq_spliceHarperCube
    (y : ℕ) (old : Omega) (eta : HarperPrimeCube y) (t : ℝ) :
    normalizedHarperCubeDensity y t eta =
      normalizedHarperEulerDensity y (spliceHarperCube y old eta) t := by
  unfold normalizedHarperCubeDensity normalizedHarperEulerDensity
  rw [harperCubeDensity_eq_spliceHarperCube y old eta t]

/-- Fiber form of the change-of-measure identity, with every coordinate
outside the prime cutoff frozen arbitrarily. -/
theorem integral_harperTiltedCubeLaw_eq_fairFiber
    (y : ℕ) (t : ℝ) (old : Omega) (G : Omega → ℝ) :
    (∫ eta, G (spliceHarperCube y old eta)
        ∂harperTiltedCubeLaw y t) =
      ∫ eta,
        normalizedHarperEulerDensity y (spliceHarperCube y old eta) t *
          G (spliceHarperCube y old eta)
        ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) := by
  rw [integral_harperTiltedCubeLaw_eq]
  apply integral_congr_ae
  exact ae_of_all _ fun eta ↦ by
    change normalizedHarperCubeDensity y t eta *
        G (spliceHarperCube y old eta) =
      normalizedHarperEulerDensity y (spliceHarperCube y old eta) t *
        G (spliceHarperCube y old eta)
    rw [normalizedHarperCubeDensity_eq_spliceHarperCube y old eta t]

end Problem520
end Erdos
