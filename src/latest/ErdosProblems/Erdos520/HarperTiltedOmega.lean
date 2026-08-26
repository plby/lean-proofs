import ErdosProblems.Erdos520.HarperTiltedLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Harper's tilted law on the infinite sign space

The Euler-product density through `y` only sees the prime coordinates at
most `y`.  This file identifies those coordinates with the finite Harper
prime cube and pulls the exact finite-cube change of measure back to the
original infinite product space `Omega`.
-/

/-- Restrict an infinite sign configuration to the prime coordinates through
`y`. -/
def harperPrimeRestriction (y : ℕ) : Omega → HarperPrimeCube y :=
  fun omega p ↦ omega p.1

@[simp] theorem harperPrimeRestriction_apply
    (y : ℕ) (omega : Omega) (p : HarperPrimeIndex y) :
    harperPrimeRestriction y omega p = omega p.1 := rfl

theorem measurable_harperPrimeRestriction (y : ℕ) :
    Measurable (harperPrimeRestriction y) := by
  rw [measurable_pi_iff]
  intro p
  exact measurable_pi_apply p.1

/-- Under the fair infinite product law, restriction to the primes through
`y` has exactly the finite fair product law. -/
theorem map_harperPrimeRestriction_mu (y : ℕ) :
    μ.map (harperPrimeRestriction y) =
      Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) := by
  let X : (p : HarperPrimeIndex y) → Omega → Bool :=
    fun p omega ↦ omega p.1
  have hIndep : iIndepFun X μ := by
    exact iIndepFun_coordinates.precomp Subtype.val_injective
  have hXmeas (p : HarperPrimeIndex y) : AEMeasurable (X p) μ := by
    simpa [X] using!
      (measurable_pi_apply p.1 :
        Measurable (fun omega : Omega ↦ omega p.1)).aemeasurable
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
      (μ := μ) (f := X) hXmeas).mp hIndep
  calc
    μ.map (harperPrimeRestriction y) =
        μ.map (fun omega p ↦ X p omega) := by
      rfl
    _ = Measure.pi (fun p : HarperPrimeIndex y ↦ μ.map (X p)) := hmap
    _ = Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) := by
      congr 1
      funext p
      simpa [μ, X] using!
        (Measure.infinitePi_map_eval (fun _ : ℕ ↦ coin) p.1)

/-- Pullback integration from the finite fair prime cube to the fair infinite
product space.  No integrability premise is needed because the source cube is
finite. -/
theorem integral_comp_harperPrimeRestriction_mu
    (y : ℕ) (g : HarperPrimeCube y → ℝ) :
    (∫ omega, g (harperPrimeRestriction y omega) ∂μ) =
      ∫ eta, g eta ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) := by
  calc
    (∫ omega, g (harperPrimeRestriction y omega) ∂μ) =
        ∫ eta, g eta ∂μ.map (harperPrimeRestriction y) := by
      symm
      exact integral_map
        (measurable_harperPrimeRestriction y).aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = ∫ eta, g eta
        ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) := by
      rw [map_harperPrimeRestriction_mu]

/-- The finite-cube Euler density is literally the original Euler density
after restricting an infinite configuration. -/
theorem harperCubeDensity_harperPrimeRestriction
    (y : ℕ) (omega : Omega) (t : ℝ) :
    harperCubeDensity y t (harperPrimeRestriction y omega) =
      harperEulerDensity y omega t := by
  unfold harperCubeDensity harperEulerDensity harperCoordinateFactor
  calc
    (∏ p : HarperPrimeIndex y,
        harperEulerFactor
          (fun _ ↦ harperPrimeRestriction y omega p) p.1 t) =
        ∏ p : HarperPrimeIndex y, harperEulerFactor omega p.1 t := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [harperEulerFactor, ε, harperPrimeRestriction]
    _ = ∏ p ∈ (y + 1).primesBelow,
        harperEulerFactor omega p t :=
      Finset.prod_coe_sort ((y + 1).primesBelow)
        (fun p ↦ harperEulerFactor omega p t)

/-- The normalized finite and infinite Euler densities agree pointwise under
prime restriction. -/
theorem normalizedHarperCubeDensity_harperPrimeRestriction
    (y : ℕ) (omega : Omega) (t : ℝ) :
    normalizedHarperCubeDensity y t (harperPrimeRestriction y omega) =
      normalizedHarperEulerDensity y omega t := by
  unfold normalizedHarperCubeDensity normalizedHarperEulerDensity
  rw [harperCubeDensity_harperPrimeRestriction]

/-- Pullback form of the weighted fair-cube integral. -/
theorem integral_normalizedHarperEulerDensity_mul_comp_eq
    (y : ℕ) (t : ℝ) (g : HarperPrimeCube y → ℝ) :
    (∫ omega,
        normalizedHarperEulerDensity y omega t *
          g (harperPrimeRestriction y omega) ∂μ) =
      ∫ eta, normalizedHarperCubeDensity y t eta * g eta
        ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) := by
  rw [← integral_comp_harperPrimeRestriction_mu y
    (fun eta ↦ normalizedHarperCubeDensity y t eta * g eta)]
  apply integral_congr_ae
  exact ae_of_all μ fun omega ↦ by
    change normalizedHarperEulerDensity y omega t *
        g (harperPrimeRestriction y omega) =
      normalizedHarperCubeDensity y t (harperPrimeRestriction y omega) *
        g (harperPrimeRestriction y omega)
    rw [normalizedHarperCubeDensity_harperPrimeRestriction]

/-- Exact change of measure on `Omega` for every observable depending only on
the prime coordinates through `y`.  Equivalently, the tilted finite-cube
expectation is the fair infinite-product expectation weighted by the
normalized squared Euler product. -/
theorem integral_harperTiltedCubeLaw_eq_omega
    (y : ℕ) (t : ℝ) (g : HarperPrimeCube y → ℝ) :
    (∫ eta, g eta ∂harperTiltedCubeLaw y t) =
      ∫ omega,
        normalizedHarperEulerDensity y omega t *
          g (harperPrimeRestriction y omega) ∂μ := by
  calc
    (∫ eta, g eta ∂harperTiltedCubeLaw y t) =
        ∫ eta, normalizedHarperCubeDensity y t eta * g eta
          ∂Measure.pi (fun _ : HarperPrimeIndex y ↦ coin) :=
      integral_harperTiltedCubeLaw_eq y t g
    _ = ∫ omega,
        normalizedHarperEulerDensity y omega t *
          g (harperPrimeRestriction y omega) ∂μ :=
      (integral_normalizedHarperEulerDensity_mul_comp_eq y t g).symm

/-- Event form of the exact change of measure: a finite-cube event is pulled
back to the corresponding event on `Omega`. -/
theorem harperTiltedCubeLaw_real_apply_eq_omega
    (y : ℕ) (t : ℝ) (A : Set (HarperPrimeCube y)) :
    (harperTiltedCubeLaw y t).real A =
      ∫ omega in harperPrimeRestriction y ⁻¹' A,
        normalizedHarperEulerDensity y omega t ∂μ := by
  have hAfin : A.Finite := Set.toFinite A
  have hA : MeasurableSet A := hAfin.measurableSet
  have hpre : MeasurableSet (harperPrimeRestriction y ⁻¹' A) :=
    hA.preimage (measurable_harperPrimeRestriction y)
  rw [← integral_indicator_one (μ := harperTiltedCubeLaw y t) hA,
    integral_harperTiltedCubeLaw_eq_omega]
  rw [← integral_indicator hpre]
  apply integral_congr_ae
  exact ae_of_all μ fun omega ↦ by
    by_cases hmem : harperPrimeRestriction y omega ∈ A
    · simp [Set.indicator_of_mem, hmem]
    · simp [Set.indicator_of_notMem, hmem]

end Problem520
end Erdos
