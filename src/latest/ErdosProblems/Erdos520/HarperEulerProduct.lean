import ErdosProblems.Erdos520.ExactEnergyMartingale
import ErdosProblems.Erdos520.OrthogonalMaximal

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# The finite Rademacher Euler-product density

This file starts the kernel-level version of the Harper input.  It defines
the real density

`|prod_{p <= y} (1 + eps_p p^(-1/2-it))|^2`

without introducing complex powers, and proves its exact first-moment
normalization from the product measure.  The missing Harper estimate is a
*fractional* moment saving over this first-moment identity; it does not follow
from Jensen or ordinary finite-cube hypercontractivity.
-/

/-- The squared norm of one Rademacher Euler factor on the critical line.
It is written as the sum of the squares of its real and imaginary parts, so
nonnegativity is definitional. -/
noncomputable def harperEulerFactor
    (omega : Omega) (p : ℕ) (t : ℝ) : ℝ :=
  (1 + ε omega p * Real.cos (t * Real.log (p : ℝ)) /
      Real.sqrt (p : ℝ)) ^ 2 +
    (ε omega p * Real.sin (t * Real.log (p : ℝ)) /
      Real.sqrt (p : ℝ)) ^ 2

theorem harperEulerFactor_nonneg (omega : Omega) (p : ℕ) (t : ℝ) :
    0 ≤ harperEulerFactor omega p t := by
  unfold harperEulerFactor
  positivity

/-- Expansion of one squared Euler factor. -/
theorem harperEulerFactor_eq
    (omega : Omega) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    harperEulerFactor omega p t =
      1 + (p : ℝ)⁻¹ +
        2 * ε omega p * Real.cos (t * Real.log (p : ℝ)) /
          Real.sqrt (p : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsqrt : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hpR).ne'
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  have htrig :
      Real.sin (t * Real.log (p : ℝ)) ^ 2 +
        Real.cos (t * Real.log (p : ℝ)) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq _
  have heps : ε omega p ^ 2 = 1 := ε_sq omega p
  have hinv : (p : ℝ)⁻¹ = (Real.sqrt (p : ℝ))⁻¹ ^ 2 := by
    calc
      (p : ℝ)⁻¹ = (Real.sqrt (p : ℝ) ^ 2)⁻¹ :=
        congrArg (fun x : ℝ ↦ x⁻¹) hsqrtSq.symm
      _ = (Real.sqrt (p : ℝ))⁻¹ ^ 2 := by rw [inv_pow]
  unfold harperEulerFactor
  rw [hinv]
  field_simp [hsqrt]
  nlinarith [hsqrtSq]

theorem stronglyMeasurable_harperEulerFactor (p : ℕ) (t : ℝ) :
    StronglyMeasurable (fun omega : Omega ↦ harperEulerFactor omega p t) := by
  unfold harperEulerFactor
  have heps : StronglyMeasurable (fun omega : Omega ↦ ε omega p) :=
    (measurable_ε p).stronglyMeasurable
  have hreal : StronglyMeasurable (fun omega : Omega ↦
      ε omega p * Real.cos (t * Real.log (p : ℝ)) /
        Real.sqrt (p : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_assoc] using!
      heps.mul_const
        (Real.cos (t * Real.log (p : ℝ)) * (Real.sqrt (p : ℝ))⁻¹)
  have himag : StronglyMeasurable (fun omega : Omega ↦
      ε omega p * Real.sin (t * Real.log (p : ℝ)) /
        Real.sqrt (p : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_assoc] using!
      heps.mul_const
        (Real.sin (t * Real.log (p : ℝ)) * (Real.sqrt (p : ℝ))⁻¹)
  exact ((stronglyMeasurable_const.add hreal).pow 2).add (himag.pow 2)

theorem integrable_harperEulerFactor {p : ℕ} (hp : 0 < p) (t : ℝ) :
    Integrable (fun omega : Omega ↦ harperEulerFactor omega p t) μ := by
  have heq : (fun omega : Omega ↦ harperEulerFactor omega p t) =
      fun omega ↦
        (1 + (p : ℝ)⁻¹) +
          (2 * Real.cos (t * Real.log (p : ℝ)) /
            Real.sqrt (p : ℝ)) * ε omega p := by
    funext omega
    rw [harperEulerFactor_eq omega hp]
    ring
  rw [heq]
  have hc : Integrable (fun _ : Omega ↦ 1 + (p : ℝ)⁻¹) μ :=
    integrable_const _
  exact hc.add ((integrable_ε p).const_mul _)

/-- The expectation of one squared Euler factor is exactly its deterministic
normalizer. -/
theorem integral_harperEulerFactor
    {p : ℕ} (hp : 0 < p) (t : ℝ) :
    (∫ omega, harperEulerFactor omega p t ∂μ) = 1 + (p : ℝ)⁻¹ := by
  have heq : (fun omega : Omega ↦ harperEulerFactor omega p t) =
      fun omega ↦
        (1 + (p : ℝ)⁻¹) +
          (2 * Real.cos (t * Real.log (p : ℝ)) /
            Real.sqrt (p : ℝ)) * ε omega p := by
    funext omega
    rw [harperEulerFactor_eq omega hp]
    ring
  have hc : Integrable (fun _ : Omega ↦ 1 + (p : ℝ)⁻¹) μ :=
    integrable_const _
  have hepsInt : Integrable (fun omega : Omega ↦
      (2 * Real.cos (t * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)) *
        ε omega p) μ :=
    (integrable_ε p).const_mul _
  rw [heq, integral_add hc hepsInt, integral_const, integral_const_mul,
    integral_ε]
  simp

/-- The squared finite Euler product through the integer cutoff `y`. -/
noncomputable def harperEulerDensity
    (y : ℕ) (omega : Omega) (t : ℝ) : ℝ :=
  ∏ p ∈ (y + 1).primesBelow, harperEulerFactor omega p t

theorem harperEulerDensity_nonneg (y : ℕ) (omega : Omega) (t : ℝ) :
    0 ≤ harperEulerDensity y omega t := by
  unfold harperEulerDensity
  exact Finset.prod_nonneg fun p hp ↦ harperEulerFactor_nonneg omega p t

theorem stronglyMeasurable_harperEulerDensity (y : ℕ) (t : ℝ) :
    StronglyMeasurable (fun omega : Omega ↦ harperEulerDensity y omega t) := by
  unfold harperEulerDensity
  exact Finset.stronglyMeasurable_fun_prod _ fun p _ ↦
    stronglyMeasurable_harperEulerFactor p t

/-- The finite Euler-product density only depends on the prime coordinates at
most its cutoff. -/
theorem harperEulerDensity_eq_of_eq_on_primesBelow
    {y : ℕ} {omega omega' : Omega}
    (h : ∀ p ∈ (y + 1).primesBelow, omega p = omega' p) (t : ℝ) :
    harperEulerDensity y omega t = harperEulerDensity y omega' t := by
  unfold harperEulerDensity
  apply Finset.prod_congr rfl
  intro p hp
  unfold harperEulerFactor ε
  rw [h p hp]

/-- Finite-coordinate measurability of the Euler-product density. -/
theorem stronglyMeasurable_harperEulerDensity_piFinset (y : ℕ) (t : ℝ) :
    StronglyMeasurable[Filtration.piFinset ((y + 1).primesBelow)]
      (fun omega : Omega ↦ harperEulerDensity y omega t) := by
  classical
  let s : Finset ℕ := (y + 1).primesBelow
  let base : Omega := fun _ ↦ false
  let G : (s → Bool) → ℝ := fun eta ↦
    harperEulerDensity y (Function.updateFinset base s eta) t
  have hG : StronglyMeasurable G :=
    (measurable_of_finite G).stronglyMeasurable
  have hcomp : StronglyMeasurable[Filtration.piFinset s]
      (fun omega : Omega ↦ G (s.restrict omega)) :=
    hG.comp_measurable (measurable_restrict_piFinset s)
  have heq : (fun omega : Omega ↦ harperEulerDensity y omega t) =
      fun omega : Omega ↦ G (s.restrict omega) := by
    funext omega
    apply harperEulerDensity_eq_of_eq_on_primesBelow
    intro p hp
    change p ∈ s at hp
    simp [Function.updateFinset, hp]
  change StronglyMeasurable[Filtration.piFinset s]
    (fun omega : Omega ↦ harperEulerDensity y omega t)
  rw [heq]
  exact hcomp

/-- The finite density is integrable under the infinite product law. -/
theorem integrable_harperEulerDensity (y : ℕ) (t : ℝ) :
    Integrable (fun omega : Omega ↦ harperEulerDensity y omega t) μ :=
  integrable_of_stronglyMeasurable_piFinset
    (stronglyMeasurable_harperEulerDensity_piFinset y t)

/-- Exact first moment of the finite critical Euler-product density. -/
theorem integral_harperEulerDensity (y : ℕ) (t : ℝ) :
    (∫ omega, harperEulerDensity y omega t ∂μ) =
      primeEnergyNormalizer y := by
  let P : Finset ℕ := (y + 1).primesBelow
  let X : P → Omega → ℝ := fun p omega ↦
    harperEulerFactor omega p.1 t
  have hbase : iIndepFun
      (fun p : P ↦ fun omega : Omega ↦ ε omega p.1) μ := by
    exact iIndepFun.precomp (g := fun p : P ↦ p.1)
      Subtype.val_injective iIndepFun_ε
  have hX : iIndepFun X μ := by
    have hcomp := hbase.comp
      (fun p (x : ℝ) ↦
        (1 + x * Real.cos (t * Real.log (p.1 : ℝ)) /
            Real.sqrt (p.1 : ℝ)) ^ 2 +
          (x * Real.sin (t * Real.log (p.1 : ℝ)) /
            Real.sqrt (p.1 : ℝ)) ^ 2)
      (fun _ ↦ by fun_prop)
    simpa only [X, harperEulerFactor, Function.comp_apply] using! hcomp
  have hprod := hX.integral_fun_prod_eq_prod_integral
    (fun p ↦ (stronglyMeasurable_harperEulerFactor p.1 t).aestronglyMeasurable)
  unfold harperEulerDensity primeEnergyNormalizer
  calc
    (∫ omega, ∏ p ∈ P, harperEulerFactor omega p t ∂μ) =
        ∫ omega, ∏ p : P, X p omega ∂μ := by
      congr 1
      funext omega
      exact (Finset.prod_coe_sort P (fun p ↦ harperEulerFactor omega p t)).symm
    _ = ∏ p : P, ∫ omega, X p omega ∂μ := hprod
    _ = ∏ p : P, (1 + (p.1 : ℝ)⁻¹) := by
      apply Finset.prod_congr rfl
      intro p _hp
      exact integral_harperEulerFactor
        (Nat.Prime.pos (Nat.prime_of_mem_primesBelow p.property)) t
    _ = ∏ p ∈ P, (1 + (p : ℝ)⁻¹) :=
      Finset.prod_coe_sort P (fun p ↦ 1 + (p : ℝ)⁻¹)

/-- The exactly normalized critical Euler-product density. -/
noncomputable def normalizedHarperEulerDensity
    (y : ℕ) (omega : Omega) (t : ℝ) : ℝ :=
  harperEulerDensity y omega t / primeEnergyNormalizer y

theorem normalizedHarperEulerDensity_nonneg
    (y : ℕ) (omega : Omega) (t : ℝ) :
    0 ≤ normalizedHarperEulerDensity y omega t := by
  exact div_nonneg (harperEulerDensity_nonneg y omega t)
    (primeEnergyNormalizer_pos y).le

theorem stronglyMeasurable_normalizedHarperEulerDensity (y : ℕ) (t : ℝ) :
    StronglyMeasurable
      (fun omega : Omega ↦ normalizedHarperEulerDensity y omega t) := by
  unfold normalizedHarperEulerDensity
  exact (stronglyMeasurable_harperEulerDensity y t).div
    stronglyMeasurable_const

theorem integrable_normalizedHarperEulerDensity (y : ℕ) (t : ℝ) :
    Integrable
      (fun omega : Omega ↦ normalizedHarperEulerDensity y omega t) μ := by
  unfold normalizedHarperEulerDensity
  exact (integrable_harperEulerDensity y t).div_const _

/-- The critical density has mean one at every point on the vertical line. -/
theorem integral_normalizedHarperEulerDensity (y : ℕ) (t : ℝ) :
    (∫ omega, normalizedHarperEulerDensity y omega t ∂μ) = 1 := by
  unfold normalizedHarperEulerDensity
  rw [integral_div, integral_harperEulerDensity, div_self]
  exact (primeEnergyNormalizer_pos y).ne'

end Problem520
end Erdos
