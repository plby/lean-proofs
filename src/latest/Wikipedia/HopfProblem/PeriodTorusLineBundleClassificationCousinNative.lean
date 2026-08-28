import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinCochain
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticCoordinates

/-!
# Native covering-space coordinates for additive Cousin data

The domains and transition functions here live on the actual
`ComplexPlane₂ = Fin 2 → ℂ`.  The canonical complex continuous linear
equivalence transports this data to the product-coordinate cocycle.
Every actual analytic product cochain pulls back to native analytic
functions with precisely the original transitions.

This file proves the coordinate construction and transport.  It does not
postulate a global Cousin solution among the input data.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin

open PeriodTorusLineBundleClassificationPolydiscAnalytic

/-- An actual additive holomorphic cocycle on an arbitrary native open
cover.  All fields concern the given cover and its transition functions. -/
structure NativeCocycle (ι : Type*) where
  domain : ι → Set ComplexPlane₂
  isOpen_domain : ∀ i, IsOpen (domain i)
  cover : ∀ x, ∃ i, x ∈ domain i
  transition : ι → ι → ComplexPlane₂ → ℂ
  holomorphic : ∀ i j, AnalyticOnNhd ℂ (transition i j) (domain i ∩ domain j)
  additive : ∀ i j k x, x ∈ domain i → x ∈ domain j → x ∈ domain k →
    transition i j x + transition j k x = transition i k x

/-- Pull an actual family of product-coordinate functions back along the
canonical complex continuous linear equivalence. -/
def cochainToNative {ι : Type*} (g : ι → ℂ × ℂ → ℂ) : ι → ComplexPlane₂ → ℂ :=
  fun i z => g i (complexPairEquiv z)

@[simp] theorem cochainToNative_apply {ι : Type*} (g : ι → ℂ × ℂ → ℂ)
    (i : ι) (z : ComplexPlane₂) : cochainToNative g i z = g i (complexPairEquiv z) := rfl

namespace NativeCocycle

variable {ι : Type*} (C : NativeCocycle ι)

/-- The product-model cocycle is the actual inverse-coordinate pullback
of the given native domains and functions. -/
def toProduct : Cocycle ι where
  domain i := complexPairEquiv.symm ⁻¹' C.domain i
  isOpen_domain i := (C.isOpen_domain i).preimage complexPairEquiv.symm.continuous
  cover q := C.cover (complexPairEquiv.symm q)
  transition i j := C.transition i j ∘ complexPairEquiv.symm
  holomorphic i j := by
    intro q hq
    exact (C.holomorphic i j (complexPairEquiv.symm q) hq).comp
      (complexPairEquiv.symm.toContinuousLinearMap.analyticAt q)
  additive i j k q hi hj hk := C.additive i j k (complexPairEquiv.symm q) hi hj hk

@[simp] theorem toProduct_domain (i : ι) :
    C.toProduct.domain i = complexPairEquiv.symm ⁻¹' C.domain i := rfl

@[simp] theorem toProduct_transition_apply (i j : ι) (q : ℂ × ℂ) :
    C.toProduct.transition i j q = C.transition i j (complexPairEquiv.symm q) := rfl

@[simp] theorem mem_toProduct_domain (i : ι) (z : ComplexPlane₂) :
    complexPairEquiv z ∈ C.toProduct.domain i ↔ z ∈ C.domain i := by
  simp only [toProduct_domain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply]

/-- Actual holomorphic product-coordinate representatives give actual
holomorphic representatives on the original native domains. -/
theorem cochainToNative_analyticOnNhd (g : ι → ℂ × ℂ → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) (C.toProduct.domain i)) (i : ι) :
    AnalyticOnNhd ℂ (cochainToNative g i) (C.domain i) := by
  intro z hz
  exact (hg i (complexPairEquiv z) ((C.mem_toProduct_domain i z).mpr hz)).comp
    (complexPairEquiv.toContinuousLinearMap.analyticAt z)

/-- The transported analytic representatives also have the native `C^ω`
regularity used by holomorphic bundle constructions. -/
theorem cochainToNative_contDiffOn (g : ι → ℂ × ℂ → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) (C.toProduct.domain i)) (i : ι) :
    ContDiffOn ℂ ω (cochainToNative g i) (C.domain i) :=
  (C.cochainToNative_analyticOnNhd g hg i).contDiffOn_of_completeSpace

/-- Pullback preserves the given additive transitions, with the native
point and native overlap unchanged. -/
theorem cochainToNative_sub (g : ι → ℂ × ℂ → ℂ)
    (hsub : ∀ i j q, q ∈ C.toProduct.domain i → q ∈ C.toProduct.domain j →
      g i q - g j q = C.toProduct.transition i j q)
    (i j : ι) {z : ComplexPlane₂} (hi : z ∈ C.domain i) (hj : z ∈ C.domain j) :
    cochainToNative g i z - cochainToNative g j z = C.transition i j z := by
  have h := hsub i j (complexPairEquiv z)
    ((C.mem_toProduct_domain i z).mpr hi) ((C.mem_toProduct_domain j z).mpr hj)
  simpa only [cochainToNative_apply, toProduct_transition_apply,
    ContinuousLinearEquiv.symm_apply_apply] using h

/-- Transport an actual analytic cochain solution to the original native
cover.  The cochain is supplied explicitly, not assumed to exist in a class. -/
theorem cochainToNative_is_solution (g : ι → ℂ × ℂ → ℂ)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) (C.toProduct.domain i))
    (hsub : ∀ i j q, q ∈ C.toProduct.domain i → q ∈ C.toProduct.domain j →
      g i q - g j q = C.toProduct.transition i j q) :
    (∀ i, AnalyticOnNhd ℂ (cochainToNative g i) (C.domain i)) ∧
      (∀ i j z, z ∈ C.domain i → z ∈ C.domain j →
        cochainToNative g i z - cochainToNative g j z = C.transition i j z) :=
  ⟨C.cochainToNative_analyticOnNhd g hg,
    fun i j _ hi hj => C.cochainToNative_sub g hsub i j hi hj⟩

end NativeCocycle

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin
