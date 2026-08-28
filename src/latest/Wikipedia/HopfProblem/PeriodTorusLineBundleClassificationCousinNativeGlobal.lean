import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinNative
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinGlobal

/-!
# Genuine additive Cousin existence on the native covering space

The proved product-coordinate Cousin theorem supplies actual holomorphic
local functions.  Pulling them back along the canonical complex continuous
linear equivalence gives solutions on the original native open cover of
`ComplexPlane₂`.  Neither a Cousin solver nor a global antiholomorphic
primitive is among the hypotheses.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin

namespace NativeCocycle

variable {ι : Type*} (C : NativeCocycle ι)

/-- Every actual additive holomorphic cocycle on an arbitrary native open
cover has holomorphic local primitives with exactly the given differences. -/
theorem exists_holomorphic_cochain :
    ∃ s : ι → ComplexPlane₂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (s i) (C.domain i)) ∧
      ∀ i j x, x ∈ C.domain i → x ∈ C.domain j → s i x - s j x = C.transition i j x := by
  obtain ⟨s, hs, hsub⟩ := C.toProduct.exists_holomorphic_cochain
  exact ⟨cochainToNative s, C.cochainToNative_is_solution s hs hsub⟩

/-- The same actual solution has the native complex `C^ω` regularity
required for analytic vector-bundle transition constructions. -/
theorem exists_contDiff_cochain :
    ∃ s : ι → ComplexPlane₂ → ℂ,
      (∀ i, ContDiffOn ℂ ω (s i) (C.domain i)) ∧
      ∀ i j x, x ∈ C.domain i → x ∈ C.domain j → s i x - s j x = C.transition i j x := by
  obtain ⟨s, hs, hsub⟩ := C.exists_holomorphic_cochain
  exact ⟨s, fun i => (hs i).contDiffOn_of_completeSpace, hsub⟩

end NativeCocycle

/-- Raw native open-cover formulation of the proved additive Cousin
theorem; the inputs are only the cover and its actual holomorphic cocycle. -/
theorem exists_holomorphic_native_cocycle_cochain {ι : Type*} {U : ι → Set ComplexPlane₂}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {h : ι → ι → ComplexPlane₂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x) :
    ∃ s : ι → ComplexPlane₂ → ℂ, (∀ i, AnalyticOnNhd ℂ (s i) (U i)) ∧
      ∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x := by
  let C : NativeCocycle ι := {
    domain := U
    isOpen_domain := hU
    cover := hcover
    transition := h
    holomorphic := hh
    additive := hc }
  exact C.exists_holomorphic_cochain

/-- Native `C^ω` open-cover formulation, with the same original transition
functions and no assumed analytic primitive. -/
theorem exists_contDiff_native_cocycle_cochain {ι : Type*} {U : ι → Set ComplexPlane₂}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {h : ι → ι → ComplexPlane₂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x) :
    ∃ s : ι → ComplexPlane₂ → ℂ, (∀ i, ContDiffOn ℂ ω (s i) (U i)) ∧
      ∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x := by
  obtain ⟨s, hs, hsub⟩ := exists_holomorphic_native_cocycle_cochain hU hcover hh hc
  exact ⟨s, fun i => (hs i).contDiffOn_of_completeSpace, hsub⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin
