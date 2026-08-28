import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinCorrection
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationGlobalDbar

/-!
# Genuine additive Cousin existence on two-dimensional complex space

The actual subordinate-partition cochain produces a globally smooth closed
antiholomorphic forcing form.  The proved unrestricted global primitive
theorem supplies one common correction.  Subtracting it yields holomorphic
local functions with the original transition cocycle, on the original
arbitrary open cover.  A global solver is not an additional hypothesis.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin

open PeriodTorusLineBundleClassification

namespace Cocycle

variable {ι : Type*} (C : Cocycle ι)

/-- Every actual holomorphic additive cocycle on an arbitrary open cover
of `ℂ × ℂ` is the coboundary of genuine holomorphic local functions. -/
theorem exists_holomorphic_cochain :
    ∃ s : ι → ℂ × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (s i) (C.domain i)) ∧
      ∀ i j x, x ∈ C.domain i → x ∈ C.domain j → s i x - s j x = C.transition i j x := by
  obtain ⟨u, hu, h₁, h₂⟩ := exists_smooth_global_dbar_primitive
    C.forcingFirst_contDiff C.forcingSecond_contDiff C.forcing_isDbarClosed
  exact ⟨C.correctedCochain u, C.correctedCochain_analyticOnNhd hu h₁ h₂,
    fun i j _ hi hj => C.correctedCochain_sub u i j hi hj⟩

end Cocycle

/-- Open-cover formulation, with no constructed cochain or global
antiholomorphic primitive among the input assumptions. -/
theorem exists_holomorphic_cocycle_cochain {ι : Type*} {U : ι → Set (ℂ × ℂ)}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {h : ι → ι → ℂ × ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x) :
    ∃ s : ι → ℂ × ℂ → ℂ, (∀ i, AnalyticOnNhd ℂ (s i) (U i)) ∧
      ∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x := by
  let C : Cocycle ι := {
    domain := U
    isOpen_domain := hU
    cover := hcover
    transition := h
    holomorphic := hh
    additive := hc }
  exact C.exists_holomorphic_cochain

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin
