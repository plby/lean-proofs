import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Difference
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Overlap

/-!
# Actual arbitrary-cover additive Cousin existence on the affine blowup

The holomorphic difference of the two affine cochains is split using the
actual blowup transition. Subtracting these two entire chart corrections
makes the local cochains agree, so they glue to actual holomorphic maps
on every member of the original open cover.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1

open AffineBlowup ToricCharts

namespace Cocycle

variable {ι : Type} (C : Cocycle ι)

theorem exists_holomorphic_cochain :
    ∃ s : ι → Space → ℂ,
      (∀ i, ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω (s i) (C.domain i)) ∧
      ∀ i j x, x ∈ C.domain i → x ∈ C.domain j →
        s i x - s j x = C.transition i j x := by
  obtain ⟨a, ha, heq⟩ := exists_holomorphic_overlap_split C.overlapDifference_analytic
  let v : ι → Bool → ℂ × ℂ → ℂ := fun i b q => C.chartCochain b i q - a b q
  have hcompat (i : ι) : CompatibleOn (C.domain i) (v i) := by
    apply compatibleOn_of_cross
    intro q hq hi
    have hsplit : a false q - a true (cross q) =
        C.chartCochain false i q - C.chartCochain true i (cross q) :=
      (heq q hq).trans (C.overlapDifference_eq i q hq hi)
    change C.chartCochain false i q - a false q =
      C.chartCochain true i (cross q) - a true (cross q)
    linear_combination -hsplit
  have hhol (i : ι) (b : Bool) :
      AnalyticOnNhd ℂ (v i b) (chartMap b ⁻¹' C.domain i) :=
    (C.chartCochain_analytic b i).sub ((ha b).mono (subset_univ _))
  refine ⟨fun i => chartGlue (v i),
    fun i => chartGlue_contMDiffOn (C.isOpen_domain i) (v i) (hcompat i) (hhol i), ?_⟩
  intro i j x hi hj
  obtain ⟨b, q, rfl⟩ := chartMap_jointly_surjective x
  change chartGlue (v i) (chartMap b q) - chartGlue (v j) (chartMap b q) = _
  rw [chartGlue_chartMap (v i) (hcompat i) b q hi,
    chartGlue_chartMap (v j) (hcompat j) b q hj]
  change (C.chartCochain b i q - a b q) - (C.chartCochain b j q - a b q) = _
  calc
    _ = C.chartCochain b i q - C.chartCochain b j q := by ring
    _ = _ := C.chartCochain_sub b i j q hi hj

end Cocycle

/-- The raw actual open-cover formulation, with no chartwise or global
cochain among the assumptions. -/
theorem exists_holomorphic_cocycle_cochain {ι : Type} {U : ι → Set Space}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {h : ι → ι → Space → ℂ}
    (hh : ∀ i j, ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x) :
    ∃ s : ι → Space → ℂ,
      (∀ i, ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω (s i) (U i)) ∧
      ∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x := by
  let C : Cocycle ι := {
    domain := U
    isOpen_domain := hU
    cover := hcover
    transition := h
    holomorphic := hh
    additive := hc }
  exact C.exists_holomorphic_cochain

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1
