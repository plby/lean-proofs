import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Gluing
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinGlobal

/-!
# Actual local cocycles and their two chartwise solutions

The original cover is arbitrary. Its inverse image in either actual
affine chart is an arbitrary open cover of `ℂ²`, so the proved affine
Cousin theorem supplies chartwise local holomorphic cochains.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1

open AffineBlowup ToricCharts

structure Cocycle (ι : Type) where
  domain : ι → Set Space
  isOpen_domain : ∀ i, IsOpen (domain i)
  cover : ∀ x : Space, ∃ i, x ∈ domain i
  transition : ι → ι → Space → ℂ
  holomorphic : ∀ i j, ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω
    (transition i j) (domain i ∩ domain j)
  additive : ∀ i j k x, x ∈ domain i → x ∈ domain j → x ∈ domain k →
    transition i j x + transition j k x = transition i k x

namespace Cocycle

variable {ι : Type} (C : Cocycle ι)

theorem exists_chart_cochain (b : Bool) :
    ∃ s : ι → ℂ × ℂ → ℂ,
      (∀ i, AnalyticOnNhd ℂ (s i) (chartMap b ⁻¹' C.domain i)) ∧
      ∀ i j q, chartMap b q ∈ C.domain i → chartMap b q ∈ C.domain j →
        s i q - s j q = C.transition i j (chartMap b q) := by
  apply PeriodTorusLineBundleClassificationCousin.exists_holomorphic_cocycle_cochain
    (U := fun i => chartMap b ⁻¹' C.domain i)
    (h := fun i j => C.transition i j ∘ chartMap b)
  · exact fun i => (C.isOpen_domain i).preimage (chartMap_continuous b)
  · exact fun q => C.cover (chartMap b q)
  · intro i j
    simpa only [preimage_inter] using analyticOnNhd_comp_chartMap
      ((C.isOpen_domain i).inter (C.isOpen_domain j)) (C.holomorphic i j) b
  · intro i j k q hi hj hk
    exact C.additive i j k (chartMap b q) hi hj hk

/-- Choose from the proved affine Cousin theorem on each chart. -/
def chartCochain (b : Bool) : ι → ℂ × ℂ → ℂ := (C.exists_chart_cochain b).choose

theorem chartCochain_analytic (b : Bool) (i : ι) :
    AnalyticOnNhd ℂ (C.chartCochain b i) (chartMap b ⁻¹' C.domain i) :=
  (C.exists_chart_cochain b).choose_spec.1 i

theorem chartCochain_sub (b : Bool) (i j : ι) (q : ℂ × ℂ)
    (hi : chartMap b q ∈ C.domain i) (hj : chartMap b q ∈ C.domain j) :
    C.chartCochain b i q - C.chartCochain b j q = C.transition i j (chartMap b q) :=
  (C.exists_chart_cochain b).choose_spec.2 i j q hi hj

end Cocycle

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1
