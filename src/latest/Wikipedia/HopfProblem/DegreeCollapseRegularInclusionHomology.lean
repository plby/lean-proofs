import Wikipedia.HopfProblem.DegreeCollapseNativeInclusionHomology
import Wikipedia.SmoothSixDPoincare.RegularSublevelDeformation

/-!
# Coherent regular-band homology uses literal sublevel inclusions

Their compositions agree exactly as continuous maps and on homology.
A regular band makes this particular inclusion a homotopy equivalence,
so its actual induced map is bijective. No independently chosen band
homeomorphism is identified with this map.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem sublevelMap_trans (f : M → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (sublevelMap f hbc).comp (sublevelMap f hab) = sublevelMap f (hab.trans hbc) := rfl

theorem sublevelHomologyMap_comp (f : M → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (k : ℕ) :
    (singularHomologyMap (sublevelMap f hbc) k).comp
      (singularHomologyMap (sublevelMap f hab) k) =
        singularHomologyMap (sublevelMap f (hab.trans hbc)) k := by
  rw [← singularHomologyMap_comp, sublevelMap_trans]

theorem regular_sublevel_inclusion_bijective
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Icc a b → x ∉ criticalPoints E f) (k : ℕ) :
    Bijective (singularHomologyMap (sublevelMap f hab) k) := by
  obtain ⟨e, he⟩ := FlowConstruction.exists_regularSublevelHomotopyEquiv hf hab hband
  have hmap : e.toFun = sublevelMap f hab := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (he x)
  have hh := (homotopyEquivHomologyEquiv e k).bijective
  change Bijective (singularHomologyMap e.toFun k) at hh
  rwa [hmap] at hh

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
