import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusMaps
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationTwo

/-!
# Degree-two specialization surjectivity at the original cusp radius

Holomorphicity supplies an actual smaller admissible radius. The proved
central radius homeomorphism and exact naturality of the product collapse
transport its degree-two surjectivity back to the original central fibre.
Neither a small-drift bound nor a radius-less-than-one assumption is
required at the original radius. The free-source collapse is surjective
on degree-two homology as well, by the genuine product factorization.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction PeriodTorusHigherHomology SingularMayerVietoris
open SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC

/-- The actual product collapse at the original radius surjects on
integral `H₂`, assuming only the original holomorphic cusp data. -/
theorem productCollapse_homologyTwo_surjective_of_holomorphic :
    Function.Surjective (singularHomologyMap (productCollapse C r hr) 2) := by
  obtain ⟨δ, hδ, hδr, hδ1, hRCδ, _hRDδ⟩ :=
    exists_common_frozen_radius C hr (fun i j => (hC i j).continuousOn)
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr.le)
  have he := congrArg (fun f => singularHomologyMap f 2)
    (centralRadiusHomeomorph_comp_productCollapse C r δ hδr.le hC hδ)
  rw [singularHomologyMap_comp] at he
  rw [← he]
  exact (homeomorphHomologyEquiv (centralRadiusHomeomorph C r δ hδr.le hC hδ) 2).surjective.comp
    (productCollapse_homologyTwo_surjective C δ hδ hδ1 hCδ hRCδ)

theorem productCollapse_homologyTwo_range_of_holomorphic :
    LinearMap.range (singularHomologyMap (productCollapse C r hr) 2) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (productCollapse_homologyTwo_surjective_of_holomorphic C r hr hC)

/-- The same surjectivity holds before changing the actual free-source
quotient to marked product-torus coordinates. -/
theorem sourceCollapse_homologyTwo_surjective_of_holomorphic :
    Function.Surjective (singularHomologyMap (sourceCollapse C r hr) 2) := by
  intro x
  obtain ⟨a, ha⟩ := productCollapse_homologyTwo_surjective_of_holomorphic C r hr hC x
  refine ⟨singularHomologyMap ((sourceProductHomeomorph (C 0)).symm :
    C(CompactFibreTorus × ProductTorus 2, SourceModel (C 0))) 2 a, ?_⟩
  change singularHomologyMap ((sourceCollapse C r hr).comp
    ((sourceProductHomeomorph (C 0)).symm :
      C(CompactFibreTorus × ProductTorus 2, SourceModel (C 0)))) 2 a = x at ha
  rw [singularHomologyMap_comp] at ha
  exact ha

theorem sourceCollapse_homologyTwo_range_of_holomorphic :
    LinearMap.range (singularHomologyMap (sourceCollapse C r hr) 2) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (sourceCollapse_homologyTwo_surjective_of_holomorphic C r hr hC)

end Wikipedia.HopfProblem.CuspCentralHomology
