import Wikipedia.HopfProblem.CuspCentralHomologySpecializationRadiusMaps
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationThreeFour

/-!
# Higher specialization surjectivity at the original cusp radius

Holomorphicity supplies a smaller admissible radius. The actual central
radius homeomorphism intertwines the actual specialization maps, so the
proved higher-degree surjectivity at that smaller radius transports to
the original central fibre. The original radius is not required to be
less than one or to satisfy a small-drift estimate.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction PeriodTorusHigherHomology SingularMayerVietoris
open SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC

/-- At the original radius the actual product collapse surjects on all
integral homology groups of degree at least three. -/
theorem productCollapse_homology_three_add_surjective_of_holomorphic (n : ℕ) :
    Function.Surjective (singularHomologyMap (productCollapse C r hr) (n + 3)) := by
  obtain ⟨δ, hδ, hδr, hδ1, hRCδ, _hRDδ⟩ :=
    exists_common_frozen_radius C hr (fun i j => (hC i j).continuousOn)
  have hCδ (i j) : ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ) :=
    (hC i j).mono (Metric.ball_subset_ball hδr.le)
  have he := congrArg (fun f => singularHomologyMap f (n + 3))
    (centralRadiusHomeomorph_comp_productCollapse C r δ hδr.le hC hδ)
  rw [singularHomologyMap_comp] at he
  rw [← he]
  exact (homeomorphHomologyEquiv
    (centralRadiusHomeomorph C r δ hδr.le hC hδ) (n + 3)).surjective.comp
      (productCollapse_homology_three_add_surjective C δ hδ hδ1 hCδ hRCδ n)

theorem productCollapse_homologyThree_surjective_of_holomorphic :
    Function.Surjective (singularHomologyMap (productCollapse C r hr) 3) :=
  productCollapse_homology_three_add_surjective_of_holomorphic C r hr hC 0

theorem productCollapse_homologyFour_surjective_of_holomorphic :
    Function.Surjective (singularHomologyMap (productCollapse C r hr) 4) :=
  productCollapse_homology_three_add_surjective_of_holomorphic C r hr hC 1

theorem productCollapse_homologyThree_range_of_holomorphic :
    LinearMap.range (singularHomologyMap (productCollapse C r hr) 3) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (productCollapse_homologyThree_surjective_of_holomorphic C r hr hC)

theorem productCollapse_homologyFour_range_of_holomorphic :
    LinearMap.range (singularHomologyMap (productCollapse C r hr) 4) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (productCollapse_homologyFour_surjective_of_holomorphic C r hr hC)

/-- The same statement holds for the actual free-source quotient before
the marked product-torus change of coordinates. -/
theorem sourceCollapse_homology_three_add_surjective_of_holomorphic (n : ℕ) :
    Function.Surjective (singularHomologyMap (sourceCollapse C r hr) (n + 3)) := by
  intro x
  obtain ⟨a, ha⟩ :=
    productCollapse_homology_three_add_surjective_of_holomorphic C r hr hC n x
  refine ⟨singularHomologyMap ((sourceProductHomeomorph (C 0)).symm :
    C(CompactFibreTorus × ProductTorus 2, SourceModel (C 0))) (n + 3) a, ?_⟩
  change singularHomologyMap ((sourceCollapse C r hr).comp
    ((sourceProductHomeomorph (C 0)).symm :
      C(CompactFibreTorus × ProductTorus 2, SourceModel (C 0)))) (n + 3) a = x at ha
  rw [singularHomologyMap_comp] at ha
  exact ha

theorem sourceCollapse_homologyThree_surjective_of_holomorphic :
    Function.Surjective (singularHomologyMap (sourceCollapse C r hr) 3) :=
  sourceCollapse_homology_three_add_surjective_of_holomorphic C r hr hC 0

theorem sourceCollapse_homologyFour_surjective_of_holomorphic :
    Function.Surjective (singularHomologyMap (sourceCollapse C r hr) 4) :=
  sourceCollapse_homology_three_add_surjective_of_holomorphic C r hr hC 1

theorem sourceCollapse_homologyThree_range_of_holomorphic :
    LinearMap.range (singularHomologyMap (sourceCollapse C r hr) 3) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (sourceCollapse_homologyThree_surjective_of_holomorphic C r hr hC)

theorem sourceCollapse_homologyFour_range_of_holomorphic :
    LinearMap.range (singularHomologyMap (sourceCollapse C r hr) 4) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (sourceCollapse_homologyFour_surjective_of_holomorphic C r hr hC)

end Wikipedia.HopfProblem.CuspCentralHomology
