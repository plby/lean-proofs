import Wikipedia.HopfProblem.CuspCentralHomologySpecializationBoundary
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationTwoSection
import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasis

/-!
# Degree-two surjectivity of the actual marked product specialization

The actual boundary classes and actual base-section classes generate the
central fibre's integral degree-two singular homology.  The boundary lift
places the former in the image of the marked product collapse.  Its literal
unit-phase section places the latter in that same image.  This proves
surjectivity of the original continuous specialization map, without assuming
a geometric model or a compatibility statement about its homology map.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse SpecializationModel
open PeriodTorusHigherHomology SingularMayerVietoris

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε1 hC hR in
/-- The actual marked product specialization surjects on integral `H₂`. -/
theorem productCollapse_homologyTwo_surjective :
    Function.Surjective (singularHomologyMap (productCollapse C ε hε) 2) := by
  intro x
  obtain ⟨a, b, hab⟩ := baseTorusH2_generated C ε hε hε1 hC hR x
  change singularHomologyMap (centralBoundaryInclusion C ε hε) 2 a +
    singularHomologyMap (baseTorusSection C ε hε) 2 b = x at hab
  have ha : singularHomologyMap (centralBoundaryInclusion C ε hε) 2 a ∈
      LinearMap.range (singularHomologyMap (productCollapse C ε hε) 2) :=
    boundaryInclusion_homologyTwo_range_le_productCollapse C ε hε hε1 hC hR ⟨a, rfl⟩
  have hb : singularHomologyMap (baseTorusSection C ε hε) 2 b ∈
      LinearMap.range (singularHomologyMap (productCollapse C ε hε) 2) :=
    baseTorusSection_homology_range_le_productCollapse C ε hε 2 ⟨b, rfl⟩
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  refine ⟨c + d, ?_⟩
  rw [map_add, hc, hd]
  exact hab

include hε1 hC hR in
theorem productCollapse_homologyTwo_range :
    LinearMap.range (singularHomologyMap (productCollapse C ε hε) 2) = ⊤ :=
  LinearMap.range_eq_top.mpr (productCollapse_homologyTwo_surjective C ε hε hε1 hC hR)

end Wikipedia.HopfProblem.CuspCentralHomology
