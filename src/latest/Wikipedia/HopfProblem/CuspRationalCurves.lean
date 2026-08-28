import Wikipedia.HopfProblem.CuspCurveSphere
import Wikipedia.HopfProblem.RiemannSphere
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The analytic projective-line structures of the double curves

Each double curve, with its actual subspace topology, has the analytic atlas
given by its two affine axis parametrizations. The sphere homeomorphism is
holomorphic in both directions for this atlas, and the inclusion into the
constructed cusp threefold is holomorphic.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace ToricFan Triangle

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

@[instance_reducible] def curveChartedSpace (i : Fin 3) :
    ChartedSpace ℂ (doubleCurve C ε hε i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact (curveCharts C ε hε i).chartedSpace

theorem curve_isManifold (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    IsManifold (modelWithCornersSelf ℂ ℂ) ω (doubleCurve C ε hε i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact (curveCharts C ε hε i).isManifold

theorem curveSphereHomeomorph_holomorphic (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (curveSphereHomeomorph C ε hε hε1 hC hR i) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact RiemannSphere.homeomorph_holomorphic (curveCharts C ε hε i)

theorem curveSphereHomeomorph_symm_holomorphic (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (curveSphereHomeomorph C ε hε hε1 hC hR i).symm := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact RiemannSphere.homeomorph_symm_holomorphic (curveCharts C ε hε i)

/-- The actual double curve is biholomorphic to the standard analytic sphere. -/
def curveBiholomorph (i : Fin 3) :
    letI := curveChartedSpace C ε hε hε1 hC hR i
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      RiemannSphere (doubleCurve C ε hε i) ω := by
  let := curveChartedSpace C ε hε hε1 hC hR i
  exact {
    toEquiv := (curveSphereHomeomorph C ε hε hε1 hC hR i).toEquiv
    contMDiff_toFun := curveSphereHomeomorph_holomorphic C ε hε hε1 hC hR i
    contMDiff_invFun := curveSphereHomeomorph_symm_holomorphic C ε hε hε1 hC hR i }

theorem curve_inclusion_holomorphic (i : Fin 3) :
    letI := chartedSpace C ε hε hε1 hC hR
    letI := curveChartedSpace C ε hε hε1 hC hR i
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (Subtype.val : doubleCurve C ε hε i → QuotientSpace C ε) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  let := chartedSpace C ε hε hε1 hC hR
  let := curveChartedSpace C ε hε hε1 hC hR i
  apply (curveCharts C ε hε i).contMDiff_of_comp_affineMaps
    (modelWithCornersSelf ℂ (CoordinateSpace 3))
  intro b
  cases b
  · exact axisMap_holomorphic C ε hε hε1 hC hR referenceTriangle i
  · exact axisMap_holomorphic C ε hε hε1 hC hR (upperNeighbour i) i

def sphereParametrization (i : Fin 3) (z : RiemannSphere) : QuotientSpace C ε :=
  curveSphereHomeomorph C ε hε hε1 hC hR i z

theorem sphereParametrization_holomorphic (i : Fin 3) :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω
      (sphereParametrization C ε hε hε1 hC hR i) := by
  let := chartedSpace C ε hε hε1 hC hR
  let := curveChartedSpace C ε hε hε1 hC hR i
  exact (curve_inclusion_holomorphic C ε hε hε1 hC hR i).comp
    (curveSphereHomeomorph_holomorphic C ε hε hε1 hC hR i)

theorem sphereParametrization_isEmbedding (i : Fin 3) :
    IsEmbedding (sphereParametrization C ε hε hε1 hC hR i) :=
  IsEmbedding.subtypeVal.comp (curveSphereHomeomorph C ε hε hε1 hC hR i).isEmbedding

theorem sphereParametrization_range (i : Fin 3) :
    range (sphereParametrization C ε hε hε1 hC hR i) = doubleCurve C ε hε i := by
  apply subset_antisymm
  · rintro _ ⟨z, rfl⟩
    exact (curveSphereHomeomorph C ε hε hε1 hC hR i z).2
  · intro x hx
    obtain ⟨z, hz⟩ := (curveSphereHomeomorph C ε hε hε1 hC hR i).surjective ⟨x, hx⟩
    exact ⟨z, congrArg Subtype.val hz⟩

end Wikipedia.HopfProblem.CuspQuotient
