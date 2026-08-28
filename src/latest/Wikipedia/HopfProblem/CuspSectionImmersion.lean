import Wikipedia.HopfProblem.CuspSection
import Wikipedia.HopfProblem.ToricComponentImmersion
import Wikipedia.HopfProblem.CoveringImmersion

/-!
# The cusp section is a holomorphic embedded disc

An explicit affine chart makes the section a coordinate-axis inclusion.
This analytic immersion normal form descends through the covering quotient.
Together with the proved closed topological embedding it gives the genuine
holomorphically embedded disc of Proposition 4.7.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

def sectionCoordinateJoin : (ℂ × CoordinateSpace 2) ≃L[ℂ] CoordinateSpace 3 :=
  (ContinuousLinearEquiv.prodComm ℂ ℂ (CoordinateSpace 2)).trans
    (ToricComponent.coordinateJoin 0)

theorem sectionCoordinateJoin_zero (t : ℂ) :
    sectionCoordinateJoin (t, 0) = ![t, 0, 0] := by
  ext i
  fin_cases i <;> rfl

/-- Shift the two constant coordinates of the section to zero. -/
def sectionAmbientChart : OpenPartialHomeomorph Space (CoordinateSpace 3) :=
  (parametrization referenceTriangle).symm.trans
    (Homeomorph.addRight (-(sectionCoordinates 0))).toOpenPartialHomeomorph

theorem sectionAmbientChart_mem_maximalAtlas :
    sectionAmbientChart ∈ IsManifold.maximalAtlas I₃ ω Space := by
  have he : (parametrization referenceTriangle).symm ∈
      IsManifold.maximalAtlas I₃ ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self referenceTriangle)
  apply sectionAmbientChart.mem_maximalAtlas_of_contMDiffOn
  · exact (contDiff_id.add contDiff_const).contMDiff.comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas he).mono inter_subset_left)
  · exact (contMDiffOn_symm_of_mem_maximalAtlas he).comp
      ((contDiff_id.sub contDiff_const).contMDiff.contMDiffOn.mono inter_subset_left)
      (fun _ hz => hz.2)

theorem sectionPoint_mem_sectionAmbientChart (t : ℂ) :
    inclusion referenceTriangle (sectionCoordinates t) ∈ sectionAmbientChart.source := by
  refine ⟨?_, mem_univ _⟩
  change inclusion referenceTriangle (sectionCoordinates t) ∈
    (parametrization referenceTriangle).target
  rw [parametrization_target]
  exact mem_range_self _

theorem sectionAmbientChart_sectionPoint (t : ℂ) :
    sectionAmbientChart (inclusion referenceTriangle (sectionCoordinates t)) =
      sectionCoordinateJoin (t, 0) := by
  change (parametrization referenceTriangle).symm
    (inclusion referenceTriangle (sectionCoordinates t)) + -(sectionCoordinates 0) = _
  have he : (parametrization referenceTriangle).symm
      (inclusion referenceTriangle (sectionCoordinates t)) = sectionCoordinates t :=
    (parametrization referenceTriangle).left_inv (mem_univ _)
  rw [he, sectionCoordinateJoin_zero]
  ext i
  fin_cases i <;> simp [sectionCoordinates]

/-- The section lift has the actual coordinate-axis normal form, with
the other two complex coordinates giving its complement. -/
theorem sectionLift_isImmersionOfComplement (ε : ℝ) :
    Manifold.IsImmersionOfComplement (CoordinateSpace 2) I₁ I₃ ω (sectionLift ε) := by
  intro t
  let hU : Nonempty (tubeOpen (disc ε)) := ⟨sectionLift ε t⟩
  let e := sectionAmbientChart.subtypeRestr hU
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (sectionLift_continuous ε).continuousAt sectionCoordinateJoin
    (chartAt ℂ t) e (mem_chart_source ℂ t) ?_
    (IsManifold.chart_mem_maximalAtlas t)
    (normalCrossing_subtype_chart (tubeOpen (disc ε)) hU sectionAmbientChart
      sectionAmbientChart_mem_maximalAtlas) ?_
  · rw [show e.source = Subtype.val ⁻¹' sectionAmbientChart.source from
      sectionAmbientChart.subtypeRestr_source hU]
    exact sectionPoint_mem_sectionAmbientChart t
  · intro w hw
    have hw' : w ∈ (chartAt ℂ t).target := by
      simpa [OpenPartialHomeomorph.extend] using hw
    have hval : ((chartAt ℂ t).symm w : ℂ) = w := by
      exact (chartAt ℂ (t : ℂ)).subtypeRestr_symm_apply ⟨t⟩ hw'
    change sectionAmbientChart
      (inclusion referenceTriangle (sectionCoordinates ((chartAt ℂ t).symm w))) = _
    rw [sectionAmbientChart_sectionPoint, hval]
    rfl

theorem zeroSection_isImmersionOfComplement
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    Manifold.IsImmersionOfComplement (CoordinateSpace 2) I₁ I₃ ω (zeroSection C ε) := by
  let := tubeAction C (disc ε)
  exact CoveringQuotient.immersion_project (quotientMap_covering C ε hε hε1 hC hR)
    (fun g => tubeTranslate_holomorphic C (disc ε) g.toAdd hC)
    (sectionLift_continuous ε) (sectionLift_isImmersionOfComplement ε)

theorem zeroSection_isImmersion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    Manifold.IsImmersion I₁ I₃ ω (zeroSection C ε) := by
  let := chartedSpace C ε hε hε1 hC hR
  exact (zeroSection_isImmersionOfComplement C ε hε hε1 hC hR).isImmersion

end Wikipedia.HopfProblem.CuspQuotient
