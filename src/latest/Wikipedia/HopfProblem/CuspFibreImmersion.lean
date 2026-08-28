import Wikipedia.HopfProblem.CuspSubmersion
import Wikipedia.HopfProblem.CoveringImmersion
import Wikipedia.HopfProblem.ExponentialCharts

/-!
# The nonzero fibres are embedded complex submanifolds

The exponential uniformization is locally a coordinate-hyperplane inclusion.
This normal form descends through both covering quotients, so that the already
constructed maps from the period tori are genuine holomorphic immersions.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem

namespace DiscreteQuotient

variable {E F E' M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace M] [ChartedSpace E' M]
    (L : Submodule ℤ E) [DiscreteTopology L]

/-- An immersion descends through a discrete-translation covering on its source.
The source charts are the actual local inverses of the lattice quotient. -/
theorem immersion_of_comp_mkQ {f : E ⧸ L → M} (hc : Continuous f)
    (hf : Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω (f ∘ L.mkQ)) :
    Manifold.IsImmersionOfComplement F (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E') ω f := by
  intro x
  let c := chart L x
  let hi := hf (c x)
  let d := c.trans hi.domChart
  have hcM : c ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ E) ω (E ⧸ L) :=
    IsManifold.chart_mem_maximalAtlas x
  have hcx : x ∈ c.source := mem_chart_source E x
  have hqx : L.mkQ (c x) = x := mkQ_chart L x x hcx
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt hc.continuousAt
    hi.equiv d hi.codChart ⟨hcx, hi.mem_domChart_source⟩ ?_ ?_
    hi.codChart_mem_maximalAtlas ?_
  · simpa only [Function.comp_apply, hqx] using hi.mem_codChart_source
  · apply d.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas hi.domChart_mem_maximalAtlas).comp
        ((contMDiffOn_of_mem_maximalAtlas hcM).mono inter_subset_left) (fun _ hw => hw.2)
    · exact (contMDiffOn_symm_of_mem_maximalAtlas hcM).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas hi.domChart_mem_maximalAtlas).mono inter_subset_left)
        (fun _ hw => hw.2)
  · intro w hw
    have hw' : w ∈ d.target := by simpa [OpenPartialHomeomorph.extend] using hw
    change hi.codChart (f (c.symm (hi.domChart.symm w))) = hi.equiv (w, 0)
    rw [show (c.symm : E → E ⧸ L) = L.mkQ from chart_symm L x]
    exact hi.writtenInCharts (by simpa [OpenPartialHomeomorph.extend] using hw'.1)

end DiscreteQuotient

namespace CuspUniformization

open ToricCharts ToricFan ToricSpace CuspQuotient

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

/-- Splitting the first two coordinates off from the transverse cusp parameter. -/
def fibreCoordinateJoin : (ComplexPlane₂ × ℂ) ≃L[ℂ] CoordinateSpace 3 :=
  (ContinuousLinearEquiv.prodComm ℂ ComplexPlane₂ ℂ).trans coordinateSplit.symm

@[simp] theorem fibreCoordinateJoin_apply (z : ComplexPlane₂) (t : ℂ) :
    fibreCoordinateJoin (z, t) = ![z 0, z 1, t] := rfl

/-- Translate the base coordinate so that the fibre over `t` is a linear
coordinate hyperplane. -/
def fibreCoordinateShift (t : ℂ) : (CoordinateSpace 3) ≃ₜ (CoordinateSpace 3) :=
  Homeomorph.addRight (- ![0, 0, t])

theorem fibreCoordinateShift_holomorphic (t : ℂ) :
    ContMDiff I₃ I₃ ω (fibreCoordinateShift t) :=
  (contDiff_id.add contDiff_const).contMDiff

theorem fibreCoordinateShift_symm_holomorphic (t : ℂ) :
    ContMDiff I₃ I₃ ω (fibreCoordinateShift t).symm :=
  (contDiff_id.sub contDiff_const).contMDiff

def tubeFibreChart (D : TopologicalSpace.Opens ℂ) (hD : Nonempty (Tube D)) (t : ℂ) :
    OpenPartialHomeomorph (Tube D) (CoordinateSpace 3) :=
  (tubeTorusChart D hD).trans (fibreCoordinateShift t).toOpenPartialHomeomorph

theorem tubeFibreChart_mem_maximalAtlas (D : TopologicalSpace.Opens ℂ)
    (hD : Nonempty (Tube D)) (t : ℂ) :
    tubeFibreChart D hD t ∈ IsManifold.maximalAtlas I₃ ω (Tube D) := by
  apply (tubeFibreChart D hD t).mem_maximalAtlas_of_contMDiffOn
  · exact (fibreCoordinateShift_holomorphic t).comp_contMDiffOn
      ((tubeTorusChart_holomorphic D hD).mono inter_subset_left)
  · exact (tubeTorusChart_symm_holomorphic D hD).comp
      ((fibreCoordinateShift_symm_holomorphic t).contMDiffOn.mono inter_subset_left)
      (fun _ hw => hw.2)

variable (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε)

theorem exponentialLift_mem_tubeFibreChart_source (hD : Nonempty (Tube (disc ε)))
    (z : ComplexPlane₂) :
    exponentialLift ε s hs z ∈ (tubeFibreChart (disc ε) hD (exponential s)).source := by
  refine ⟨?_, mem_univ _⟩
  change exponentialLift ε s hs z ∈ (tubeTorusChart (disc ε) hD).source
  rw [tubeTorusChart_source]
  exact exponentialPoint_mem (exponential_ne_zero s) z

theorem tubeFibreChart_exponentialLift (hD : Nonempty (Tube (disc ε)))
    (z : ComplexPlane₂) :
    tubeFibreChart (disc ε) hD (exponential s) (exponentialLift ε s hs z) =
      fibreCoordinateJoin ((fun i => exponential (z i)), 0) := by
  change torusCoordinates (exponentialPoint (exponential s) z) +
    - ![0, 0, exponential s] = _
  rw [torusCoordinates_exponentialPoint (exponential_ne_zero s), fibreCoordinateJoin_apply]
  ext i
  fin_cases i <;> simp [exponentialCoordinates]

private theorem exponentialLift_isImmersionAt_of_chart (z : ComplexPlane₂)
    (e : OpenPartialHomeomorph ComplexPlane₂ ComplexPlane₂) (hz : z ∈ e.source)
    (he : e ∈ IsManifold.maximalAtlas I₂ ω ComplexPlane₂)
    (heq : ∀ w, e w = fun i => exponential (w i)) :
    Manifold.IsImmersionAtOfComplement ℂ I₂ I₃ ω (exponentialLift ε s hs) z := by
  let hD : Nonempty (Tube (disc ε)) := ⟨exponentialLift ε s hs z⟩
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (exponentialLift_continuous ε s hs).continuousAt fibreCoordinateJoin e
    (tubeFibreChart (disc ε) hD (exponential s)) hz
    (exponentialLift_mem_tubeFibreChart_source ε s hs hD z) he
    (tubeFibreChart_mem_maximalAtlas (disc ε) hD (exponential s)) ?_
  intro w hw
  have hw' : w ∈ e.target := by simpa [OpenPartialHomeomorph.extend] using hw
  change tubeFibreChart (disc ε) hD (exponential s)
    (exponentialLift ε s hs (e.symm w)) = fibreCoordinateJoin (w, 0)
  rw [tubeFibreChart_exponentialLift]
  have hwexp : (fun i => exponential (e.symm w i)) = w :=
    (heq (e.symm w)).symm.trans (e.right_inv hw')
  rw [hwexp]

/-- Before the twisted quotient, exponential uniformization is an analytic
immersion with the cusp direction as its one-dimensional complement. -/
theorem exponentialLift_isImmersionOfComplement :
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω (exponentialLift ε s hs) := by
  intro z
  exact exponentialLift_isImmersionAt_of_chart ε s hs z (exponentialChart z)
    (mem_exponentialChart_source z) (exponentialChart_mem_maximalAtlas z)
    (fun w => exponentialChart_apply z w)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

theorem fibreCover_isImmersionOfComplement :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω (fibreCover C ε s hs) := by
  let := tubeAction C (disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact CoveringQuotient.immersion_project (quotientMap_covering C ε hε hε1 hC hR)
    (fun g => tubeTranslate_holomorphic C (disc ε) g.toAdd hC)
    (exponentialLift_continuous ε s hs) (exponentialLift_isImmersionOfComplement ε s hs)

variable (hlog : Real.log ‖exponential s‖ < 0)
    (hRp : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)

/-- The actual full-period torus map is an immersion for the quotient complex
structures on both its source and target. -/
theorem fibreMap_isImmersionOfComplement :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω (fibreMap C ε s hs hlog hRp) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply DiscreteQuotient.immersion_of_comp_mkQ (periodData C s hlog hRp).lattice
    (fibreMap_continuous C ε s hs hlog hRp)
  exact fibreCover_isImmersionOfComplement ε s hs C hε hε1 hC hR

theorem fibreMap_isImmersion :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Manifold.IsImmersion I₂ I₃ ω (fibreMap C ε s hs hlog hRp) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact (fibreMap_isImmersionOfComplement ε s hs C hε hε1 hC hR hlog hRp).isImmersion

/-- Every nonzero cusp fibre is the image of its compact period torus by an
analytic immersion that is also a topological embedding. -/
theorem nonzero_fibre_embedded_torus {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ∃ p : FullPeriodMatrix, ∃ f : p.Torus → QuotientSpace C ε,
      Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω f ∧
      IsEmbedding f ∧ range f = projection C ε ⁻¹' {t} := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let s := logarithm t
  have hst : exponential s = t := exponential_logarithm ht0
  have hs : ‖exponential s‖ < ε := by simpa only [hst] using ht
  have hpos : 0 < ‖exponential s‖ := norm_pos_iff.mpr (exponential_ne_zero s)
  have hlog := Real.log_neg hpos (hs.trans hε1)
  have hRp := hR _ hpos hs
  refine ⟨periodData C s hlog hRp, fibreMap C ε s hs hlog hRp,
    fibreMap_isImmersionOfComplement ε s hs C hε hε1 hC hR hlog hRp,
    fibreMap_isEmbedding C ε s hs hlog hRp hε hε1 hC hR, ?_⟩
  simpa only [hst] using fibreMap_range C ε s hs hlog hRp

end CuspUniformization

end Wikipedia.HopfProblem
