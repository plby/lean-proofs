import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeDifferential
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeInclusion
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeHolomorphic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedCoordinates

/-!
# The genuine holomorphic kernel in the original three-dimensional atlas

The native differential kills the actual holomorphic sections.  Conversely,
its vanishing gives the actual Cauchy--Riemann equations in each original
chart, hence genuine joint analyticity and the original holomorphic section.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

section Inclusion

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem chartFunction_inclusion_contDiffAt (U : Opens M)
    (s : Functions.HolomorphicSection E M U) (x : U) :
    ContDiffAt ℂ ω (chartFunction E M U (Functions.inclusionSection E M U s) x)
      (chartAt E (x : M) (x : M)) := by
  have h := Functions.extend_inclusion_contMDiffAt E M U s x x.property
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt] at h
  simpa [chartFunction, extChartAt, OpenPartialHomeomorph.extend,
    contDiffWithinAt_univ] using h

/-- The original holomorphic inclusion is killed by the actual native differential. -/
theorem differentialSection_inclusion (U : Opens M)
    (s : Functions.HolomorphicSection E M U) :
    differentialSection E M U (Functions.inclusionSection E M U s) = 0 := by
  apply Forms.FormSection.ext E M
  intro x
  change Forms.covectorAsModel E M
    (formOfSmooth E M U (Functions.inclusionSection E M U s) x) = 0
  rw [formOfSmooth_eq_chart_dbar]
  exact dbar_zero_of_differentiableAt
    ((chartFunction_inclusion_contDiffAt E M U s x).differentiableAt (by simp))

theorem inclusion_differential : Functions.inclusion E M ≫ differential E M = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext (differentialSection_inclusion E M U.unop)

end Inclusion

variable (M : Type) [TopologicalSpace M] [ChartedSpace Model M]
  [IsManifold 𝓘(ℂ, Model) ω M] [IsManifold 𝓘(ℝ, Model) ∞ M]

/-- In every original chart, a zero native differential gives the actual
zero antiholomorphic Fréchet derivative of the literal chart function. -/
theorem chartFunction_dbar_zero (U : Opens M) (s : Functions.SmoothSection Model M U)
    (hs : differentialSection Model M U s = 0) (x₀ : M) (z : Model)
    (hz : z ∈ ClosedForms.coordinateDomain Model M U x₀) :
    dbar (chartFunction Model M U s x₀) z = 0 := by
  let x : U := ⟨(chartAt Model x₀).symm z, hz.2⟩
  have hsrc : (x : M) ∈ (chartAt Model x₀).source :=
    (chartAt Model x₀).map_target hz.1
  have h := differentialSection_inCoordinates Model M U s x₀ x hsrc
  have hchart : chartAt Model x₀ (x : M) = z := (chartAt Model x₀).right_inv hz.1
  rw [hchart] at h
  rw [← h, hs]
  apply ContinuousLinearMap.ext
  intro v
  rw [Forms.inCoordinates_apply]
  rfl

/-- The literal chart function is jointly analytic on its entire
original chart domain, not only separately along fibre slices. -/
theorem chartFunction_analyticOnNhd (U : Opens M) (s : Functions.SmoothSection Model M U)
    (hs : differentialSection Model M U s = 0) (x₀ : M) :
    AnalyticOnNhd ℂ (chartFunction Model M U s x₀)
      (ClosedForms.coordinateDomain Model M U x₀) := by
  apply analyticOnNhd_of_dbar_zero (ClosedForms.coordinateDomain Model M U x₀).isOpen
  · intro z hz
    exact (chartFunction_contDiffAt Model M U s x₀ z hz.1 hz.2).differentiableAt
      (by simp) |>.differentiableWithinAt
  · exact chartFunction_dbar_zero M U s hs x₀

/-- Vanishing of the actual differential makes the actual original
ambient representative holomorphic at every point of its original domain. -/
theorem holomorphicAt_of_differential_zero (U : Opens M)
    (s : Functions.SmoothSection Model M U) (hs : differentialSection Model M U s = 0)
    (x : M) (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℂ, Model) 𝓘(ℂ, ℂ) ω (Functions.extend Model M U s) x := by
  have ha := (chartFunction_analyticOnNhd M U s hs x) (chartAt Model x x)
    (ClosedForms.mem_coordinateDomain_self Model M U x hx)
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt]
  simpa [chartFunction, extChartAt, OpenPartialHomeomorph.extend,
    contDiffWithinAt_univ] using ha.contDiffAt

/-- Every actual smooth section in the true kernel has an original
holomorphic preimage on that same whole open set, with identical values. -/
theorem exists_holomorphic_preimage (U : Opens M) (s : Functions.SmoothSection Model M U)
    (hs : differentialSection Model M U s = 0) :
    ∃ f : Functions.HolomorphicSection Model M U,
      Functions.inclusionSection Model M U f = s := by
  let f : Functions.HolomorphicSection Model M U :=
    ⟨fun x => Functions.extend Model M U s x,
      fun x => contMDiffAt_subtype_iff.mpr
        (holomorphicAt_of_differential_zero M U s hs x x.property)⟩
  refine ⟨f, ContMDiffMap.ext fun x => ?_⟩
  exact Functions.extend_apply Model M U s x x.property

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential
