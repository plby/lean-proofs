import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyAction
import Wikipedia.HopfProblem.CoveringSubmersion

/-!
# The actual iterated cusp-family quotient

Starting with the varying-period quotient by the four-dimensional lattice,
we take the genuine orbit quotient by clockwise integer monodromy.  Its
analytic charts are lifts through this second covering, and the projection
to the punctured disc is a holomorphic submersion.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspFamily.Data

open CuspUniformization

/-- The genuine integer-monodromy quotient of the actual period family. -/
def Space (D : CuspFamily.Data) : Type :=
  @MulAction.orbitRel.Quotient (Multiplicative ℤ) D.TotalSpace _ D.totalAction

variable (D : CuspFamily.Data)

instance spaceTopology : TopologicalSpace D.Space :=
  inferInstanceAs (TopologicalSpace
    (@MulAction.orbitRel.Quotient (Multiplicative ℤ) D.TotalSpace _ D.totalAction))

def quotient : D.TotalSpace → D.Space := by
  let := D.totalAction
  exact Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) D.TotalSpace)

theorem quotient_surjective : Function.Surjective D.quotient := Quotient.mk_surjective

theorem quotient_continuous : Continuous D.quotient := continuous_quotient_mk'

theorem quotient_eq_iff (x y : D.TotalSpace) :
    letI := D.totalAction
    D.quotient x = D.quotient y ↔ ∃ k : Multiplicative ℤ, k • y = x := Quotient.eq''

@[simp] theorem quotient_smul (k : Multiplicative ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    D.quotient (k • x) = D.quotient x := by
  let := D.totalAction
  exact (D.quotient_eq_iff _ _).mpr ⟨k, rfl⟩

/-- The descended exponential projection to the actual punctured disc. -/
def projection : D.Space → puncturedDisc D.radius := by
  let := logBaseAction D.radius
  let := D.totalAction
  exact Quotient.lift (fun x : D.TotalSpace => baseExponential D.radius x.1) (by
    rintro x y ⟨k, hk⟩
    rw [← hk]
    exact baseExponential_smul D.radius k y.1)

@[simp] theorem projection_quotient (x : D.TotalSpace) :
    D.projection (D.quotient x) = baseExponential D.radius x.1 := rfl

theorem projection_surjective : Function.Surjective D.projection := by
  intro t
  obtain ⟨s, rfl⟩ := baseExponential_surjective D.radius t
  exact ⟨D.quotient (s, 0), rfl⟩

/-- Disjoint logarithmic base sheets provide disjoint sheets for the
entire period family, not just for each individual torus. -/
theorem quotientCoveringMap :
    letI := D.totalAction
    IsQuotientCoveringMap D.quotient (Multiplicative ℤ) := by
  let := logBaseAction D.radius
  let := D.totalAction
  let := D.totalAction_continuous
  refine
    { toIsQuotientMap := isQuotientMap_quotient_mk'
      continuous_const_smul := continuous_const_smul
      apply_eq_iff_mem_orbit := Quotient.eq''
      disjoint := ?_ }
  intro x
  obtain ⟨U, hU, hd⟩ := (baseExponential_covering D.radius).disjoint x.1
  refine ⟨Prod.fst ⁻¹' U, continuous_fst.continuousAt hU, ?_⟩
  rintro k ⟨z, ⟨w, hw, rfl⟩, hz⟩
  exact hd k ⟨k • w.1, ⟨w.1, hw, rfl⟩, hz⟩

/-- The natural second covering atlas, selected after the actual period
family atlas. -/
@[instance_reducible] def chartedSpace : ChartedSpace (ℂ × ComplexPlane₂) D.Space := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  exact CoveringQuotient.chartedSpace (E := ℂ × ComplexPlane₂) D.quotientCoveringMap

theorem isManifold :
    letI := D.chartedSpace
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.Space := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.isManifold D.quotientCoveringMap ω D.totalAction_holomorphic

theorem quotient_holomorphic :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.contMDiff_project D.quotientCoveringMap ω D.totalAction_holomorphic

theorem quotient_isLocalDiffeomorph :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.project_isLocalDiffeomorph D.quotientCoveringMap
    D.totalAction_holomorphic

theorem projection_holomorphic :
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ ℂ) ω D.projection := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  apply CoveringQuotient.contMDiff_of_comp D.quotientCoveringMap
    (modelWithCornersSelf ℂ ℂ) ω
  exact (baseExponential_holomorphic D.radius).comp D.periods.projection_holomorphic

theorem projection_submersion :
    letI := D.chartedSpace
    Manifold.IsSubmersionOfComplement ComplexPlane₂
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
      D.projection := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace
  let := D.isManifold
  exact submersion_of_localDiffeomorph_square D.quotient_isLocalDiffeomorph
    (baseExponential_isLocalDiffeomorph D.radius) D.quotient_surjective
    D.periods.projection_submersion D.projection_quotient

/-- Both actual quotient operations, applied to the original logarithmic
vector cover. -/
def iteratedCover : LogCover D.radius → D.Space := D.quotient ∘ D.familyCover

theorem iteratedCover_surjective : Function.Surjective D.iteratedCover :=
  D.quotient_surjective.comp D.familyCover_surjective

theorem iteratedCover_holomorphic :
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.iteratedCover := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace
  exact D.quotient_holomorphic.comp D.familyCover_holomorphic

theorem iteratedCover_isLocalDiffeomorph :
    letI := D.chartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.iteratedCover := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace
  intro x
  exact (D.familyCover_isLocalDiffeomorph x).comp
    (K := modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (P := D.Space)
    (D.quotient_isLocalDiffeomorph (D.familyCover x))

@[simp] theorem projection_iteratedCover (x : LogCover D.radius) :
    (D.projection (D.iteratedCover x) : ℂ) = exponential x.1.1 := rfl

end Wikipedia.HopfProblem.SpecialPeriods.CuspFamily.Data
