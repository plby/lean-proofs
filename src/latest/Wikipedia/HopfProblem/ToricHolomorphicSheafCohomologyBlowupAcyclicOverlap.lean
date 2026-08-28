import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Charts
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyChartsIncidence
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyPuncturedDbarOneDomains

/-!
# The actual overlap of the two incidence blowup charts

The literal product chart in either incidence chart identifies the actual
intersection with `ℂ × ℂ*`. Both directions use the existing chart maps and
coordinates, and their transition is the actual blowup transition
`(z,w) ↦ (z*w,w⁻¹)`.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupAcyclic

open AffineBlowup ToricCharts

/-- The actual punctured product, with its inherited open-submanifold structure. -/
def puncturedOpen : Opens (ℂ × ℂ) :=
  ⟨PuncturedDbarOne.domain, PuncturedDbarOne.isOpen_domain⟩

/-- The literal intersection of the two incidence-model affine opens. -/
def overlapOpen : Opens Space := Charts.incidenceOpen false ⊓ Charts.incidenceOpen true

theorem overlap_mem_target (b : Bool) {x : Space} (hx : x ∈ overlapOpen) :
    x ∈ affineTarget b := by
  cases b
  · exact hx.1
  · exact hx.2

/-- Membership in the other chart is exactly nonvanishing of the slope. -/
theorem chartMap_mem_other_iff (b : Bool) (q : ℂ × ℂ) :
    BlowupH1.chartMap b q ∈ affineTarget (!b) ↔ q.2 ≠ 0 := by
  constructor
  · intro hq
    exact ((BlowupH1.chartMap_cross_eq_iff b q
      (BlowupH1.chartCoords (!b) (BlowupH1.chartMap b q))).mp
        (BlowupH1.chartMap_chartCoords (!b) _ hq).symm).1
  · intro hq
    rw [← BlowupH1.chartMap_cross b q hq]
    exact BlowupH1.chartMap_mem_target (!b) _

theorem chartMap_mem_overlap (b : Bool) (q : ℂ × ℂ) (hq : q.2 ≠ 0) :
    BlowupH1.chartMap b q ∈ overlapOpen := by
  have h₁ := BlowupH1.chartMap_mem_target b q
  have h₂ := (chartMap_mem_other_iff b q).mpr hq
  cases b
  · exact ⟨h₁, h₂⟩
  · exact ⟨h₂, h₁⟩

theorem chartCoords_overlap_nonzero (b : Bool) (x : Space) (hx : x ∈ overlapOpen) :
    (BlowupH1.chartCoords b x).2 ≠ 0 := by
  apply (chartMap_mem_other_iff b _).mp
  rw [BlowupH1.chartMap_chartCoords b x (overlap_mem_target b hx)]
  exact overlap_mem_target (!b) hx

/-- Either actual product chart is a genuine analytic biholomorphism
from `ℂ × ℂ*` onto the actual incidence-chart intersection. -/
def overlapBiholomorph (b : Bool) :
    Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2)
      puncturedOpen overlapOpen ω where
  toEquiv :=
    { toFun q := ⟨BlowupH1.chartMap b q, chartMap_mem_overlap b q q.property⟩
      invFun x := ⟨BlowupH1.chartCoords b x, chartCoords_overlap_nonzero b x x.property⟩
      left_inv q := Subtype.ext (BlowupH1.chartCoords_chartMap b q)
      right_inv x := Subtype.ext
        (BlowupH1.chartMap_chartCoords b x (overlap_mem_target b x.property)) }
  contMDiff_toFun q := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact ((BlowupH1.chartMap_holomorphic b).comp contMDiff_subtype_val) q
  contMDiff_invFun x := by
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    apply (contMDiffAt_subtype_iff (f := BlowupH1.chartCoords b) (x := x)).mpr
    exact (BlowupH1.chartCoords_holomorphicOn b).contMDiffAt
      ((affineTarget_isOpen b).mem_nhds (overlap_mem_target b x.property))

@[simp] theorem overlapBiholomorph_apply (b : Bool) (q : puncturedOpen) :
    (overlapBiholomorph b q : Space) = BlowupH1.chartMap b q := rfl

@[simp] theorem overlapBiholomorph_symm_apply (b : Bool) (x : overlapOpen) :
    ((overlapBiholomorph b).symm x : ℂ × ℂ) = BlowupH1.chartCoords b x := rfl

/-- The two actual overlap parametrizations have the literal blowup transition. -/
theorem overlapBiholomorph_transition (b : Bool) (q : puncturedOpen) :
    ((overlapBiholomorph (!b)).symm (overlapBiholomorph b q) : ℂ × ℂ) =
      ((q : ℂ × ℂ).1 * (q : ℂ × ℂ).2, (q : ℂ × ℂ).2⁻¹) := by
  have h := congrArg (BlowupH1.chartCoords (!b))
    (BlowupH1.chartMap_cross b q q.property)
  rw [overlapBiholomorph_symm_apply, overlapBiholomorph_apply]
  simpa only [BlowupH1.chartCoords_chartMap, BlowupH1.cross] using h.symm

/-- The two literal incidence opens cover the actual blowup. -/
theorem incidenceOpen_sup : Charts.incidenceOpen false ⊔ Charts.incidenceOpen true = ⊤ := by
  apply le_antisymm le_top
  intro x _
  obtain ⟨b, hb⟩ := Charts.incidenceOpen_cover x
  cases b
  · exact Or.inl hb
  · exact Or.inr hb

/-- Genuine cohomology of the actual intersection is genuine cohomology
of the actual punctured product, via its literal chart biholomorphism. -/
def overlapCohomologyEquiv (b : Bool) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) overlapOpen) n ≃+
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) puncturedOpen) n :=
  Biholomorph.cohomologyEquiv (overlapBiholomorph b) n

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupAcyclic
