import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultGeometry

/-!
# Local smooth sections in the original period-torus charts

A smooth function on the covering plane gives an actual smooth section
on any subopen of an original quotient chart. Its literal quotient lift
has the prescribed germ inside that chart target. No periodicity or
global descent hypothesis is imposed.
-/

noncomputable section

open Set Topology TopologicalSpace Filter
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

local notation "IR₂" => modelWithCornersSelf ℝ ComplexPlane₂
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

/-- Pull a smooth plane function back along the original native chart,
on an actual torus open contained in that chart's source. -/
def chartSection (p : PeriodDomain) (x : p.Torus) (V : Opens p.Torus)
    (hV : V ≤ chartSource p x) (u : ComplexPlane₂ → ℂ) (hu : ContDiff ℝ ∞ u) :
    SmoothSection p V :=
  sectionOfSmooth p V (fun y => u (DiscreteQuotient.chart p.lattice x y)) fun y hy =>
    (hu.contDiffAt.contMDiffAt : ContMDiffAt IR₂ IR₁ ∞ u
      (DiscreteQuotient.chart p.lattice x y)).comp y
        ((chart_contMDiffOn_real p x ∞).contMDiffAt
          ((chartSource p x).isOpen.mem_nhds (hV hy)))

@[simp] theorem chartSection_apply (p : PeriodDomain) (x : p.Torus) (V : Opens p.Torus)
    (hV : V ≤ chartSource p x) (u : ComplexPlane₂ → ℂ) (hu : ContDiff ℝ ∞ u) (y : V) :
    chartSection p x V hV u hu y = u (DiscreteQuotient.chart p.lattice x (y : p.Torus)) := rfl

/-- Inside the original chart target, the actual quotient lift of the
chart section has exactly the prescribed smooth plane germ. -/
theorem chartSection_lift_germ (p : PeriodDomain) (x : p.Torus) (V : Opens p.Torus)
    (hV : V ≤ chartSource p x) (u : ComplexPlane₂ → ℂ) (hu : ContDiff ℝ ∞ u)
    {z : ComplexPlane₂} (hzt : z ∈ chartTarget p x) (hzV : p.lattice.mkQ z ∈ V) :
    (smoothExtend p V (chartSection p x V hV u hu) ∘ p.lattice.mkQ) =ᶠ[𝓝 z] u := by
  filter_upwards [(chartTarget p x).isOpen.mem_nhds hzt,
    (mkQ_contMDiff_real p).continuous.continuousAt (V.isOpen.mem_nhds hzV)] with w hwt hwV
  change smoothExtend p V (chartSection p x V hV u hu) (p.lattice.mkQ w) = u w
  rw [smoothExtend_apply p V _ _ hwV, chartSection_apply]
  apply congrArg u
  simpa only [DiscreteQuotient.chart_symm] using
    (DiscreteQuotient.chart p.lattice x).right_inv hwt

/-- The image of a plane open under the original inverse chart, with the
original chart target retained in the source of that inverse. -/
def chartImage (p : PeriodDomain) (x : p.Torus) (W : Opens ComplexPlane₂) : Opens p.Torus :=
  ⟨(DiscreteQuotient.chart p.lattice x).symm ''
      ((DiscreteQuotient.chart p.lattice x).target ∩ (W : Set ComplexPlane₂)),
    (DiscreteQuotient.chart p.lattice x).symm.isOpen_image_source_inter W.isOpen⟩

theorem chartImage_le_source (p : PeriodDomain) (x : p.Torus) (W : Opens ComplexPlane₂) :
    chartImage p x W ≤ chartSource p x := by
  rintro y ⟨z, ⟨hzt, _hzW⟩, rfl⟩
  exact (DiscreteQuotient.chart p.lattice x).map_target hzt

theorem chartImage_chart_mem (p : PeriodDomain) (x : p.Torus) (W : Opens ComplexPlane₂)
    {y : p.Torus} (hy : y ∈ chartImage p x W) :
    DiscreteQuotient.chart p.lattice x y ∈ W := by
  rcases hy with ⟨z, ⟨hzt, hzW⟩, rfl⟩
  rw [(DiscreteQuotient.chart p.lattice x).right_inv hzt]
  exact hzW

theorem mem_chartImage_center (p : PeriodDomain) (x : p.Torus) (W : Opens ComplexPlane₂)
    (hxW : DiscreteQuotient.chart p.lattice x x ∈ W) : x ∈ chartImage p x W := by
  refine ⟨DiscreteQuotient.chart p.lattice x x, ⟨chart_mem_chartTarget p x, hxW⟩, ?_⟩
  exact (DiscreteQuotient.chart p.lattice x).left_inv (mem_chartSource p x)

/-- An inclusion of quotient images of the plane open gives an inclusion
of the native chart image into the specified actual torus open. -/
theorem chartImage_le (p : PeriodDomain) (x : p.Torus) (W : Opens ComplexPlane₂)
    (U : Opens p.Torus) (hW : ∀ z ∈ W, p.lattice.mkQ z ∈ U) : chartImage p x W ≤ U := by
  rintro y ⟨z, ⟨_hzt, hzW⟩, rfl⟩
  simpa only [DiscreteQuotient.chart_symm] using hW z hzW

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
