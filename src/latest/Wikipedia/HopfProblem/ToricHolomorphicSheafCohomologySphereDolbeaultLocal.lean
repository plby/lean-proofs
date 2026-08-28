import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereDolbeaultBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsLocal

/-!
# Actual local primitives of smooth sphere forms

In one of the original affine charts, the actual form coefficient has a
smooth Cauchy–Green primitive. A sufficiently small actual chart image
is chosen where its derivative equals that coefficient. Pulling the
primitive through the genuine coordinate inverse gives a smooth sphere
function. Equality of the chosen coefficient implies equality of the
entire actual form, by its already proved derivative transition law.
-/

noncomputable section

open Set TopologicalSpace Filter Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault

open HolomorphicCousin DolbeaultLocal

/-- A genuine smooth form has a genuine smooth primitive on an actual
smaller neighborhood in either of the original sphere charts. -/
theorem exists_local_primitive_in_chart (U : Opens RiemannSphere)
    (s : SphereForms.Section U) (b : Bool) (z : ℂ)
    (hz : z ∈ SphereForms.coordinateOpen U b) :
    ∃ (V : Opens RiemannSphere) (hVU : V ≤ U),
      RiemannSphere.standardCharts.affineMap b z ∈ V ∧
      ∃ t : SmoothSection V,
        differentialSection V t = SphereForms.restriction hVU s := by
  let a := SphereForms.coefficient s b
  let g : ℂ → ℂ := smoothExtend (SphereForms.coordinateOpen U b) a
  have hg : ContDiffOn ℝ ∞ g (SphereForms.coordinateOpen U b) := by
    intro w hw
    have hw' := smoothExtend_contMDiffAt (SphereForms.coordinateOpen U b) a w hw
    exact hw'.contDiffAt.contDiffWithinAt
  obtain ⟨u, hu, he⟩ := exists_smooth_dbar_primitive_germ
    (SphereForms.coordinateOpen U b).isOpen hg hz
  have hmem : ∀ᶠ w in 𝓝 z, w ∈ SphereForms.coordinateOpen U b :=
    (SphereForms.coordinateOpen U b).isOpen.mem_nhds hz
  have hnear : ∀ᶠ w in 𝓝 z, w ∈ SphereForms.coordinateOpen U b ∧ dbar u w = g w :=
    hmem.and he
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let V : Opens RiemannSphere :=
    ⟨RiemannSphere.standardCharts.affineMap b '' Metric.ball z r,
      (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).isOpenMap _ isOpen_ball⟩
  have hVU : V ≤ U := by
    rintro p ⟨w, hw, rfl⟩
    exact (hball hw).1
  have hVrange : (V : Set RiemannSphere) ⊆
      range (RiemannSphere.standardCharts.affineMap b) := by
    rintro p ⟨w, _hw, rfl⟩
    exact mem_range_self w
  let t : SmoothSection V :=
    ⟨fun p => u (SphereForms.chartInverseOn b V hVrange p),
      hu.contMDiff.comp (SphereForms.chartInverseOn b V hVrange).contMDiff⟩
  refine ⟨V, hVU, ⟨z, mem_ball_self hr, rfl⟩, t, ?_⟩
  apply SphereForms.section_ext_of_coefficient b V hVrange
  apply ContMDiffMap.ext
  intro w
  have hwBall : (w : ℂ) ∈ Metric.ball z r := by
    have hw := w.property
    change RiemannSphere.standardCharts.affineMap b w ∈
      RiemannSphere.standardCharts.affineMap b '' Metric.ball z r at hw
    obtain ⟨v, hv, hvw⟩ := hw
    exact (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).injective hvw ▸ hv
  have hwU : (w : ℂ) ∈ SphereForms.coordinateOpen U b := hVU w.property
  have hcoef : smoothCoefficient V t b =ᶠ[𝓝 (w : ℂ)] u := by
    filter_upwards [(SphereForms.coordinateOpen V b).isOpen.mem_nhds w.property] with q hq
    change smoothExtend V t (RiemannSphere.standardCharts.affineMap b q) = u q
    rw [smoothExtend_apply V t (RiemannSphere.standardCharts.affineMap b q) hq]
    change u (SphereForms.chartInverseOn b V hVrange
      ⟨RiemannSphere.standardCharts.affineMap b q, hq⟩) = u q
    rw [SphereForms.chartInverseOn_affineMap]
  change dbar (smoothCoefficient V t b) w = a ⟨w, hwU⟩
  exact (dbar_congr_of_eventuallyEq hcoef).trans
    ((hball hwBall).2.trans (smoothExtend_apply (SphereForms.coordinateOpen U b) a w hwU))

/-- Every actual smooth form section admits an actual smooth primitive
on a neighborhood of each actual sphere point in its domain. -/
theorem exists_local_primitive (U : Opens RiemannSphere) (x : RiemannSphere)
    (hx : x ∈ U) (s : SphereForms.Section U) :
    ∃ (V : Opens RiemannSphere) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : SmoothSection V, differentialSection V t = SphereForms.restriction hVU s := by
  rcases RiemannSphere.standardCharts.covered x with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact exists_local_primitive_in_chart U s false z hx
  · exact exists_local_primitive_in_chart U s true z hx

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault
