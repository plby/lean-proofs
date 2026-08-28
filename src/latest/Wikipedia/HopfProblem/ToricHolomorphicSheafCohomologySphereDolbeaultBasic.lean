import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsCharts
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultSections
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultInclusion

/-!
# The actual sphere antiholomorphic differential in its two charts

The coefficients are obtained by differentiating actual smooth functions
in the sphere's original affine coordinates. The proved real derivative
chain rule supplies precisely the required antiholomorphic-covector
overlap law. Thus this map takes values in the independently constructed
smooth form sections, and not in a formal collection of unrelated local
coefficients.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault

open HolomorphicCousin DolbeaultLocal

abbrev SmoothSection (U : Opens RiemannSphere) :=
  SmoothFunctions.Section 𝓘(ℝ, ℂ) RiemannSphere U

/-- The actual smooth function expressed in one of the two original
affine coordinates, with a named extension outside its open domain. -/
def smoothCoefficient (U : Opens RiemannSphere) (s : SmoothSection U)
    (b : Bool) (z : ℂ) : ℂ :=
  smoothExtend U s (RiemannSphere.standardCharts.affineMap b z)

theorem smoothCoefficient_contDiffAt (U : Opens RiemannSphere) (s : SmoothSection U)
    (b : Bool) (z : ℂ) (hz : z ∈ SphereForms.coordinateOpen U b) :
    ContDiffAt ℝ ∞ (smoothCoefficient U s b) z :=
  ((smoothExtend_contMDiffAt U s _ hz).comp z (SphereForms.affineMap_smooth b z)).contDiffAt

theorem smoothCoefficient_smooth (U : Opens RiemannSphere) (s : SmoothSection U)
    (b : Bool) : ContDiffOn ℝ ∞ (smoothCoefficient U s b) (SphereForms.coordinateOpen U b) :=
  fun z hz => (smoothCoefficient_contDiffAt U s b z hz).contDiffWithinAt

theorem smoothCoefficient_add (U : Opens RiemannSphere) (s t : SmoothSection U) (b : Bool) :
    smoothCoefficient U (s + t) b = fun z =>
      smoothCoefficient U s b z + smoothCoefficient U t b z :=
  funext fun z => congrFun (smoothExtend_add U s t)
    (RiemannSphere.standardCharts.affineMap b z)

theorem smoothCoefficient_smul (U : Opens RiemannSphere) (c : ℂ) (s : SmoothSection U)
    (b : Bool) : smoothCoefficient U (c • s) b = fun z => c * smoothCoefficient U s b z :=
  funext fun z => congrFun (smoothExtend_smul U c s)
    (RiemannSphere.standardCharts.affineMap b z)

/-- Reciprocal coordinates are the same actual sphere point, including
when that point is outside the original open domain. -/
theorem smoothCoefficient_inversion (U : Opens RiemannSphere) (s : SmoothSection U)
    (z : ℂ) (hz : z ≠ 0) :
    smoothCoefficient U s false z = smoothCoefficient U s true z⁻¹ := by
  unfold smoothCoefficient
  rw [RiemannSphere.standardCharts.affineMap_inversion false z hz]
  rfl

/-- The actual derivative coefficients satisfy the actual form transition. -/
theorem dbar_coefficient_transition (U : Opens RiemannSphere) (s : SmoothSection U)
    (z : ℂ) (hz : z ≠ 0) (hInf : z⁻¹ ∈ SphereForms.coordinateOpen U true) :
    dbar (smoothCoefficient U s false) z =
      SphereForms.transition z * dbar (smoothCoefficient U s true) z⁻¹ := by
  have he : smoothCoefficient U s false =ᶠ[𝓝 z]
      (fun w => smoothCoefficient U s true w⁻¹) := by
    filter_upwards [(isOpen_ne_fun continuous_id continuous_const).mem_nhds hz] with w hw
    exact smoothCoefficient_inversion U s w hw
  exact (dbar_congr_of_eventuallyEq he).trans
    (dbar_comp_inv hz ((smoothCoefficient_contDiffAt U s true z⁻¹ hInf).differentiableAt
      (by simp)))

/-- One actual smooth derivative coefficient, bundled on its true
coordinate preimage. -/
def dbarCoefficient (U : Opens RiemannSphere) (s : SmoothSection U) (b : Bool) :
    SmoothFunctions.Section 𝓘(ℝ, ℂ) ℂ (SphereForms.coordinateOpen U b) :=
  ⟨fun z => dbar (smoothCoefficient U s b) z,
    fun z => contMDiffAt_subtype_iff.mpr
      (contDiffAt_dbar (smoothCoefficient_contDiffAt U s b z z.property)).contMDiffAt⟩

@[simp] theorem dbarCoefficient_apply (U : Opens RiemannSphere) (s : SmoothSection U)
    (b : Bool) (z : SphereForms.coordinateOpen U b) :
    dbarCoefficient U s b z = dbar (smoothCoefficient U s b) z := rfl

/-- The genuine complex-linear antiholomorphic differential on actual
sphere sections. -/
def differentialSection (U : Opens RiemannSphere) :
    SmoothSection U →ₗ[ℂ] SphereForms.Section U where
  toFun s := SphereForms.sectionMk U (dbarCoefficient U s)
    (fun z hz _h₀ hInf => dbar_coefficient_transition U s z hz hInf)
  map_add' s t := by
    apply SphereForms.section_ext
    intro b z
    change dbar (smoothCoefficient U (s + t) b) z =
      dbar (smoothCoefficient U s b) z + dbar (smoothCoefficient U t b) z
    rw [smoothCoefficient_add]
    exact dbar_add
      ((smoothCoefficient_contDiffAt U s b z z.property).differentiableAt (by simp))
      ((smoothCoefficient_contDiffAt U t b z z.property).differentiableAt (by simp))
  map_smul' c s := by
    apply SphereForms.section_ext
    intro b z
    change dbar (smoothCoefficient U (c • s) b) z = c * dbar (smoothCoefficient U s b) z
    rw [smoothCoefficient_smul]
    exact dbar_const_mul
      ((smoothCoefficient_contDiffAt U s b z z.property).differentiableAt (by simp)) c

@[simp] theorem differentialSection_coefficient (U : Opens RiemannSphere)
    (s : SmoothSection U) (b : Bool) (z : SphereForms.coordinateOpen U b) :
    SphereForms.coefficient (differentialSection U s) b z =
      dbar (smoothCoefficient U s b) z := rfl

/-- The actual derivative is independent of the named ambient
representative and commutes with actual open restriction. -/
theorem differentialSection_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : SmoothSection V) :
    differentialSection U (ContMDiffMap.restrictRingHom 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ h s) =
      SphereForms.restriction h (differentialSection V s) := by
  apply SphereForms.section_ext
  intro b z
  apply dbar_congr_of_eventuallyEq
  exact (smoothExtend_restrict_germ h s _ z.property).comp_tendsto
    ((RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).continuous.tendsto z)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault
