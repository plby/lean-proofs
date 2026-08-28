import Wikipedia.HopfProblem.HolomorphicFibreConstancy
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalization

/-!
# Holomorphic functions are constant on every actual global fibre

The regular and elliptic fibres have their native compact connected
surface parametrizations. The singular cusp fibre is covered by the
actual compact connected toric normalization surface. Applying the
compact maximum principle to those actual holomorphic maps proves
fibrewise constancy, including at all three exceptional values.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open Triangle

attribute [local instance] chartedSpace

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The literal preimage of an open set of the actual sphere base. -/
def basePreimage (U : Opens RiemannSphere) : Opens Space :=
  ⟨projectionSphere ⁻¹' (U : Set RiemannSphere),
    U.isOpen.preimage projectionSphere_continuous⟩

@[simp] theorem mem_basePreimage (U : Opens RiemannSphere) (x : Space) :
    x ∈ basePreimage U ↔ projectionSphere x ∈ U := Iff.rfl

private theorem fibre_apply_eq_of_parametrization
    {F K T : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace K] {J : ModelWithCorners ℂ F K} [J.Boundaryless]
    [TopologicalSpace T] [ChartedSpace K T] [IsManifold J ω T]
    [CompactSpace T] [ConnectedSpace T]
    (U : Opens RiemannSphere) (f : basePreimage U → ℂ)
    (hf : ContMDiff IF 𝓘(ℂ) ω f) (b : RiemannSphere) (hb : b ∈ U)
    (g : T → Space) (hg : ContMDiff J IF ω g)
    (hgr : range g = projectionSphere ⁻¹' {b})
    (x y : basePreimage U) (hx : projectionSphere x = b) (hy : projectionSphere y = b) :
    f x = f y := by
  apply holomorphic_apply_eq_of_compact_parametrization (basePreimage U) f hf g hg
  · intro t
    change projectionSphere (g t) ∈ U
    have ht : projectionSphere (g t) = b := by
      have hr : g t ∈ range g := mem_range_self t
      rw [hgr] at hr
      exact hr
    rw [ht]
    exact hb
  · rw [hgr]
    exact hx
  · rw [hgr]
    exact hy

theorem holomorphic_regular_fibre_apply_eq (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∈ U)
    (x y : basePreimage U)
    (hx : projectionSphere x = regularSphereValue z)
    (hy : projectionSphere y = regularSphereValue z) : f x = f y :=
  fibre_apply_eq_of_parametrization U f hf (regularSphereValue z) hz
    (regularTorusInclusion z) (regularTorusInclusion_holomorphic z)
    (regularTorusInclusion_range z) x y hx hy

theorem holomorphic_elliptic_fibre_apply_eq (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f)
    (j : Elliptic.Kind) (hb : EllipticGeometry.sphereValue j ∈ U)
    (x y : basePreimage U)
    (hx : projectionSphere x = EllipticGeometry.sphereValue j)
    (hy : projectionSphere y = EllipticGeometry.sphereValue j) : f x = f y :=
  fibre_apply_eq_of_parametrization U f hf (EllipticGeometry.sphereValue j) hb
    (EllipticGeometry.centralSurfaceInclusion j)
    (EllipticGeometry.centralSurfaceInclusion_holomorphic j)
    (EllipticGeometry.centralSurfaceInclusion_range j) x y hx hy

theorem holomorphic_cusp_fibre_apply_eq (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f)
    (hb : (∞ : RiemannSphere) ∈ U) (x y : basePreimage U)
    (hx : projectionSphere x = (∞ : RiemannSphere))
    (hy : projectionSphere y = (∞ : RiemannSphere)) : f x = f y :=
  fibre_apply_eq_of_parametrization U f hf (∞ : RiemannSphere) hb
    CuspGeometry.componentMap CuspGeometry.componentMap_holomorphic
    CuspGeometry.componentMap_range x y hx hy

/-- Every holomorphic function on the preimage of any base open set is
constant on every literal fibre, including the singular cusp fibre. -/
theorem holomorphic_fibre_apply_eq (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f)
    (x y : basePreimage U) (hxy : projectionSphere x = projectionSphere y) : f x = f y := by
  let b := projectionSphere x
  have hb : b ∈ U := x.property
  have hx : projectionSphere x = b := rfl
  have hy : projectionSphere y = b := hxy.symm
  by_cases hi : b = (∞ : RiemannSphere)
  · exact holomorphic_cusp_fibre_apply_eq U f hf (hi ▸ hb) x y (hx.trans hi) (hy.trans hi)
  by_cases h0 : b = ((0 : ℂ) : RiemannSphere)
  · apply holomorphic_elliptic_fibre_apply_eq U f hf .three
    · simpa only [EllipticGeometry.sphereValue_three] using h0 ▸ hb
    · simpa only [EllipticGeometry.sphereValue_three] using hx.trans h0
    · simpa only [EllipticGeometry.sphereValue_three] using hy.trans h0
  by_cases h1 : b = ((1 : ℂ) : RiemannSphere)
  · apply holomorphic_elliptic_fibre_apply_eq U f hf .four
    · simpa only [EllipticGeometry.sphereValue_four] using h1 ▸ hb
    · simpa only [EllipticGeometry.sphereValue_four] using hx.trans h1
    · simpa only [EllipticGeometry.sphereValue_four] using hy.trans h1
  let z := regularPointOver b hi h0 h1
  have hz : regularSphereValue z = b := regularPointOver_value b hi h0 h1
  exact holomorphic_regular_fibre_apply_eq U f hf z (hz.symm ▸ hb) x y
    (hx.trans hz.symm) (hy.trans hz.symm)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
