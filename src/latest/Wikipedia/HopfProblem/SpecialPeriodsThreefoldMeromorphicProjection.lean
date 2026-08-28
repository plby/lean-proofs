import Wikipedia.HopfProblem.HolomorphicMeromorphicPullback
import Wikipedia.HopfProblem.HolomorphicMeromorphicOpenMapping
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionDensity
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationBasic

/-!
# Genuine meromorphic pullback along the actual sphere projection

The constructed threefold projection is nowhere locally constant: any
open neighborhood contains a point of the actual dense regular locus,
where its true differential is surjective. The holomorphic open-mapping
theorem therefore proves that the original projection is open. Its
genuine pullback on local meromorphic sections is consequently defined
and is injective, since the original sphere projection is surjective.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The actual sphere projection, bundled with its proved holomorphicity. -/
def sphereProjection : ContMDiffMap IF I₁ Threefold.Space RiemannSphere ω :=
  ⟨projectionSphere, projectionSphere_holomorphic⟩

@[simp] theorem sphereProjection_apply (x : Threefold.Space) :
    sphereProjection x = projectionSphere x := rfl

/-- A constant neighborhood would contain a regular point with zero
differential, contradicting the proved surjectivity at that point. -/
theorem projectionSphere_not_locally_constant (x : Threefold.Space) :
    ¬ projectionSphere =ᶠ[𝓝 x] fun _ => projectionSphere x := by
  intro hconst
  obtain ⟨U, hU, hUopen, hxU⟩ := mem_nhds_iff.mp hconst
  obtain ⟨y, hyregular, hyU⟩ := regularLocus_dense.exists_mem_open hUopen ⟨x, hxU⟩
  have hlocal : projectionSphere =ᶠ[𝓝 y] fun _ => projectionSphere x :=
    Filter.eventuallyEq_of_mem (hUopen.mem_nhds hyU) (fun z hz => hU hz)
  have hderiv : mfderiv IF I₁ projectionSphere y = 0 := by
    have heq : (mfderiv IF I₁ projectionSphere y :
        (ℂ × ComplexPlane₂) →L[ℂ] ℂ) =
        mfderiv IF I₁ (fun _ : Threefold.Space => projectionSphere x) y :=
      hlocal.mfderiv_eq
    exact heq.trans mfderiv_const
  obtain ⟨hinf, hzero, hone⟩ :=
    (mem_sphereRegularPatch (projectionSphere y)).mp
      ((mem_regularLocus_iff_sphere y).mp hyregular)
  exact (FibreClassification.not_surjective_of_mfderiv_eq_zero y hderiv)
    (FibreClassification.regular_mfderiv_surjective y hinf hzero hone)

/-- The original projection is open, including at points of the special fibers. -/
theorem projectionSphere_isOpenMap : IsOpenMap projectionSphere :=
  HolomorphicMeromorphicOpenMapping.isOpenMap_of_contMDiff_of_not_locally_constant
    IF I₁ projectionSphere_holomorphic projectionSphere_not_locally_constant

theorem sphereProjection_isOpenMap : IsOpenMap sphereProjection := projectionSphere_isOpenMap

/-- The actual global meromorphic pullback from the sphere to the constructed
threefold. The inverse image of the whole sphere is the whole original space. -/
def sphereMeromorphicPullback :
    HolomorphicMeromorphic.Section I₁ RiemannSphere ⊤ →+*
      HolomorphicMeromorphic.Section IF Threefold.Space ⊤ :=
  HolomorphicMeromorphic.pullbackRingHom IF I₁ sphereProjection sphereProjection_isOpenMap ⊤

/-- Pullback acts at every original point by the actual fraction-field germ map. -/
@[simp] theorem sphereMeromorphicPullback_apply
    (s : HolomorphicMeromorphic.Section I₁ RiemannSphere ⊤)
    (x : (⊤ : Opens Threefold.Space)) :
    sphereMeromorphicPullback s x =
      HolomorphicMeromorphic.germPullback IF I₁ sphereProjection sphereProjection_isOpenMap x.val
        (s ⟨projectionSphere x.val, by trivial⟩) := rfl

/-- The original surjectivity of the sphere projection makes its genuine
meromorphic pullback injective. -/
theorem sphereMeromorphicPullback_injective : Function.Injective sphereMeromorphicPullback :=
  HolomorphicMeromorphic.pullbackRingHom_injective IF I₁ sphereProjection
    sphereProjection_isOpenMap projectionSphere_surjective ⊤

@[simp] theorem sphereMeromorphicPullback_ofHolomorphic
    (s : HolomorphicFunctionSheaf.Section I₁ RiemannSphere ⊤) :
    sphereMeromorphicPullback (HolomorphicMeromorphic.ofHolomorphic I₁ RiemannSphere ⊤ s) =
      HolomorphicMeromorphic.ofHolomorphic IF Threefold.Space ⊤
        (HolomorphicMeromorphic.holomorphicPullback IF I₁ sphereProjection ⊤ s) :=
  HolomorphicMeromorphic.pullbackSection_ofHolomorphic IF I₁ sphereProjection
    sphereProjection_isOpenMap ⊤ s

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
