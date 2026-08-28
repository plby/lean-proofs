import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCartierPullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwist
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspReduced

/-!
# The actual pullback of the sphere ideal line

This is the holomorphic pullback along the constructed sphere projection
of the line whose local frames are the actual ideal-sheaf frames of
`O(-infinity)`.  Its native bundle coefficients are the literal pulled-back
Cartier fractions.  Near the full cusp fibre, the denominator is the
standard reciprocal coordinate, equal to the original cusp parameter
times its proved analytic unit.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalBasePullback

open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames Triangle

attribute [local instance] Threefold.chartedSpace triangleCompactifiedChartedSpace
  CuspGeometry.nativeChartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

theorem generic_preimage_eq :
    Threefold.projectionSphere ⁻¹' (CanonicalGlobal.BaseTwist.cartier.genericSet :
      Set RiemannSphere) = (GlobalCusp.outside : Set Threefold.Space) := by
  ext x
  exact mem_finiteChart (Threefold.projectionSphere x)

theorem generic_preimage_dense :
    Dense (Threefold.projectionSphere ⁻¹' (CanonicalGlobal.BaseTwist.cartier.genericSet :
      Set RiemannSphere)) := generic_preimage_eq.symm ▸ GlobalCusp.outside_dense

/-- The actual holomorphic inverse-image Cartier presentation. -/
def cartier : CanonicalGlobal.CartierData IF Threefold.Space Bool :=
  CanonicalGlobal.BaseTwist.cartier.pullback Threefold.projectionSphere
    Threefold.projectionSphere_holomorphic generic_preimage_dense

/-- The genuine pulled-back vector bundle, with its inherited analytic atlas. -/
abbrev bundle := cartier.associatedBundle

theorem bundle_contMDiffVectorBundle : ContMDiffVectorBundle ω ℂ bundle.Fiber IF :=
  cartier.associatedBundle_contMDiffVectorBundle

@[simp] theorem genericSet_eq :
    (cartier.genericSet : Set Threefold.Space) = (GlobalCusp.outside : Set Threefold.Space) :=
  generic_preimage_eq

@[simp] theorem numerator_eq_one (b : Bool) (x : Threefold.Space) : cartier.numerator b x = 1 := rfl

@[simp] theorem denominator_finite (x : Threefold.Space) : cartier.denominator false x = 1 := rfl

@[simp] theorem denominator_infinity (x : Threefold.Space) :
    cartier.denominator true x =
      CanonicalGlobal.BaseTwist.infinityCoordinate (Threefold.projectionSphere x) := rfl

@[simp] theorem localFraction_finite (x : Threefold.Space) :
    cartier.localFraction false x = 1 :=
  CanonicalGlobal.BaseTwist.localFraction_false (Threefold.projectionSphere x)

@[simp] theorem localFraction_infinity (x : Threefold.Space) :
    cartier.localFraction true x =
      (CanonicalGlobal.BaseTwist.infinityCoordinate (Threefold.projectionSphere x))⁻¹ :=
  CanonicalGlobal.BaseTwist.localFraction_true (Threefold.projectionSphere x)

/-- The total-space pullback map is holomorphic for the two original
bundle atlases and takes the actual Cartier section to the original one. -/
theorem totalMap_holomorphic :
    ContMDiff ((IF).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω
      (CanonicalGlobalLineBundle.pullbackTotalMap CanonicalGlobal.BaseTwist.data
        Threefold.projectionSphere Threefold.projectionSphere_holomorphic.continuous) :=
  CanonicalGlobal.BaseTwist.cartier.pullbackTotalMap_holomorphic Threefold.projectionSphere
    Threefold.projectionSphere_holomorphic

theorem totalMap_rawSection (x : Threefold.Space) :
    CanonicalGlobalLineBundle.pullbackTotalMap CanonicalGlobal.BaseTwist.data
      Threefold.projectionSphere Threefold.projectionSphere_holomorphic.continuous
      (cartier.rawSectionMap x) =
        CanonicalGlobal.BaseTwist.cartier.rawSectionMap (Threefold.projectionSphere x) := rfl

/-- The old ideal-frame reciprocal coordinate is the fixed atlas's
reciprocal chart on its actual domain. -/
theorem infinityCoordinate_eq_reciprocal {p : RiemannSphere} (hp : p ∈ infinityChart) :
    CanonicalGlobal.BaseTwist.infinityCoordinate p = GlobalCusp.reciprocalCoordinate p := by
  obtain ⟨u, rfl⟩ := exists_infinityCoordinate p hp
  rw [CanonicalGlobal.BaseTwist.infinityCoordinate_infinityParametrization]
  exact (RiemannSphere.standardCharts.parametrization_symm_apply true u).symm

/-- Disjointness of the original filling patches excludes the finite
origin from the entire cusp patch, not just from a smaller neighborhood. -/
theorem cusp_projection_mem_infinityChart {y : Threefold.Space}
    (hy : y ∈ (Threefold.liftedPatch (some none) : Set Threefold.Space)) :
    Threefold.projectionSphere y ∈ infinityChart := by
  apply (mem_infinityChart _).mpr
  intro hzero
  have hbase : Threefold.projection y = Threefold.puncturePoint (some .three) := by
    apply triangleSphereUniformization.injective
    exact hzero.trans triangleSphereUniformization_centerOne.symm
  have hm : Threefold.projection y ∈ specialBaseCover.fillingPatch none := hy
  rw [hbase] at hm
  have hbad := (specialBaseCover.point_mem_fillingPatch_iff (some .three) none).mp hm
  cases hbad

/-- The actual pulled-back denominator, on the whole global cusp patch. -/
theorem denominator_infinity_on_cusp {y : Threefold.Space}
    (hy : y ∈ (Threefold.liftedPatch (some none) : Set Threefold.Space)) :
    cartier.denominator true y = CuspGeometry.cuspCoordinate y *
      GlobalCusp.coordinateUnit (CuspGeometry.cuspCoordinate y) := by
  rw [denominator_infinity,
    infinityCoordinate_eq_reciprocal (cusp_projection_mem_infinityChart hy)]
  exact GlobalCusp.reciprocal_projection_eq_mul_unit hy

/-- In every genuine central chart, the pulled-back ideal denominator
is the product of distinct branch coordinates times an analytic unit. -/
theorem denominator_reduced_normalCrossingChart (x : CuspGeometry.LocalSpace)
    (hx : CuspGeometry.parameter x = 0) :
    ∃ J : Finset (Fin 3),
      ∃ e : PartialDiffeomorph IF (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
          Threefold.Space (ToricCharts.CoordinateSpace 3) ω,
      J.Nonempty ∧ CuspGeometry.inclusion x ∈ e.source ∧
      e (CuspGeometry.inclusion x) = 0 ∧
      AnalyticAt ℂ (GlobalCusp.branchUnit J) 0 ∧ GlobalCusp.branchUnit J 0 ≠ 0 ∧
      ∀ w ∈ e.target, cartier.denominator true (e.symm w) =
        GlobalCusp.branchProduct J w * GlobalCusp.branchUnit J w := by
  obtain ⟨J, e, _, hJ, hxs, hzero, hsource, hprod⟩ :=
    CuspNormalForms.normalCrossingChart_with_branchCount x hx
  refine ⟨J, e, hJ, hxs, hzero, GlobalCusp.branchUnit_analyticAt J hJ,
    GlobalCusp.branchUnit_zero_ne_zero J hJ, ?_⟩
  intro w hw
  exact (denominator_infinity_on_cusp (hsource (e.map_target hw))).trans
    (congrArg (fun q : ℂ => q * GlobalCusp.coordinateUnit q) (hprod w hw))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalBasePullback
