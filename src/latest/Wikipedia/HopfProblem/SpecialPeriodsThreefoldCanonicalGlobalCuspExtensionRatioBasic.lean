import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullbackComparison
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspBiholomorph

/-!
# The actual punctured native cusp domain and reciprocal parameter

The source is the entire complement of the central fibre in the original
cusp quotient. Its map to the actual regular locus is the original cusp
inclusion, whose membership follows from the full proved overlap source.
The reciprocal parameter is the fixed sphere chart composed with the
actual global projection.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension

open ToricCharts CuspGeometry HolomorphicForms.Cusp

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

local instance nativeManifold : IsManifold I₃ ω LocalSpace := native_isManifold
local instance globalManifold : IsManifold IF ω Threefold.Space := Threefold.space_isManifold

/-- The complete punctured native cusp quotient, with its inherited open atlas. -/
def puncturedNative : TopologicalSpace.Opens CuspGeometry.LocalSpace :=
  ⟨{y | CuspGeometry.parameter y ≠ 0}, isOpen_ne_fun parameter_continuous continuous_const⟩

@[simp] theorem mem_puncturedNative (y : CuspGeometry.LocalSpace) :
    y ∈ puncturedNative ↔ CuspGeometry.parameter y ≠ 0 := Iff.rfl

theorem punctured_mem_overlap (y : puncturedNative) :
    y.val ∈ specialCuspOverlap.source := by
  change y.val ∈ (univ : Set SpecialCuspPiece) ∧ y.val ∈ specialCuspNativeOverlap.source
  exact ⟨mem_univ _, (specialCuspNativeOverlap_source_iff y.val).mpr y.property⟩

theorem inclusion_mem_regular (y : puncturedNative) :
    CuspGeometry.inclusion y.val ∈ regularLocus := by
  change Threefold.projection (CuspGeometry.inclusion y.val) ∈ regularPatch
  rw [CuspGeometry.projection_inclusion]
  exact (Set.ext_iff.mp specialCuspOverlap_source y.val).mp (punctured_mem_overlap y)

/-- The same original cusp inclusion, now with its proved regular-locus membership. -/
def puncturedRegularPoint (y : puncturedNative) : regularLocus :=
  ⟨CuspGeometry.inclusion y.val, inclusion_mem_regular y⟩

@[simp] theorem puncturedRegularPoint_val (y : puncturedNative) :
    (puncturedRegularPoint y : Threefold.Space) = CuspGeometry.inclusion y.val := rfl

theorem puncturedRegularPoint_holomorphic : ContMDiff I₃ IF ω puncturedRegularPoint := by
  have hh : ContMDiff I₃ IF ω
      (fun y : puncturedNative => CuspGeometry.inclusion y.val) :=
    CuspGeometry.inclusion_holomorphic.comp contMDiff_subtype_val
  intro y
  have he : ContMDiffAt I₃ IF ω (Subtype.val ∘ puncturedRegularPoint) y ↔
      ContMDiffAt I₃ IF ω puncturedRegularPoint y :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hh y)

/-- The original logarithmic point, with its genuine nonzero cusp parameter. -/
def logPoint (x : LogDomain) : puncturedNative :=
  ⟨localLogMap x, by
    change CuspQuotient.projection CuspGeometry.data.correction CuspGeometry.data.radius
      (CuspUniformization.totalCuspCover CuspGeometry.data.correction
        CuspGeometry.data.radius x) ≠ 0
    rw [CuspUniformization.projection_totalCuspCover]
    exact CuspUniformization.exponential_ne_zero _⟩

@[simp] theorem logPoint_val (x : LogDomain) : (logPoint x).val = localLogMap x := rfl

/-- The original logarithmic cover covers every point of the entire punctured cusp quotient. -/
theorem logPoint_surjective : Function.Surjective logPoint :=
  CuspUniformization.puncturedCuspCover_surjective CuspGeometry.data.correction
    CuspGeometry.data.radius

theorem logPoint_holomorphic : ContMDiff IF I₃ ω logPoint := by
  intro x
  have he : ContMDiffAt IF I₃ ω (Subtype.val ∘ logPoint) x ↔
      ContMDiffAt IF I₃ ω logPoint x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (localLogMap_holomorphic x)

@[simp] theorem parameter_logPoint (x : LogDomain) :
    parameter (logPoint x).val = CuspUniformization.exponential x.val.1 :=
  CuspUniformization.projection_totalCuspCover CuspGeometry.data.correction
    CuspGeometry.data.radius x

@[simp] theorem puncturedRegularPoint_logPoint (x : LogDomain) :
    puncturedRegularPoint (logPoint x) = GlobalCuspPullback.regularLogPoint x :=
  Subtype.ext rfl

theorem punctured_projection_ne (y : puncturedNative) :
    Threefold.projectionSphere (CuspGeometry.inclusion y.val) ≠ (∞ : RiemannSphere) ∧
    Threefold.projectionSphere (CuspGeometry.inclusion y.val) ≠ ((0 : ℂ) : RiemannSphere) ∧
    Threefold.projectionSphere (CuspGeometry.inclusion y.val) ≠ ((1 : ℂ) : RiemannSphere) :=
  (mem_sphereRegularPatch _).mp ((mem_regularLocus_iff_sphere _).mp (inclusion_mem_regular y))

/-- The literal standard reciprocal sphere coordinate of the actual global base point. -/
def reciprocalParameter (y : puncturedNative) : ℂ :=
  GlobalCusp.reciprocalCoordinate (Threefold.projectionSphere (CuspGeometry.inclusion y.val))

theorem reciprocalParameter_holomorphic : ContMDiff I₃ I₁ ω reciprocalParameter := by
  intro y
  apply (MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_holomorphicAt
    (punctured_projection_ne y).2.1).comp y
  exact ((Threefold.projectionSphere_holomorphic.comp CuspGeometry.inclusion_holomorphic).comp
    contMDiff_subtype_val) y

theorem reciprocalParameter_ne_zero (y : puncturedNative) : reciprocalParameter y ≠ 0 := by
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp (punctured_projection_ne y).1
  have hzne : z ≠ 0 := by
    intro h
    apply (punctured_projection_ne y).2.1
    exact hz.symm.trans (congrArg (fun w : ℂ => (w : RiemannSphere)) h)
  unfold reciprocalParameter
  rw [← hz, GlobalCusp.reciprocalCoordinate_coe hzne]
  exact inv_ne_zero hzne

theorem reciprocalParameter_logarithmic (x : LogDomain) :
    reciprocalParameter (logPoint x) =
      GlobalCusp.reciprocalCoordinate (Threefold.projectionSphere (globalLogMap x)) := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension
