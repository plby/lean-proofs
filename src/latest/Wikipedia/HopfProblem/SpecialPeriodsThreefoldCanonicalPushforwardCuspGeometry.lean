import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspExtension
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDirectImage

/-!
# The actual sphere neighborhood underlying the full cusp patch

The original cusp filling patch is the full inverse image of this sphere
open set, obtained through the fixed sphere uniformization. It contains
infinity and excludes both elliptic values. The unchanged reciprocal
sphere coordinate is holomorphic on the entire open set and vanishes at
infinity.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Cusp

open Triangle

attribute [local instance] Threefold.chartedSpace triangleCompactifiedChartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The image of the entire original cusp filling neighborhood in the actual sphere. -/
def basePatch : Opens RiemannSphere :=
  ⟨triangleSphereUniformization.symm ⁻¹'
      (specialBaseCover.fillingPatch none : Set TriangleCompactifiedOrbitSpace),
    (specialBaseCover.fillingPatch none).isOpen.preimage
      triangleSphereUniformization.symm.continuous⟩

@[simp] theorem mem_basePatch (p : RiemannSphere) :
    p ∈ basePatch ↔ triangleSphereUniformization.symm p ∈
      specialBaseCover.fillingPatch none := Iff.rfl

/-- The actual full cusp patch is precisely the preimage of this sphere open set. -/
theorem projection_mem_basePatch (x : Threefold.Space) :
    Threefold.projectionSphere x ∈ basePatch ↔
      x ∈ Threefold.liftedPatch (some none) := by
  change triangleSphereUniformization.symm
      (triangleSphereUniformization (Threefold.projection x)) ∈
        specialBaseCover.fillingPatch none ↔
      Threefold.projection x ∈ specialBaseCover.fillingPatch none
  rw [triangleSphereUniformization.symm_apply_apply]

theorem basePreimage_basePatch :
    Threefold.basePreimage basePatch = Threefold.liftedPatch (some none) := by
  ext x
  exact projection_mem_basePatch x

theorem infty_mem_basePatch : (∞ : RiemannSphere) ∈ basePatch := by
  change triangleSphereUniformization.symm (∞ : RiemannSphere) ∈
    specialBaseCover.fillingPatch none
  rw [← triangleSphereUniformization_cusp, triangleSphereUniformization.symm_apply_apply]
  exact specialBaseCover.point_mem_fillingPatch none

theorem elliptic_point_not_mem_basePatch (j : Elliptic.Kind) :
    triangleSphereUniformization (Threefold.puncturePoint (some j)) ∉ basePatch := by
  change triangleSphereUniformization.symm
    (triangleSphereUniformization (Threefold.puncturePoint (some j))) ∉
      specialBaseCover.fillingPatch none
  rw [triangleSphereUniformization.symm_apply_apply]
  intro h
  have he := (specialBaseCover.point_mem_fillingPatch_iff (some j) none).mp h
  cases he

theorem zero_not_mem_basePatch : ((0 : ℂ) : RiemannSphere) ∉ basePatch := by
  have h := elliptic_point_not_mem_basePatch .three
  have he : triangleSphereUniformization (Threefold.puncturePoint (some .three)) =
      ((0 : ℂ) : RiemannSphere) := triangleSphereUniformization_centerOne
  rwa [he] at h

theorem one_not_mem_basePatch : ((1 : ℂ) : RiemannSphere) ∉ basePatch := by
  have h := elliptic_point_not_mem_basePatch .four
  have he : triangleSphereUniformization (Threefold.puncturePoint (some .four)) =
      ((1 : ℂ) : RiemannSphere) := triangleSphereUniformization_centerTwo
  rwa [he] at h

theorem basePatch_ne_zero {p : RiemannSphere} (hp : p ∈ basePatch) :
    p ≠ ((0 : ℂ) : RiemannSphere) := fun h => zero_not_mem_basePatch (h ▸ hp)

theorem basePatch_ne_one {p : RiemannSphere} (hp : p ∈ basePatch) :
    p ≠ ((1 : ℂ) : RiemannSphere) := fun h => one_not_mem_basePatch (h ▸ hp)

theorem basePatch_regular_iff {p : RiemannSphere} (hp : p ∈ basePatch) :
    p ∈ Threefold.sphereRegularPatch ↔ p ≠ (∞ : RiemannSphere) := by
  rw [Threefold.mem_sphereRegularPatch]
  exact ⟨fun h => h.1, fun h => ⟨h, basePatch_ne_zero hp, basePatch_ne_one hp⟩⟩

/-- The same standard reciprocal coordinate, restricted to this entire base patch. -/
def reciprocal (p : basePatch) : ℂ := GlobalCusp.reciprocalCoordinate p.val

theorem reciprocal_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω reciprocal := by
  intro p
  exact (MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_holomorphicAt
    (basePatch_ne_zero p.property)).comp p contMDiff_subtype_val.contMDiffAt

@[simp] theorem reciprocal_infty : reciprocal ⟨∞, infty_mem_basePatch⟩ = 0 :=
  GlobalCusp.reciprocalCoordinate_infty

/-- The base open set needed for an arbitrary open-set canonical section. -/
def localBase (U : Opens RiemannSphere) : Opens RiemannSphere := U ⊓ basePatch

theorem localBase_le (U : Opens RiemannSphere) : localBase U ≤ U := inf_le_left

theorem localBase_le_basePatch (U : Opens RiemannSphere) : localBase U ≤ basePatch :=
  inf_le_right

theorem infty_mem_localBase {U : Opens RiemannSphere} (hU : (∞ : RiemannSphere) ∈ U) :
    (∞ : RiemannSphere) ∈ localBase U := ⟨hU, infty_mem_basePatch⟩

theorem preimage_localBase_le_cuspPatch (U : Opens RiemannSphere) :
    Threefold.basePreimage (localBase U) ≤ Threefold.liftedPatch (some none) := by
  intro x hx
  exact (projection_mem_basePatch x).mp hx.2

/-- The literal reciprocal coordinate as a holomorphic function on the chosen base open. -/
def reciprocalSection (U : Opens RiemannSphere) : Threefold.BaseSection (localBase U) :=
  ⟨fun p => GlobalCusp.reciprocalCoordinate p.val, by
    intro p
    exact (MuTorsor.CuspCoordinates.sphereReciprocalCoordinate_holomorphicAt
      (basePatch_ne_zero p.property.2)).comp p contMDiff_subtype_val.contMDiffAt⟩

@[simp] theorem reciprocalSection_apply (U : Opens RiemannSphere) (p : localBase U) :
    reciprocalSection U p = GlobalCusp.reciprocalCoordinate p.val := rfl

@[simp] theorem reciprocalSection_infty {U : Opens RiemannSphere}
    (hU : (∞ : RiemannSphere) ∈ U) :
    reciprocalSection U ⟨∞, infty_mem_localBase hU⟩ = 0 :=
  GlobalCusp.reciprocalCoordinate_infty

/-- The actual full-patch point of every point lying over the local base open. -/
def cuspPoint (U : Opens RiemannSphere) (x : Threefold.basePreimage (localBase U)) :
    GlobalCuspExtension.FullCuspPatch :=
  ⟨x.val, preimage_localBase_le_cuspPatch U x.property⟩

theorem cuspPoint_holomorphic (U : Opens RiemannSphere) :
    ContMDiff IF IF ω (cuspPoint U) := by
  intro x
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    (contMDiff_subtype_val.contMDiffAt (x := x))

@[simp] theorem patchReciprocal_cuspPoint (U : Opens RiemannSphere)
    (x : Threefold.basePreimage (localBase U)) :
    GlobalCuspExtension.patchReciprocal (cuspPoint U x) =
      reciprocalSection U (Threefold.baseProjection (localBase U) x) := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Cusp
