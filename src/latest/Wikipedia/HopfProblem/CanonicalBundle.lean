import Wikipedia.HopfProblem.CanonicalBundleAlternating
import Wikipedia.HopfProblem.HolomorphicLineBundleTrivialization

/-!
# Canonical line bundles from analytic volume charts

For an analytic complex threefold with charts whose Jacobian determinants
are ratios of nonzero constant volume coefficients, construct the actual
holomorphic canonical line bundle by its inverse-Jacobian transition maps.
The identification with top alternating covectors is proved by the
pullback formula for the genuine chart derivatives.

The compatible coordinate volume forms then give an actual nonvanishing
holomorphic section and a base-preserving, fibrewise linear holomorphic
trivialization of the bundle total space.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalBundle

local notation "I₃" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₄" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

/-- Analytic volume charts and their actual derivative transformation law.
The Jacobian assumption is supplied on the entire coordinate overlap. -/
structure ConstantVolumeAtlas (M : Type*) [TopologicalSpace M] [ChartedSpace Model M]
    (ι : Type*) where
  chart : ι → OpenPartialHomeomorph M Model
  chart_mem_maximalAtlas : ∀ i, chart i ∈ IsManifold.maximalAtlas I₃ ω M
  indexAt : M → ι
  mem_source : ∀ x, x ∈ (chart (indexAt x)).source
  coefficient : ι → ℂ
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  jacobian_eq : ∀ i j z, z ∈ ((chart i).symm.trans (chart j)).source →
    LinearMap.det (fderiv ℂ ((chart i).symm.trans (chart j)) z).toLinearMap =
      coefficient i / coefficient j

namespace ConstantVolumeAtlas

variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Model M]
    (A : ConstantVolumeAtlas M ι)

def transitionData : HolomorphicLineBundle.ConstantTransitionData M ι where
  baseSet i := (A.chart i).source
  isOpen_baseSet i := (A.chart i).open_source
  indexAt := A.indexAt
  mem_baseSet_at := A.mem_source
  coefficient := A.coefficient
  coefficient_ne_zero := A.coefficient_ne_zero

/-- The canonical line bundle core: a coefficient in chart `i` transforms
to chart `j` by multiplication by the inverse complex Jacobian. -/
abbrev core : VectorBundleCore ℂ M ℂ ι := A.transitionData.core

theorem mem_transition_source (i j : ι) {x : M}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    A.chart i x ∈ ((A.chart i).symm.trans (A.chart j)).source := by
  refine ⟨(A.chart i).map_source hi, ?_⟩
  change (A.chart i).symm (A.chart i x) ∈ (A.chart j).source
  rw [(A.chart i).left_inv hi]
  exact hj

theorem jacobian_at (i j : ι) {x : M}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    LinearMap.det
      (fderiv ℂ ((A.chart i).symm.trans (A.chart j)) (A.chart i x)).toLinearMap =
        A.coefficient i / A.coefficient j :=
  A.jacobian_eq i j _ (A.mem_transition_source i j hi hj)

/-- The constructed transition function is exactly the inverse of the
actual chart Jacobian, not an independently postulated bundle transition. -/
theorem coordChange_eq_inverse_jacobian (i j : ι) {x : M}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) :
    A.core.coordChange i j x =
      (LinearMap.det
        (fderiv ℂ ((A.chart i).symm.trans (A.chart j)) (A.chart i x)).toLinearMap)⁻¹ •
          ContinuousLinearMap.id ℂ ℂ := by
  rw [A.jacobian_at i j hi hj]
  change (A.coefficient j / A.coefficient i) • ContinuousLinearMap.id ℂ ℂ = _
  rw [inv_div]

theorem coordChange_topCovector (i j : ι) {x : M}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source) (c : ℂ) :
    coefficientEquiv (A.core.coordChange i j x c) =
      (coefficientEquiv c).compContinuousLinearMap
        (fderiv ℂ ((A.chart j).symm.trans (A.chart i)) (A.chart j x)) := by
  rw [coefficientEquiv_pullback, A.jacobian_at j i hj hi]
  rfl

/-- The top alternating covector representing a canonical-bundle fibre
element in an analytic coordinate chart. -/
def inCoordinates (i : ι) (x : M) (v : A.core.Fiber x) : TopCovector :=
  coefficientEquiv (A.core.localTriv i ⟨x, v⟩).2

/-- On each chart, a fibre is continuously and complex-linearly identified
with the full space of top alternating covectors on the coordinate model. -/
def coordinateEquiv (i : ι) {x : M} (hx : x ∈ (A.chart i).source) :
    A.core.Fiber x ≃L[ℂ] TopCovector :=
  ((A.core.localTriv i).continuousLinearEquivAt ℂ x hx).trans coefficientEquiv

@[simp] theorem coordinateEquiv_apply (i : ι) {x : M} (hx : x ∈ (A.chart i).source)
    (v : A.core.Fiber x) : A.coordinateEquiv i hx v = A.inCoordinates i x v := rfl

/-- Coordinate representations of the constructed fibres transform by the
usual cotangent pullback on actual continuous top alternating covectors. -/
theorem inCoordinates_change (i j : ι) {x : M}
    (hi : x ∈ (A.chart i).source) (hj : x ∈ (A.chart j).source)
    (v : A.core.Fiber x) :
    A.inCoordinates j x v = (A.inCoordinates i x v).compContinuousLinearMap
      (fderiv ℂ ((A.chart j).symm.trans (A.chart i)) (A.chart j x)) := by
  rw [inCoordinates, inCoordinates, coefficientEquiv_pullback, A.jacobian_at j i hj hi]
  apply congrArg coefficientEquiv
  change (A.coefficient j / A.coefficient (A.indexAt x)) * id (α := ℂ) v =
    (A.coefficient j / A.coefficient i) *
      ((A.coefficient i / A.coefficient (A.indexAt x)) * id (α := ℂ) v)
  field_simp [A.coefficient_ne_zero]

instance isContMDiff : A.core.IsContMDiff I₃ ω := inferInstance

theorem holomorphicVectorBundle : ContMDiffVectorBundle ω ℂ A.core.Fiber I₃ := inferInstance

theorem fibre_rank_one (x : M) : Module.finrank ℂ (A.core.Fiber x) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

theorem totalSpace_isManifold [IsManifold I₃ ω M] :
    IsManifold I₄ ω A.core.TotalSpace := inferInstance

/-- The actual holomorphic global trivialization of the constructed
canonical bundle. It covers the identity and is linear on each fibre. -/
def globalTrivialization :
    Diffeomorph I₄ I₄ A.core.TotalSpace (M × ℂ) ω :=
  A.transitionData.globalTrivialization I₃

@[simp] theorem globalTrivialization_fst (p : A.core.TotalSpace) :
    (A.globalTrivialization p).1 = p.1 := rfl

theorem globalTrivialization_add (x : M) (v w : A.core.Fiber x) :
    (A.globalTrivialization ⟨x, v + w⟩).2 =
      (A.globalTrivialization ⟨x, v⟩).2 + (A.globalTrivialization ⟨x, w⟩).2 :=
  A.transitionData.globalTrivialization_add I₃ x v w

theorem globalTrivialization_smul (x : M) (c : ℂ) (v : A.core.Fiber x) :
    (A.globalTrivialization ⟨x, c • v⟩).2 = c • (A.globalTrivialization ⟨x, v⟩).2 :=
  A.transitionData.globalTrivialization_smul I₃ x c v

/-- The global holomorphic trivialization as Mathlib's actual bundle
trivialization object. Its domain is the entire bundle. -/
abbrev bundleTrivialization : Trivialization ℂ
    (Bundle.TotalSpace.proj : A.core.TotalSpace → M) :=
  A.transitionData.bundleTrivialization I₃

@[simp] theorem bundleTrivialization_baseSet : A.bundleTrivialization.baseSet = univ := rfl

theorem bundleTrivialization_holomorphic :
    ContMDiff I₄ I₄ ω A.bundleTrivialization :=
  A.transitionData.bundleTrivialization_holomorphic I₃

theorem bundleTrivialization_symm_holomorphic :
    ContMDiff I₄ I₄ ω A.bundleTrivialization.toOpenPartialHomeomorph.symm :=
  A.transitionData.bundleTrivialization_symm_holomorphic I₃

/-- The global nowhere-zero holomorphic canonical section. -/
def volumeSection (x : M) : A.core.Fiber x := A.transitionData.frame x

theorem volumeSection_ne_zero (x : M) : A.volumeSection x ≠ 0 :=
  A.transitionData.frame_ne_zero x

theorem volumeSection_holomorphic :
    ContMDiff I₃ I₄ ω (fun x => (⟨x, A.volumeSection x⟩ : A.core.TotalSpace)) :=
  A.transitionData.frame_holomorphic I₃

theorem volumeSection_inCoordinates (i : ι) (x : M) :
    A.inCoordinates i x (A.volumeSection x) = A.coefficient i • volume := by
  unfold inCoordinates volumeSection
  rw [A.transitionData.frame_localTriv]
  rfl

@[simp] theorem globalTrivialization_volumeSection (x : M) :
    A.globalTrivialization ⟨x, A.volumeSection x⟩ = (x, 1) :=
  A.transitionData.globalTrivialization_frame I₃ x

end ConstantVolumeAtlas

end Wikipedia.HopfProblem.CanonicalBundle
