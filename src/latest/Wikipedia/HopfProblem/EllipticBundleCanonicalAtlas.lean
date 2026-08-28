import Wikipedia.HopfProblem.EllipticBundleCanonicalAlternating
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore

/-!
# Canonical bundles from general analytic character cocycles

An existing complex line-bundle cocycle describes the canonical bundle
when its transitions are the inverse determinants of actual analytic chart
derivatives. The chart sources need only be contained in the corresponding
bundle base sets. Each bundle fibre is identified with the full space of
continuous alternating two-covectors, and changes of this identification
are the genuine cotangent pullbacks.

No coboundary expression for the transitions, global frame, or triviality
of the resulting canonical bundle is assumed or asserted here.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.CanonicalBundle

local notation "I₂" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

/-- Analytic coordinate charts identify a general character cocycle with
the inverse-Jacobian cocycle. The bundle cover may be larger than the
coordinate-chart cover. -/
structure CocycleAtlas {M ι : Type*} [TopologicalSpace M] [ChartedSpace Model M]
    (A : HolomorphicCharacterBundle.TransitionData M ι) where
  chart : ι → OpenPartialHomeomorph M Model
  chart_mem_maximalAtlas : ∀ i, chart i ∈ IsManifold.maximalAtlas I₂ ω M
  chart_source_subset : ∀ i, (chart i).source ⊆ A.baseSet i
  mem_source : ∀ x, x ∈ (chart (A.indexAt x)).source
  jacobian_eq : ∀ i j x, x ∈ (chart i).source → x ∈ (chart j).source →
    LinearMap.det
      (fderiv ℂ ((chart i).symm.trans (chart j)) (chart i x)).toLinearMap =
        (A.transition j i x : ℂ)

namespace CocycleAtlas

variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace Model M]
    {A : HolomorphicCharacterBundle.TransitionData M ι} (S : CocycleAtlas A)

/-- The underlying bundle core is the independently constructed character
cocycle bundle, with its original topology and local trivializations. -/
abbrev core (_S : CocycleAtlas A) : VectorBundleCore ℂ M ℂ ι := A.core

theorem mem_baseSet (i : ι) {x : M} (hx : x ∈ (S.chart i).source) : x ∈ A.baseSet i :=
  S.chart_source_subset i hx

theorem mem_transition_source (i j : ι) {x : M}
    (hi : x ∈ (S.chart i).source) (hj : x ∈ (S.chart j).source) :
    S.chart i x ∈ ((S.chart i).symm.trans (S.chart j)).source := by
  refine ⟨(S.chart i).map_source hi, ?_⟩
  change (S.chart i).symm (S.chart i x) ∈ (S.chart j).source
  rw [(S.chart i).left_inv hi]
  exact hj

/-- The bundle transition is the inverse determinant of the actual
coordinate change, including for cocycles that are not coboundaries. -/
theorem coordChange_eq_inverse_jacobian (i j : ι) {x : M}
    (hi : x ∈ (S.chart i).source) (hj : x ∈ (S.chart j).source) :
    S.core.coordChange i j x =
      (LinearMap.det
        (fderiv ℂ ((S.chart i).symm.trans (S.chart j)) (S.chart i x)).toLinearMap)⁻¹ •
          ContinuousLinearMap.id ℂ ℂ := by
  rw [S.jacobian_eq i j x hi hj]
  have hc : A.transition j i x * A.transition i j x = 1 :=
    (A.transition_comp i j i x ⟨⟨S.mem_baseSet i hi, S.mem_baseSet j hj⟩,
      S.mem_baseSet i hi⟩).trans (A.transition_self i x (S.mem_baseSet i hi))
  have hinv := eq_inv_of_mul_eq_one_right hc
  change (A.transition i j x : ℂ) • ContinuousLinearMap.id ℂ ℂ = _
  rw [hinv, Units.val_inv_eq_inv_val]

theorem coordChange_topCovector (i j : ι) {x : M}
    (hi : x ∈ (S.chart i).source) (hj : x ∈ (S.chart j).source) (c : ℂ) :
    coefficientEquiv (S.core.coordChange i j x c) =
      (coefficientEquiv c).compContinuousLinearMap
        (fderiv ℂ ((S.chart j).symm.trans (S.chart i)) (S.chart j x)) := by
  rw [coefficientEquiv_pullback, S.jacobian_eq j i x hj hi]
  rfl

/-- The coordinate covector representing a vector in a canonical fibre. -/
def inCoordinates (i : ι) (x : M) (v : S.core.Fiber x) : TopCovector :=
  coefficientEquiv (S.core.localTriv i ⟨x, v⟩).2

/-- Each fibre is continuously and complex-linearly identified with the
entire space of continuous alternating two-covectors in a valid chart. -/
def coordinateEquiv (i : ι) {x : M} (hx : x ∈ (S.chart i).source) :
    S.core.Fiber x ≃L[ℂ] TopCovector :=
  ((S.core.localTriv i).continuousLinearEquivAt ℂ x (S.mem_baseSet i hx)).trans coefficientEquiv

@[simp] theorem coordinateEquiv_apply (i : ι) {x : M} (hx : x ∈ (S.chart i).source)
    (v : S.core.Fiber x) : S.coordinateEquiv i hx v = S.inCoordinates i x v := rfl

/-- Coordinate representations transform by pullback through the actual
derivative of the reversed chart change. -/
theorem inCoordinates_change (i j : ι) {x : M}
    (hi : x ∈ (S.chart i).source) (hj : x ∈ (S.chart j).source)
    (v : S.core.Fiber x) :
    S.inCoordinates j x v = (S.inCoordinates i x v).compContinuousLinearMap
      (fderiv ℂ ((S.chart j).symm.trans (S.chart i)) (S.chart j x)) := by
  rw [inCoordinates, inCoordinates, coefficientEquiv_pullback, S.jacobian_eq j i x hj hi]
  apply congrArg coefficientEquiv
  change (A.transition (A.indexAt x) j x : ℂ) * id (α := ℂ) v =
    (A.transition i j x : ℂ) *
      ((A.transition (A.indexAt x) i x : ℂ) * id (α := ℂ) v)
  rw [← mul_assoc, ← Units.val_mul,
    A.transition_comp (A.indexAt x) i j x
      ⟨⟨A.mem_baseSet_at x, S.mem_baseSet i hi⟩, S.mem_baseSet j hj⟩]

theorem isContMDiff [A.IsHolomorphic I₂] : S.core.IsContMDiff I₂ ω := inferInstance

theorem holomorphicVectorBundle [A.IsHolomorphic I₂] :
    ContMDiffVectorBundle ω ℂ S.core.Fiber I₂ := inferInstance

theorem fibre_rank_one (x : M) : Module.finrank ℂ (S.core.Fiber x) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

theorem totalSpace_isManifold [A.IsHolomorphic I₂] [IsManifold I₂ ω M] :
    IsManifold I₃ ω S.core.TotalSpace := inferInstance

end CocycleAtlas

end Wikipedia.HopfProblem.Elliptic.CanonicalBundle
