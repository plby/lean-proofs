import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicProjection
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackFunctor
import Wikipedia.HopfProblem.HolomorphicMeromorphicPullbackRegular
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphere

/-!
# The actual rational base field inside the threefold's meromorphic field

The original sphere projection induces an injective complex-algebra map
from its genuine meromorphic field. Composing with proved native sphere
rationality embeds the usual rational-function field into the threefold's
actual field. The image of the indeterminate is the meromorphic base
coordinate, with its literal projection values at every finite base point.

This proves the lower bound one for the actual transcendence degree. It
does not assume or establish that every meromorphic function descends.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRational

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

instance threefoldGlobalDomain_connected : ConnectedSpace (⊤ : Opens Threefold.Space) := by
  let : ConnectedSpace Threefold.Space := Threefold.space_connected
  exact Subtype.connectedSpace isConnected_univ

/-- The already constructed pullback preserves the original complex constants. -/
def spherePullbackAlgHom :
    HolomorphicMeromorphic.Function I₁ RiemannSphere →ₐ[ℂ]
      HolomorphicMeromorphic.Function IF Threefold.Space :=
  HolomorphicMeromorphic.pullbackAlgHom IF I₁ sphereProjection sphereProjection_isOpenMap ⊤

@[simp] theorem spherePullbackAlgHom_toRingHom :
    spherePullbackAlgHom.toRingHom = sphereMeromorphicPullback := rfl

theorem spherePullbackAlgHom_injective : Function.Injective spherePullbackAlgHom :=
  sphereMeromorphicPullback_injective

/-- The actual rational subfield supplied by the original sphere projection. -/
def rationalFunctionEmbedding :
    RatFunc ℂ →ₐ[ℂ] HolomorphicMeromorphic.Function IF Threefold.Space :=
  spherePullbackAlgHom.comp HolomorphicMeromorphic.SphereNative.rationalEquiv.toAlgHom

theorem rationalFunctionEmbedding_injective : Function.Injective rationalFunctionEmbedding :=
  spherePullbackAlgHom_injective.comp
    HolomorphicMeromorphic.SphereNative.rationalEquiv.injective

/-- The genuine meromorphic base coordinate of the constructed threefold. -/
def baseCoordinate : HolomorphicMeromorphic.Function IF Threefold.Space :=
  spherePullbackAlgHom HolomorphicMeromorphic.SphereNative.coordinate

@[simp] theorem rationalFunctionEmbedding_X :
    rationalFunctionEmbedding RatFunc.X = baseCoordinate := by
  change spherePullbackAlgHom (HolomorphicMeromorphic.SphereNative.rationalEquiv RatFunc.X) = _
  rw [HolomorphicMeromorphic.SphereNative.rationalEquiv_X]
  rfl

/-- The actual base coordinate satisfies no nonzero complex polynomial relation. -/
theorem baseCoordinate_transcendental : Transcendental ℂ baseCoordinate := by
  apply transcendental_iff_injective.mpr
  rw [show Polynomial.aeval baseCoordinate = spherePullbackAlgHom.comp
      HolomorphicMeromorphic.SphereNative.polynomialMap from
    Polynomial.aeval_algHom spherePullbackAlgHom HolomorphicMeromorphic.SphereNative.coordinate]
  exact spherePullbackAlgHom_injective.comp
    HolomorphicMeromorphic.SphereNative.polynomialMap_injective

/-- A lower bound for the original threefold field, without a descent hypothesis. -/
theorem one_le_meromorphic_trdeg :
    1 ≤ Algebra.trdeg ℂ (HolomorphicMeromorphic.Function IF Threefold.Space) := by
  have h := trdeg_le_of_injective spherePullbackAlgHom spherePullbackAlgHom_injective
  rwa [HolomorphicMeromorphic.SphereNative.meromorphic_trdeg_eq_one] at h

/-- At any actual point above a finite base value, the meromorphic
coordinate has exactly the value of the original sphere projection. -/
theorem baseCoordinate_value (x : Threefold.Space) (z : ℂ)
    (hx : projectionSphere x = (z : RiemannSphere)) :
    HolomorphicMeromorphic.value IF Threefold.Space baseCoordinate ⟨x, trivial⟩ = z := by
  have hreg : HolomorphicMeromorphic.RegularAt I₁ RiemannSphere
      HolomorphicMeromorphic.SphereNative.coordinate
      ⟨projectionSphere x, trivial⟩ := by
    rw [hx]
    exact ⟨_, HolomorphicMeromorphic.SphereNative.coordinate_finite_holomorphicGerm z⟩
  have hv := HolomorphicMeromorphic.value_pullbackSection_of_regularAt IF I₁
    sphereProjection sphereProjection_isOpenMap HolomorphicMeromorphic.SphereNative.coordinate
    (⟨x, trivial⟩ : (⊤ : Opens Threefold.Space)) hreg
  change HolomorphicMeromorphic.value IF Threefold.Space baseCoordinate ⟨x, trivial⟩ =
    HolomorphicMeromorphic.value I₁ RiemannSphere HolomorphicMeromorphic.SphereNative.coordinate
      ⟨projectionSphere x, trivial⟩ at hv
  rw [hx] at hv
  exact hv.trans (HolomorphicMeromorphic.SphereNative.coordinate_finiteValue z)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRational
