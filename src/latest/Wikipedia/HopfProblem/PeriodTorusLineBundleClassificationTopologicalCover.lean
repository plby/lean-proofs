import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopologicalCoverIdentification
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

/-!
# The actual universal-cover pullback on a convex trivializing cover

For an arbitrary native holomorphic complex line bundle on a period torus,
this file uses Mathlib's native pullback along the actual quotient map. Its
ball-cover scalar cocycle is analytically identified with that native pullback.
The transitions on the balls are proved to be the original torus transitions
composed with the quotient projection.

Only local triviality is used and proved here. Global triviality of this
pullback, and vanishing of its integer logarithmic Čech obstruction, remain
separate proof obligations.
-/

noncomputable section

open Bundle Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological

open PeriodTorusLineBundleClassificationNative

local notation "I₀" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The original quotient projection bundled as an analytic map. -/
def coveringProjection (p : PeriodDomain) : ContMDiffMap I₀ I₀ ComplexPlane₂ p.Torus ω :=
  ⟨p.lattice.mkQ, p.torus_projection_holomorphic⟩

@[simp] theorem coveringProjection_apply (p : PeriodDomain) (z : ComplexPlane₂) :
    coveringProjection p z = p.lattice.mkQ z := rfl

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V I₀]

/-- Mathlib's actual native pullback fibre family with its native pullback
topology and analytic vector-bundle structure. -/
abbrev universalCoverPullback :=
  (coveringProjection p : ComplexPlane₂ → p.Torus) *ᵖ V

theorem universalCoverPullback_isHolomorphic :
    ContMDiffVectorBundle ω ℂ (universalCoverPullback p V) I₀ := inferInstance

/-- A convex-cover cocycle extracted from the actual native pullback. -/
def pullbackBallData : HolomorphicCharacterBundle.TransitionData ComplexPlane₂ ComplexPlane₂ :=
  ballData (universalCoverPullback p V)

instance pullbackBallData_isHolomorphic : (pullbackBallData p V).IsHolomorphic I₀ :=
  inferInstanceAs ((ballData (universalCoverPullback p V)).IsHolomorphic I₀)

/-- The ball-cocycle bundle is genuinely the universal-cover pullback of the
arbitrary native torus bundle, by an analytic fibre-linear total-space map. -/
def pullbackBallIdentification :
    AnalyticBundleIso I₀ (pullbackBallData p V).core.Fiber (universalCoverPullback p V) :=
  ballIdentification (universalCoverPullback p V)

omit [ContMDiffVectorBundle ω ℂ V I₀] in
theorem pullbackBallData_transition_eq_native (i j z : ComplexPlane₂)
    (hz : z ∈ (pullbackBallData p V).baseSet i ∩ (pullbackBallData p V).baseSet j) :
    ((pullbackBallData p V).transition i j z : ℂ) =
      (nativeTriv V (p.lattice.mkQ i)).coordChangeL ℂ
        (nativeTriv V (p.lattice.mkQ j)) (p.lattice.mkQ z) 1 := by
  have hi : p.lattice.mkQ z ∈ (nativeTriv V (p.lattice.mkQ i)).baseSet :=
    ball_subset_nativeTriv (universalCoverPullback p V) i hz.1
  have hj : p.lattice.mkQ z ∈ (nativeTriv V (p.lattice.mkQ j)).baseSet :=
    ball_subset_nativeTriv (universalCoverPullback p V) j hz.2
  change ((nativeTriv V (p.lattice.mkQ i)).pullback (coveringProjection p)).coordChangeL ℂ
    ((nativeTriv V (p.lattice.mkQ j)).pullback (coveringProjection p)) z 1 = _
  rw [(nativeTriv V (p.lattice.mkQ i)).coordChangeL_apply _ ⟨hi, hj⟩,
    ((nativeTriv V (p.lattice.mkQ i)).pullback (coveringProjection p)).coordChangeL_apply' _]
  · rfl
  · exact ⟨hi, hj⟩

omit [ContMDiffVectorBundle ω ℂ V I₀] in
theorem pullbackBallData_finite_intersection_contractible (s : Finset ComplexPlane₂)
    (hne : (⋂ i ∈ s, (pullbackBallData p V).baseSet i).Nonempty) :
    ContractibleSpace (⋂ i ∈ s, (pullbackBallData p V).baseSet i : Set ComplexPlane₂) :=
  ballData_finite_intersection_contractible (universalCoverPullback p V) s hne

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTopological
