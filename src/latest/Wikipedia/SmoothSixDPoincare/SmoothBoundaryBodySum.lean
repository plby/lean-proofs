import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

/-! # Disjoint sums of actual compact bodies and their native smooth boundaries -/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} (U V : SmoothBoundaryBody J)

def sumInclusion : C(U.boundary ⊕ V.boundary, U.body ⊕ V.body) :=
  ⟨Sum.map U.inclusion V.inclusion, U.inclusion.continuous.sumMap V.inclusion.continuous⟩

theorem sumInclusion_isClosedEmbedding : IsClosedEmbedding (sumInclusion U V) := by
  apply (sumInclusion U V).continuous.isClosedEmbedding
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (U.closedEmbedding.injective (Sum.inl.inj h))
      | inr y => cases h
  | inr x =>
      cases y with
      | inl y => cases h
      | inr y => exact congrArg Sum.inr (V.closedEmbedding.injective (Sum.inr.inj h))

def sum : SmoothBoundaryBody J :=
  ofEmbedding (sumInclusion U V) (sumInclusion_isClosedEmbedding U V)

theorem sum_inclusion_inl (x : U.boundary) :
    (U.sum V).inclusion (Sum.inl x) = Sum.inl (U.inclusion x) := rfl

theorem sum_inclusion_inr (x : V.boundary) :
    (U.sum V).inclusion (Sum.inr x) = Sum.inr (V.inclusion x) := rfl

variable {U V} {U' V' : SmoothBoundaryBody J}

def sumEquiv (e : Equiv U U') (f : Equiv V V') : Equiv (U.sum V) (U'.sum V') where
  body := e.body.sumCongr f.body
  boundary := e.boundary.sumCongr f.boundary
  boundary_point := by
    intro x
    cases x with
    | inl x => exact congrArg Sum.inl (e.boundary_point x)
    | inr x => exact congrArg Sum.inr (f.boundary_point x)

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
