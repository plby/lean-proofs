import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodySum
import Wikipedia.SmoothSixDPoincare.NativeInwardBoundaryCollar

/-! # Disjoint sums retain their actual inward collars -/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} (U V : SmoothBoundaryBody J)
  (C : InwardBoundaryCollar U.inclusion) (D : InwardBoundaryCollar V.inclusion)

def sumCollarMap : C((U.boundary ⊕ V.boundary) × unitInterval, U.body ⊕ V.body) :=
  ⟨fun q => Sum.map C.map D.map (Homeomorph.sumProdDistrib q),
    (C.map.continuous.sumMap D.map.continuous).comp Homeomorph.sumProdDistrib.continuous⟩

theorem sumCollarMap_injective : Injective (sumCollarMap U V C D) :=
  (Sum.map_injective.mpr ⟨C.closedEmbedding.injective, D.closedEmbedding.injective⟩).comp
    Homeomorph.sumProdDistrib.injective

theorem sumCollarMap_inner_image :
    sumCollarMap U V C D '' {q : (U.boundary ⊕ V.boundary) × unitInterval | q.2 < 1} =
      Sum.inl '' (C.map '' {q : U.boundary × unitInterval | q.2 < 1}) ∪
        Sum.inr '' (D.map '' {q : V.boundary × unitInterval | q.2 < 1}) := by
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, ht, rfl⟩
    cases x with
    | inl x => exact Or.inl ⟨_, ⟨(x, t), ht, rfl⟩, rfl⟩
    | inr x => exact Or.inr ⟨_, ⟨(x, t), ht, rfl⟩, rfl⟩
  · rintro (⟨_, ⟨q, hq, rfl⟩, rfl⟩ | ⟨_, ⟨q, hq, rfl⟩, rfl⟩)
    · exact ⟨(Sum.inl q.1, q.2), hq, rfl⟩
    · exact ⟨(Sum.inr q.1, q.2), hq, rfl⟩

def sumInwardCollar : InwardBoundaryCollar (U.sum V).inclusion where
  map := sumCollarMap U V C D
  closedEmbedding := (sumCollarMap U V C D).continuous.isClosedEmbedding
    (sumCollarMap_injective U V C D)
  zero := by
    intro x
    cases x with
    | inl x => exact congrArg Sum.inl (C.zero x)
    | inr x => exact congrArg Sum.inr (D.zero x)
  inner_open := by
    exact (sumCollarMap_inner_image U V C D).symm ▸
      (isOpenMap_inl _ C.inner_open).union (isOpenMap_inr _ D.inner_open)

theorem sum_hasInwardCollar (hU : U.HasInwardCollar) (hV : V.HasInwardCollar) :
    (U.sum V).HasInwardCollar := by
  obtain ⟨C⟩ := hU
  obtain ⟨D⟩ := hV
  exact ⟨sumInwardCollar U V C D⟩

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
