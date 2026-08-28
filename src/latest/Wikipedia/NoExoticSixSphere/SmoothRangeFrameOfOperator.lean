import Wikipedia.NoExoticSixSphere.SmoothFrameCoordinates

/-!
# Smooth range frames from an actual injective operator family
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothRangeFrame

variable {B H M E K : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  {P : M → E →L[ℝ] E}

theorem ambient_range_eq (a : SmoothRangeFrame I P K) (p : M) :
    (a.ambient p).range = (P p).range := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact (a.equiv p v).property
  · intro hy
    obtain ⟨v, hv⟩ := (a.equiv p).surjective ⟨y, hy⟩
    exact ⟨v, congrArg Subtype.val hv⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ K]
  (A : M → K →L[ℝ] E) (hA : ContMDiff I 𝓘(ℝ, K →L[ℝ] E) ∞ A)
  (hi : ∀ p, Function.Injective (A p)) (hr : ∀ p, (A p).range = (P p).range)

def ofOperator : SmoothRangeFrame I P K := by
  let q (p : M) : K ≃L[ℝ] (P p).range :=
    (LinearEquiv.ofInjective (A p).toLinearMap (hi p)).toContinuousLinearEquiv.trans
      (ContinuousLinearEquiv.ofEq _ _ (hr p))
  refine ⟨q, ?_⟩
  have he : (fun p ↦ (P p).range.subtypeL.comp (q p).toContinuousLinearMap) = A := by
    funext p
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [he]
  exact hA

theorem ofOperator_ambient (p : M) : (ofOperator A hA hi hr).ambient p = A p := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

end NoExoticSixSphere.SmoothRangeFrame
