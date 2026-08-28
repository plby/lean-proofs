import Wikipedia.NoExoticSixSphere.RoundedTraceVerticalFrame

/-!
# The actual tangent image and the vertical frame give a direct sum

Normal projection kills the tangent summand and recovers the original
orthonormal frame from the vertical summand. This proves bijectivity of the
actual combined operator, without asserting smoothness of raw tangent coordinates.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem graphNormalProjection_eq_zero_iff (p : ambientSet A) (v : TimeGraphSpace (e := e)) :
    timeGraphNormalProjection A p v = 0 ↔ v ∈ (timeGraphDifferential A p).range := by
  change v ∈ (timeGraphDifferential A p).rangeᗮ.starProjection.ker ↔ _
  rw [Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]

theorem normalProjection_timeGraphDifferential (p : ambientSet A) (v : ℝ × Vector 6) :
    timeGraphNormalProjection A p (timeGraphDifferential A p v) = 0 :=
  (graphNormalProjection_eq_zero_iff A p _).mpr ⟨v, rfl⟩

def transverseSum (p : ambientSet A) :
    ((ℝ × Vector 6) × TimeGraphFrameSpace (e := e)) →L[ℝ] TimeGraphSpace (e := e) :=
  (timeGraphDifferential A p).coprod (verticalFrame A p)

theorem transverseSum_apply (p : ambientSet A)
    (v : (ℝ × Vector 6) × TimeGraphFrameSpace (e := e)) :
    transverseSum A p v = timeGraphDifferential A p v.1 + verticalFrame A p v.2 := rfl

theorem normalProjection_transverseSum (p : ambientSet A)
    (v : (ℝ × Vector 6) × TimeGraphFrameSpace (e := e)) :
    timeGraphNormalProjection A p (transverseSum A p v) = timeGraphFrame A p v.2 := by
  rw [transverseSum_apply, map_add, normalProjection_timeGraphDifferential,
    normalProjection_verticalFrame, zero_add]

theorem injective_transverseSum (p : ambientSet A) : Injective (transverseSum A p) := by
  rintro ⟨x, v⟩ ⟨y, w⟩ he
  have hP := congrArg (timeGraphNormalProjection A p) he
  rw [normalProjection_transverseSum, normalProjection_transverseSum] at hP
  have hv : v = w := injective_timeGraphFrame A p hP
  subst w
  change timeGraphDifferential A p x + verticalFrame A p v =
    timeGraphDifferential A p y + verticalFrame A p v at he
  exact Prod.ext (injective_timeGraphDifferential A p (add_right_cancel he)) rfl

theorem surjective_transverseSum (p : ambientSet A) : Surjective (transverseSum A p) := by
  intro y
  have hnormal : timeGraphNormalProjection A p y ∈ (timeGraphFrame A p).range := by
    rw [timeGraphFrame_range]
    exact (timeGraphDifferential A p).rangeᗮ.starProjection_apply_mem y
  obtain ⟨v, hv⟩ := hnormal
  change timeGraphFrame A p v = timeGraphNormalProjection A p y at hv
  have ht : y - verticalFrame A p v ∈ (timeGraphDifferential A p).range := by
    apply (graphNormalProjection_eq_zero_iff A p _).mp
    rw [map_sub, normalProjection_verticalFrame, hv, sub_self]
  obtain ⟨x, hx⟩ := ht
  change timeGraphDifferential A p x = y - verticalFrame A p v at hx
  refine ⟨(x, v), ?_⟩
  rw [transverseSum_apply, hx, sub_add_cancel]

def transverseSumEquiv (p : ambientSet A) :
    ((ℝ × Vector 6) × TimeGraphFrameSpace (e := e)) ≃L[ℝ] TimeGraphSpace (e := e) :=
  ContinuousLinearEquiv.ofBijective (transverseSum A p)
    (LinearMap.ker_eq_bot.mpr (injective_transverseSum A p))
    (LinearMap.range_eq_top.mpr (surjective_transverseSum A p))

theorem transverseSumEquiv_apply (p : ambientSet A)
    (v : (ℝ × Vector 6) × TimeGraphFrameSpace (e := e)) :
    transverseSumEquiv A p v = timeGraphDifferential A p v.1 + verticalFrame A p v.2 := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
