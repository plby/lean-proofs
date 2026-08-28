import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryTimeCollar
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarHalf
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Positive surgery preserves the actual entire negative half

Every nonpositive point is in the retained time region, where the
original surgery map preserves time exactly. Conversely the actual
target cover and positivity of the handle put every nonpositive target
point in that image. Restricting the original embedding therefore gives
a homeomorphism of the literal negative halves in all homology degrees.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare SingularMayerVietoris PeriodTorusHigherHomology

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

omit [CompactSpace M] [IsManifold (𝓡 7) ∞ M] [T2Space M] in
theorem nonpositive_mem_retainedTimeBand {p : M} (hp : 0 ≤ -T.time p) :
    p ∈ retainedTimeBand A T :=
  (neg_nonneg.mp hp).trans_lt (half_pos T.margin_pos)

def negativeRetainedPoint :
    C(TimeCollar.NonnegativeHalf (fun p ↦ -T.time p), retainedTimeBand A T) :=
  ⟨fun p ↦ ⟨p.val, nonpositive_mem_retainedTimeBand A T p.property⟩,
    continuous_subtype_val.subtype_mk _⟩

omit [CompactSpace M] [IsManifold (𝓡 7) ∞ M] [T2Space M] in
theorem negativeRetainedPoint_isEmbedding : IsEmbedding (negativeRetainedPoint A T) :=
  IsEmbedding.of_comp (negativeRetainedPoint A T).continuous continuous_subtype_val
    IsEmbedding.subtypeVal

theorem negativeRetainedPoint_time (p : TimeCollar.NonnegativeHalf (fun p ↦ -T.time p)) :
    timeFunction A hR T (retainedTimeMap A hR T (negativeRetainedPoint A T p)) = T.time p.val :=
  timeFunction_retainedTimeMap A hR T _

theorem negativeRetainedPoint_nonpositive
    (p : TimeCollar.NonnegativeHalf (fun p ↦ -T.time p)) :
    0 ≤ -timeFunction A hR T (retainedTimeMap A hR T (negativeRetainedPoint A T p)) := by
  rw [negativeRetainedPoint_time]
  exact p.property

def negativeHalfMap :
    C(TimeCollar.NonnegativeHalf (fun p ↦ -T.time p),
      TimeCollar.NonnegativeHalf (fun p ↦ -timeFunction A hR T p)) :=
  ⟨fun p ↦ ⟨retainedTimeMap A hR T (negativeRetainedPoint A T p),
      negativeRetainedPoint_nonpositive A hR T p⟩,
    ((isOpenEmbedding_retainedTimeMap A hR T).continuous.comp
      (negativeRetainedPoint A T).continuous).subtype_mk _⟩

theorem negativeHalfMap_isEmbedding : IsEmbedding (negativeHalfMap A hR T) :=
  IsEmbedding.of_comp (negativeHalfMap A hR T).continuous continuous_subtype_val
    ((isOpenEmbedding_retainedTimeMap A hR T).isEmbedding.comp
      (negativeRetainedPoint_isEmbedding A T))

theorem negativeHalfMap_surjective : Surjective (negativeHalfMap A hR T) := by
  rintro ⟨p, hp⟩
  rcases FramedSurgery.cover (E := Vector 4) (face A hR) 3 p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hq : 0 ≤ -T.time q.val := by
      apply neg_nonneg.mpr
      by_contra hn
      have hpos := SurgeryTimeProfile.profile_pos (δ := T.margin) (lt_of_not_ge hn)
      change 0 ≤ -SurgeryTimeProfile.profile T.margin (T.time q.val) at hp
      exact (not_lt_of_ge (neg_nonneg.mp hp)) hpos
    exact ⟨⟨q.val, hq⟩, Subtype.ext rfl⟩
  · have hu : (0 : ℝ) ≤ -1 := hp
    norm_num at hu

def negativeHalfHomeomorph :
    TimeCollar.NonnegativeHalf (fun p ↦ -T.time p) ≃ₜ
      TimeCollar.NonnegativeHalf (fun p ↦ -timeFunction A hR T p) :=
  (negativeHalfMap_isEmbedding A hR T).toHomeomorphOfSurjective
    (negativeHalfMap_surjective A hR T)

theorem negativeHalfHomeomorph_time
    (p : TimeCollar.NonnegativeHalf (fun p ↦ -T.time p)) :
    timeFunction A hR T (negativeHalfHomeomorph A hR T p).val = T.time p.val :=
  negativeRetainedPoint_time A hR T p

def negativeHalfHomologyEquiv (k : ℕ) :
    SingularHomology (TimeCollar.NonnegativeHalf (fun p ↦ -T.time p)) k ≃ₗ[ℤ]
      SingularHomology (TimeCollar.NonnegativeHalf (fun p ↦ -timeFunction A hR T p)) k :=
  homeomorphHomologyEquiv (negativeHalfHomeomorph A hR T) k

theorem negativeHalf_homology_finite (k : ℕ)
    [Finite (SingularHomology (TimeCollar.NonnegativeHalf (fun p ↦ -T.time p)) k)] :
    Finite (SingularHomology
      (TimeCollar.NonnegativeHalf (fun p ↦ -timeFunction A hR T p)) k) :=
  Finite.of_injective _ (negativeHalfHomologyEquiv A hR T k).symm.injective

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
