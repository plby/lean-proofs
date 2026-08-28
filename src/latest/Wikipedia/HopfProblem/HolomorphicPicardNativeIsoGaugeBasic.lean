import Wikipedia.HopfProblem.HolomorphicPicardNativeCocycle
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# Actual local scalar coordinates of a native analytic bundle isomorphism

The common cover consists of intersections of the two original native
trivializing covers. The scalar function is extracted from the actual image
of the vector with source coordinate one. Its nonvanishing and its action
on every fibre vector follow from the original fibrewise linear equivalence.
-/

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open PeriodTorusLineBundleClassificationNative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (V W : M → Type*)
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W]

/-- The common cover uses the original native chart indices on both sides. -/
def isoGaugeCover (a : M × M) : Opens M := nativeCover M V a.1 ⊓ nativeCover M W a.2

theorem isoGaugeCover_covers (x : M) : ∃ a : M × M, x ∈ isoGaugeCover M V W a :=
  ⟨(x, x), FiberBundle.mem_baseSet_trivializationAt ℂ V x,
    FiberBundle.mem_baseSet_trivializationAt ℂ W x⟩

theorem isoGaugeCover_le_left (a : M × M) :
    isoGaugeCover M V W a ≤ nativeCover M V a.1 := inf_le_left

theorem isoGaugeCover_le_right (a : M × M) :
    isoGaugeCover M V W a ≤ nativeCover M W a.2 := inf_le_right

variable [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [VectorBundle ℂ ℂ V] [VectorBundle ℂ ℂ W]

/-- The actual target-chart coordinate of the image of the source-chart
unit vector. No scalar gauge or existence premise is supplied. -/
def isoGaugeValue (e : AnalyticBundleIso I V W) (a : M × M)
    (x : isoGaugeCover M V W a) : ℂ :=
  (nativeTriv W a.2 (e.diffeomorph
    ((nativeTriv V a.1).toOpenPartialHomeomorph.symm ((x : M), 1)))).2

/-- Express the original fibre equivalence in the two fixed native charts. -/
def isoGaugeLinearEquiv (e : AnalyticBundleIso I V W) (a : M × M)
    (x : isoGaugeCover M V W a) : ℂ ≃ₗ[ℂ] ℂ :=
  (((nativeTriv V a.1).linearEquivAt ℂ (x : M) x.property.1).symm.trans
    (e.fiberEquiv x)).trans ((nativeTriv W a.2).linearEquivAt ℂ (x : M) x.property.2)

/-- The actual total-space definition and actual fibrewise definition agree. -/
theorem isoGaugeValue_eq_linearEquiv (e : AnalyticBundleIso I V W) (a : M × M)
    (x : isoGaugeCover M V W a) :
    isoGaugeValue I M V W e a x = isoGaugeLinearEquiv I M V W e a x 1 := by
  unfold isoGaugeValue
  rw [← (nativeTriv V a.1).mk_symm x.property.1 1, e.map_fiber]
  rfl

/-- The extracted scalar is nonzero because the original fibre map and
both native coordinate maps are actual linear equivalences. -/
theorem isoGaugeValue_ne_zero (e : AnalyticBundleIso I V W) (a : M × M)
    (x : isoGaugeCover M V W a) : isoGaugeValue I M V W e a x ≠ 0 := by
  rw [isoGaugeValue_eq_linearEquiv]
  exact (map_ne_zero_iff (isoGaugeLinearEquiv I M V W e a x)
    (isoGaugeLinearEquiv I M V W e a x).injective).mpr one_ne_zero

/-- Fibrewise complex linearity forces the scalar's action on all coordinates. -/
theorem isoGaugeLinearEquiv_apply (e : AnalyticBundleIso I V W) (a : M × M)
    (x : isoGaugeCover M V W a) (z : ℂ) :
    isoGaugeLinearEquiv I M V W e a x z = isoGaugeValue I M V W e a x * z := by
  rw [isoGaugeValue_eq_linearEquiv]
  calc
    _ = isoGaugeLinearEquiv I M V W e a x (z • (1 : ℂ)) := by
      rw [smul_eq_mul, mul_one]
    _ = z • isoGaugeLinearEquiv I M V W e a x 1 := map_smul _ _ _
    _ = _ := mul_comm _ _

/-- In any pair of original native charts, the coordinate of the actual
image of a fibre vector is multiplication by the extracted scalar. -/
theorem isoGaugeValue_coordinate (e : AnalyticBundleIso I V W) (a : M × M)
    (x : isoGaugeCover M V W a) (v : V x) :
    (nativeTriv W a.2).linearEquivAt ℂ (x : M) x.property.2 (e.fiberEquiv x v) =
      isoGaugeValue I M V W e a x *
        (nativeTriv V a.1).linearEquivAt ℂ (x : M) x.property.1 v := by
  have h := isoGaugeLinearEquiv_apply I M V W e a x
    ((nativeTriv V a.1).linearEquivAt ℂ (x : M) x.property.1 v)
  simpa only [isoGaugeLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] using h

end Wikipedia.HopfProblem.HolomorphicPicardNative
