import Wikipedia.HopfProblem.HolomorphicPicardNativeIsoGaugeSmooth
import Wikipedia.HopfProblem.HolomorphicPicardNativeIsoGaugeRelation
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinement

/-!
# An actual native bundle isomorphism gives an actual Čech coboundary

The actual scalar coefficients of the original analytic isomorphism form
a zero cochain of the genuine holomorphic unit sheaf. On the common original
cover, the source cocycle minus the target cocycle is its coboundary.
Thus the two refined Čech classes agree; no scalar gauge is assumed.
-/

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open PeriodTorusLineBundleClassificationNative HolomorphicExponentialSheaf
  HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.Cech

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Additive subtraction of actual unit sections evaluates as a quotient. -/
theorem unitSectionEval_sub {U : Opens M} (u v : UnitSection I M U) (x : U) :
    unitSectionEval (u - v) x = unitSectionEval u x / unitSectionEval v x := by
  rw [sub_eq_add_neg, unitSectionEval_add, unitSectionEval_neg, div_eq_mul_inv]

variable (V W : M → Type*)
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W]
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [VectorBundle ℂ ℂ V] [VectorBundle ℂ ℂ W]
    [ContMDiffVectorBundle ω ℂ V I] [ContMDiffVectorBundle ω ℂ W I]

/-- The actual unit zero cochain extracted from the original native
analytic bundle isomorphism in pairs of original native charts. -/
def isoGauge (e : AnalyticBundleIso I V W) :
    ZeroCochain (unitsSheaf I M) (isoGaugeCover M V W) := isoGaugeUnit I M V W e

@[simp] theorem isoGauge_apply (e : AnalyticBundleIso I V W) (a : M × M) :
    isoGauge I M V W e a = isoGaugeUnit I M V W e a := rfl

@[simp] theorem isoGauge_eval (e : AnalyticBundleIso I V W) (a : M × M)
    (x : isoGaugeCover M V W a) :
    unitSectionEval (isoGauge I M V W e a) x = isoGaugeValue I M V W e a x := rfl

/-- The original isomorphism proves the precise Čech coboundary identity
after refining both original native covers to their common intersections. -/
theorem nativeIso_refinement_sub_refinement (e : AnalyticBundleIso I V W) :
    refinement (unitsSheaf I M) (V := isoGaugeCover M V W) Prod.fst
        (isoGaugeCover_le_left M V W) (nativeCocycle I M V) -
      refinement (unitsSheaf I M) (V := isoGaugeCover M V W) Prod.snd
        (isoGaugeCover_le_right M V W) (nativeCocycle I M W) =
      coboundary (unitsSheaf I M) (isoGaugeCover M V W) (isoGauge I M V W e) := by
  apply cocycle_ext
  intro a b
  apply unitSection_ext
  intro x
  rw [sub_value, refinement_value, refinement_value, coboundary_value]
  change (scalarTransition V a.1 b.1 (x : M) : ℂ) /
      (scalarTransition W a.2 b.2 (x : M) : ℂ) =
    isoGaugeValue I M V W e a ⟨x, x.property.1⟩ /
      isoGaugeValue I M V W e b ⟨x, x.property.2⟩
  exact isoGaugeValue_transition_div I M V W e a b x x.property

/-- Actual analytically isomorphic native bundles have equal Čech classes
on the constructed common refinement of their original chart covers. -/
theorem nativeIso_refined_class_eq (e : AnalyticBundleIso I V W) :
    classOf (unitsSheaf I M) (isoGaugeCover M V W)
        (refinement (unitsSheaf I M) (V := isoGaugeCover M V W) Prod.fst
          (isoGaugeCover_le_left M V W) (nativeCocycle I M V)) =
      classOf (unitsSheaf I M) (isoGaugeCover M V W)
        (refinement (unitsSheaf I M) (V := isoGaugeCover M V W) Prod.snd
          (isoGaugeCover_le_right M V W) (nativeCocycle I M W)) := by
  apply (class_eq_class_iff (unitsSheaf I M) (isoGaugeCover M V W) _ _).mpr
  rw [nativeIso_refinement_sub_refinement I M V W e]
  exact ⟨isoGauge I M V W e, fun _ _ => rfl⟩

end Wikipedia.HopfProblem.HolomorphicPicardNative
