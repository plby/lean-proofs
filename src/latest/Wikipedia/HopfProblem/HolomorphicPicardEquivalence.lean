import Wikipedia.HopfProblem.HolomorphicPicardClassGluing
import Wikipedia.HopfProblem.HolomorphicPicardNativeGaugeComparison
import Wikipedia.HopfProblem.HolomorphicPicardCechClassInjectivityCriterion

/-!
# Original holomorphic line bundles are classified by genuine unit-sheaf H¹

The source consists of original native holomorphic line bundles modulo
actual analytic fibre-linear isomorphisms. Equality of their genuine
cohomology classes gives an actual coboundary on the common original
cover, hence a proved analytic isomorphism. Conversely, every cohomology
class has a proved cocycle representative and a genuinely glued native
bundle. Neither direction is a classification assumption.
-/

noncomputable section

open Bundle TopologicalSpace CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicard

open HolomorphicExponentialSheaf HolomorphicPicardNative
  PeriodTorusLineBundleClassificationNative

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

variable (V W : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W] [VectorBundle ℂ ℂ V] [VectorBundle ℂ ℂ W]
    [ContMDiffVectorBundle ω ℂ V I] [ContMDiffVectorBundle ω ℂ W I]

/-- Equality of actual derived classes detects genuine analytic
fibre-linear isomorphism of arbitrary original native bundles. -/
theorem nativeClass_eq_iff_nonempty_iso :
    nativeClass I M V = nativeClass I M W ↔ Nonempty (AnalyticBundleIso I V W) := by
  constructor
  · intro h
    apply (nonempty_analyticBundleIso_iff_commonCover_class_eq I M V W).mpr
    apply (CechClassInjectivity.classOf_eq_iff_coverClass_eq _ _
      (isoGaugeCover_covers M V W)).mp
    have hV := CechExtension.classOf_refinement Prod.fst (isoGaugeCover_le_left M V W)
      (nativeCocycle I M V) (nativeCover_covers M V) (isoGaugeCover_covers M V W)
    have hW := CechExtension.classOf_refinement Prod.snd (isoGaugeCover_le_right M V W)
      (nativeCocycle I M W) (nativeCover_covers M W) (isoGaugeCover_covers M V W)
    exact hV.trans (h.trans hW.symm)
  · rintro ⟨e⟩
    exact nativeClass_eq_of_iso I M V W e

namespace LineBundle

theorem cohomologyClass_eq_iff_nonempty_iso (V W : LineBundle.{u} I M) :
    cohomologyClass I M V = cohomologyClass I M W ↔
      Nonempty (AnalyticBundleIso I V.Fiber W.Fiber) :=
  nativeClass_eq_iff_nonempty_iso I M V.Fiber W.Fiber

theorem isoClassCohomologyClass_injective :
    Function.Injective (isoClassCohomologyClass.{u} I M) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h V =>
    induction y using Quotient.inductionOn with
    | h W =>
      intro h
      exact (toIsoClasses_eq_iff I M V W).mpr
        ((cohomologyClass_eq_iff_nonempty_iso I M V W).mp h)

theorem isoClassCohomologyClass_bijective :
    Function.Bijective (isoClassCohomologyClass.{0} I M) :=
  ⟨isoClassCohomologyClass_injective I M, isoClassCohomologyClass_surjective I M⟩

/-- Genuine classification: the actual native isomorphism-class quotient
is equivalent to mathlib's actual first cohomology of the original unit
sheaf. The source is not defined to be cohomology. -/
def classificationEquiv : IsoClasses.{0} I M ≃
    CategoryTheory.Sheaf.H.{0} (unitsSheaf I M) 1 :=
  Equiv.ofBijective (isoClassCohomologyClass I M) (isoClassCohomologyClass_bijective I M)

@[simp] theorem classificationEquiv_toIsoClasses (V : LineBundle.{0} I M) :
    classificationEquiv I M (toIsoClasses I M V) = cohomologyClass I M V := rfl

@[simp] theorem classificationEquiv_ofCocycle {ι : Type} (U : ι → Opens M)
    (hU : ∀ x : M, ∃ i, x ∈ U i)
    (c : HolomorphicFunctionSheaf.SphereH1.CechOneCocycle (unitsSheaf I M) U) :
    classificationEquiv I M (toIsoClasses I M (ofCocycle I M U hU c)) =
      CechExtension.classOf c hU := cohomologyClass_ofCocycle I M U hU c

end LineBundle

end Wikipedia.HopfProblem.HolomorphicPicard
