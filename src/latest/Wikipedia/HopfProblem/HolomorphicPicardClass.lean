import Wikipedia.HopfProblem.HolomorphicPicardBundles
import Wikipedia.HopfProblem.HolomorphicPicardNativeIsoGaugeCech
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinementClass
import Wikipedia.HopfProblem.HolomorphicPicardCechCoboundaryClass

/-!
# The genuine unit-sheaf cohomology class of an original line bundle

Every original native holomorphic line bundle supplies its actual native
transition cocycle. The proved cocycle extension gives an element of
mathlib's genuine `H¹(O*)`. Analytic fibre-linear isomorphisms give actual
changes of local frame on the common original cover, so this element
descends to the quotient of original native bundles by actual isomorphism.
No classification or tensor assertion is part of this construction.
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

variable (V : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V I]

/-- The actual derived unit-sheaf cohomology class of the original native
bundle, constructed from its original native transition maps. -/
def nativeClass : CategoryTheory.Sheaf.H.{0} (unitsSheaf I M) 1 :=
  CechExtension.classOf (nativeCocycle I M V) (nativeCover_covers M V)

variable (W : M → Type*)
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ W] [VectorBundle ℂ ℂ W] [ContMDiffVectorBundle ω ℂ W I]

theorem nativeClass_eq_of_iso (e : AnalyticBundleIso I V W) :
    nativeClass I M V = nativeClass I M W := by
  have hV := CechExtension.classOf_refinement Prod.fst (isoGaugeCover_le_left M V W)
    (nativeCocycle I M V) (nativeCover_covers M V) (isoGaugeCover_covers M V W)
  have hW := CechExtension.classOf_refinement Prod.snd (isoGaugeCover_le_right M V W)
    (nativeCocycle I M W) (nativeCover_covers M W) (isoGaugeCover_covers M V W)
  have h := CechExtension.classOf_eq_of_coboundary _ _ (isoGaugeCover_covers M V W)
    (isoGauge I M V W e) (nativeIso_refinement_sub_refinement I M V W e)
  exact hV.symm.trans (h.trans hW)

namespace LineBundle

/-- The genuine cohomology class of a bundled original native object. -/
def cohomologyClass (V : LineBundle.{u} I M) :
    CategoryTheory.Sheaf.H.{0} (unitsSheaf I M) 1 := nativeClass I M V.Fiber

theorem cohomologyClass_eq_of_iso (V W : LineBundle.{u} I M)
    (e : AnalyticBundleIso I V.Fiber W.Fiber) :
    cohomologyClass I M V = cohomologyClass I M W :=
  nativeClass_eq_of_iso I M V.Fiber W.Fiber e

/-- The map is defined on the quotient of actual original bundles, not
on a quotient chosen to make the desired classification tautological. -/
def isoClassCohomologyClass : IsoClasses.{u} I M →
    CategoryTheory.Sheaf.H.{0} (unitsSheaf I M) 1 :=
  Quotient.lift (cohomologyClass I M) (fun V W ⟨e⟩ => cohomologyClass_eq_of_iso I M V W e)

@[simp] theorem isoClassCohomologyClass_toIsoClasses (V : LineBundle.{u} I M) :
    isoClassCohomologyClass I M (toIsoClasses I M V) = cohomologyClass I M V := rfl

end LineBundle

end Wikipedia.HopfProblem.HolomorphicPicard
