import Wikipedia.HopfProblem.HolomorphicPicardGroup
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassNaturality

/-!
# Actual exponential-cocycle bundles on a holomorphically H¹-acyclic base

Vanishing of the original additive holomorphic sheaf's degree-one
cohomology makes every actual exponentiated additive cocycle class zero.
The proved classification of original native line bundles then produces
a genuine analytic fibre-linear isomorphism with the original trivial
bundle.  No topological classification or Chern-class assertion is used.
-/

noncomputable section

open Bundle TopologicalSpace CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.LineBundleNormalization.Exponential

open HolomorphicExponentialSheaf HolomorphicPicard HolomorphicPicardNative
open HolomorphicFunctionSheaf.SphereH1 PeriodTorusLineBundleClassificationNative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (hO : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf I M) 1))
    {ι : Type} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i)
    (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf I M) U)

/-- The native class of the original bundle glued from an actual
exponential cocycle is zero by genuine coefficient-map naturality. -/
theorem nativeClass_eq_zero :
    nativeClass I M
      (cocycleCore I M U hU (Cech.mapCocycle (exponential I M) c)).Fiber = 0 := by
  have hc : CechExtension.classOf c hU = 0 := hO.elim _ _
  calc
    _ = CechExtension.classOf (Cech.mapCocycle (exponential I M) c) hU :=
      nativeClass_glued I M U hU _
    _ = CategoryTheory.Sheaf.H.map (exponential I M) 1 (CechExtension.classOf c hU) :=
      (CechExtension.classOf_naturality (exponential I M) c hU).symm
    _ = 0 := by rw [hc]; exact map_zero _

/-- Genuine analytic triviality of the original native exponential
bundle, obtained from the already proved native classification theorem. -/
theorem native_trivial :
    Nonempty (AnalyticBundleIso I
      (cocycleCore I M U hU (Cech.mapCocycle (exponential I M) c)).Fiber
      (Bundle.Trivial M ℂ)) := by
  apply (nativeClass_eq_iff_nonempty_iso I M
    (cocycleCore I M U hU (Cech.mapCocycle (exponential I M) c)).Fiber
    (Bundle.Trivial M ℂ)).mp
  exact (nativeClass_eq_zero I M hO U hU c).trans
    (LineBundle.cohomologyClass_trivialBundle I M).symm

end Wikipedia.HopfProblem.LineBundleNormalization.Exponential
