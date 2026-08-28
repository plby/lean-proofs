import Wikipedia.HopfProblem.ThreefoldLineBundleChern
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassNaturality

/-!
# Actual exponential-cocycle presentations of the original bundles

The proved original exponential map is surjective on genuine first sheaf
cohomology of the constructed threefold.  Representing a preimage by an
actual additive cocycle and gluing its actual exponential gives a native
holomorphic bundle analytically isomorphic to the original bundle.

No topological classification premise or continuous trivialization is
assumed in constructing this genuine analytic bundle isomorphism.
-/

noncomputable section

open Bundle TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleTrivialization

open HolomorphicExponentialSheaf HolomorphicPicard HolomorphicPicardNative
  HolomorphicFunctionSheaf.SphereH1 PeriodTorusLineBundleClassificationNative

universe u

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

variable (V : Space → Type u)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IF]

/-- Every original native bundle is genuinely analytically isomorphic to
the native bundle glued from an actual exponentiated additive cocycle. -/
theorem exists_exponential_cocycle_iso :
    ∃ (U : Space → Opens Space) (hU : ∀ x : Space, ∃ i, x ∈ U i)
      (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf IF Space) U),
      Nonempty (AnalyticBundleIso IF
        (cocycleCore IF Space U hU (Cech.mapCocycle (exponential IF Space) c)).Fiber V) := by
  obtain ⟨ξ, hξ⟩ := PicardExponential.exponentialH1_surjective (nativeClass IF Space V)
  obtain ⟨U, hU, c, hc⟩ :=
    CechExtension.exists_classOf_eq (HolomorphicFunctionSheaf.additiveSheaf IF Space) ξ
  refine ⟨U, hU, c, ?_⟩
  apply (nativeClass_eq_iff_nonempty_iso IF Space
    (cocycleCore IF Space U hU (Cech.mapCocycle (exponential IF Space) c)).Fiber V).mp
  calc
    nativeClass IF Space
        (cocycleCore IF Space U hU (Cech.mapCocycle (exponential IF Space) c)).Fiber =
        CechExtension.classOf (Cech.mapCocycle (exponential IF Space) c) hU :=
      nativeClass_glued IF Space U hU _
    _ = CategoryTheory.Sheaf.H.map (exponential IF Space) 1 (CechExtension.classOf c hU) :=
      (CechExtension.classOf_naturality (exponential IF Space) c hU).symm
    _ = nativeClass IF Space V := by rw [hc]; exact hξ

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LineBundleTrivialization
