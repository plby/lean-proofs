import Wikipedia.HopfProblem.HolomorphicPicardClass
import Wikipedia.HopfProblem.HolomorphicPicardNativeGluingCocycle
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionRepresentation

/-!
# Every genuine unit-sheaf cohomology class is realized by a native bundle

The proved extension representation gives an actual unit cocycle on an
actual cover. Gluing constructs a genuine native holomorphic line bundle.
Its original native cocycle is the proved refinement of the input cocycle,
so its genuine cohomology class is precisely the original given class.
-/

noncomputable section

open Bundle TopologicalSpace CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicPicard

open HolomorphicExponentialSheaf HolomorphicPicardNative
  HolomorphicFunctionSheaf.SphereH1

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    {ι : Type} (U : ι → Opens M) (hU : ∀ x : M, ∃ i, x ∈ U i)
    (c : CechOneCocycle (unitsSheaf I M) U)

theorem nativeClass_glued :
    nativeClass I M (cocycleCore I M U hU c).Fiber = CechExtension.classOf c hU := by
  have hc := congrArg
    (fun t : CechOneCocycle (unitsSheaf I M)
        (nativeCover M (cocycleCore I M U hU c).Fiber) =>
      CechExtension.classOf t (nativeCover_covers M (cocycleCore I M U hU c).Fiber))
    (nativeCocycle_glued_eq_refinement I M U hU c)
  exact hc.trans (CechExtension.classOf_refinement
    (cocycleTransitionData I M U hU c).indexAt (fun _ => le_rfl) c hU
    (nativeCover_covers M (cocycleCore I M U hU c).Fiber))

namespace LineBundle

/-- The genuine native bundle obtained by gluing actual unit sections.
This constructs an object of the original unrestricted bundle type. -/
def ofCocycle : LineBundle.{0} I M := ofFamily I M (cocycleCore I M U hU c).Fiber

@[simp] theorem ofCocycle_fiber :
    (ofCocycle I M U hU c).Fiber = (cocycleCore I M U hU c).Fiber := rfl

theorem cohomologyClass_ofCocycle :
    cohomologyClass I M (ofCocycle I M U hU c) = CechExtension.classOf c hU :=
  nativeClass_glued I M U hU c

/-- Every class of the original unit sheaf is realized by an actual native
holomorphic line bundle, with no cocycle-representation premise. -/
theorem cohomologyClass_surjective : Function.Surjective (cohomologyClass.{0} I M) := by
  intro ξ
  obtain ⟨U, hU, c, hc⟩ := CechExtension.exists_classOf_eq (unitsSheaf I M) ξ
  exact ⟨ofCocycle I M U hU c, (cohomologyClass_ofCocycle I M U hU c).trans hc⟩

theorem isoClassCohomologyClass_surjective :
    Function.Surjective (isoClassCohomologyClass.{0} I M) := by
  intro ξ
  obtain ⟨V, hV⟩ := cohomologyClass_surjective I M ξ
  exact ⟨toIsoClasses I M V, hV⟩

end LineBundle

end Wikipedia.HopfProblem.HolomorphicPicard
