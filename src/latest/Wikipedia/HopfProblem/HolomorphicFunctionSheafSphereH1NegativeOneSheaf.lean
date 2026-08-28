import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSheafBasic

/-!
# The actual ideal sheaf of functions vanishing at infinity

The presheaf of literal vanishing ideals is a genuine additive sheaf.
Actual compatible families glue in the holomorphic-function sheaf, and
the gluing vanishes at infinity because one member of the cover contains
that point. Local frames, proved separately, identify this ideal sheaf
with the degree-minus-one holomorphic line bundle.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- The actual vanishing-ideal presheaf satisfies the actual sheaf
condition; no gluing or locality hypothesis is imposed. -/
theorem negativeOnePresheaf_isSheaf : negativeOnePresheaf.IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing negativeOnePresheaf).mpr
  intro ι U s hs
  let sf : ∀ i : ι, Section sphereSheaf (U i) := fun i => (s i).val
  have hsf : TopCat.Presheaf.IsCompatible sphereSheaf.obj U sf := by
    intro i j
    exact congrArg (fun t : NegativeOneSection (U i ⊓ U j) => t.val) (hs i j)
  obtain ⟨f, hf, huniq⟩ := sphereSheaf.existsUnique_gluing U sf hsf
  have hfvanish : f ∈ vanishingIdeal (iSup U) := by
    intro hinfty
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hinfty
    have he := congrArg
      (fun g : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere (U i) => g ⟨∞, hi⟩)
      (hf i)
    exact he.trans ((s i).property hi)
  refine ⟨⟨f, hfvanish⟩, ?_, ?_⟩
  · intro i
    exact Subtype.ext (hf i)
  · intro q hq
    apply Subtype.ext
    apply huniq q.val
    intro i
    exact congrArg (fun t : NegativeOneSection (U i) => t.val) (hq i)

/-- The genuine additive sheaf of actual holomorphic functions vanishing
at infinity on the constructed analytic Riemann sphere. -/
def negativeOneSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of RiemannSphere) where
  obj := negativeOnePresheaf
  property := negativeOnePresheaf_isSheaf

/-- The sheaf sections are definitionally the literal vanishing ideals. -/
theorem negativeOneSheaf_obj_eq (U : Opens RiemannSphere) :
    negativeOneSheaf.obj.obj (op U) = AddCommGrpCat.of (NegativeOneSection U) := rfl

/-- Complex scalars act by the actual pointwise scalar multiplication. -/
instance negativeOneSheaf_obj_module (U : (Opens (TopCat.of RiemannSphere))ᵒᵖ) :
    Module ℂ (negativeOneSheaf.obj.obj U) := negativeOneSectionModule U.unop

/-- The section-to-ideal identification is the identity on actual values,
not a noncanonical comparison with a substitute model. -/
def negativeOneSectionEquiv (U : Opens RiemannSphere) :
    Section negativeOneSheaf U ≃ₗ[ℂ] NegativeOneSection U :=
  LinearEquiv.refl ℂ _

@[simp] theorem negativeOneSectionEquiv_apply (U : Opens RiemannSphere)
    (s : Section negativeOneSheaf U) : negativeOneSectionEquiv U s = s := rfl

@[simp] theorem negativeOne_res_val {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : NegativeOneSection V) :
    (res negativeOneSheaf h s).val = res sphereSheaf h s.val := rfl

/-- The actual inclusion of the vanishing-ideal sheaf into the sheaf
of all holomorphic functions. -/
def negativeOneInclusion : negativeOneSheaf ⟶ sphereSheaf :=
  ObjectProperty.homMk negativeOnePresheafInclusion

@[simp] theorem negativeOneInclusion_apply (U : Opens RiemannSphere)
    (s : NegativeOneSection U) :
    negativeOneInclusion.hom.app (op U) s = s.val := rfl

/-- The actual inclusion is injective on every section group. -/
theorem negativeOneInclusion_app_injective (U : Opens RiemannSphere) :
    Function.Injective (negativeOneInclusion.hom.app (op U)) :=
  Subtype.val_injective

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
