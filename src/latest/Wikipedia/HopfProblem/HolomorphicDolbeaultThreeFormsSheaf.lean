import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsOperations
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Topology.Sheaves.Forget

/-!
# The genuine additive sheaf of native antiholomorphic one-forms

The underlying functions are dependent sections in the original real
cotangent Hom bundle.  Smoothness and pointwise anti-linearity supply
the proved local predicate and hence the sheaf condition.  The additive
presheaf has exactly those native sections and literal restrictions.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The additive presheaf of actual smooth anti-linear native covectors. -/
def presheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of M) where
  obj U := AddCommGrpCat.of (FormSection E M U.unop)
  map h := AddCommGrpCat.ofHom (restrictionLinearMap E M (leOfHom h.unop)).toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

instance presheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((presheaf E M).obj U) (fun _ => ∀ x : U.unop, Covector E M (x : M)) where
  coe s := s.val

/-- The genuine sheaf condition follows from locality of the actual
native smooth section maps and their fibre anti-linearity. -/
theorem presheaf_isSheaf : (presheaf E M).IsSheaf := by
  change CategoryTheory.Presheaf.IsSheaf
    (Opens.grothendieckTopology (TopCat.of M)) (presheaf E M)
  rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget AddCommGrpCat)]
  exact (typeSheaf E M).property

/-- The original additive sheaf of actual smooth antiholomorphic
cotangent sections, without a closedness or local-exactness condition. -/
def sheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of M) where
  obj := presheaf E M
  property := presheaf_isSheaf E M

/-- The section groups are the actual native form sections. -/
theorem sheaf_obj_eq (U : Opens M) :
    (sheaf E M).obj.obj (op U) = AddCommGrpCat.of (FormSection E M U) := rfl

instance sheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((sheaf E M).obj.obj U) (fun _ => ∀ x : U.unop, Covector E M (x : M)) where
  coe s := s.val

instance sheaf_obj_module (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module ℂ ((sheaf E M).obj.obj U) :=
  inferInstanceAs (Module ℂ (FormSection E M U.unop))

@[simp] theorem sheaf_restriction {U V : Opens M} (h : U ≤ V) (s : FormSection E M V) :
    (sheaf E M).obj.map (homOfLE h).op s = restriction E M h s := rfl

/-- Forgetting the group structure recovers precisely the original
dependent local-predicate sheaf. -/
theorem forget_sheaf :
    (CategoryTheory.sheafCompose _ (CategoryTheory.forget AddCommGrpCat)).obj (sheaf E M) =
      typeSheaf E M := rfl

/-- Compatible native forms glue uniquely in the original cotangent
fibres, with the original smoothness and anti-linearity requirements. -/
theorem existsUnique_gluing {ι : Type} (U : ι → Opens M)
    (s : ∀ i, FormSection E M (U i))
    (hs : TopCat.Presheaf.IsCompatible (presheaf E M) U s) :
    ∃! t : FormSection E M (iSup U),
      ∀ i, restriction E M (le_iSup U i) t = s i := by
  obtain ⟨t, ht, huniq⟩ := (typeSheaf E M).existsUnique_gluing U s (by
    intro i j
    exact hs i j)
  exact ⟨t, ht, huniq⟩

/-- Native form-sheaf morphisms are determined by their literal fibre values. -/
theorem sheafEnd_ext {f g : sheaf E M ⟶ sheaf E M}
    (h : ∀ (U : Opens M) (s : FormSection E M U) (x : U),
      f.hom.app (op U) s x = g.hom.app (op U) s x) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact FormSection.ext E M (h U.unop s)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms
