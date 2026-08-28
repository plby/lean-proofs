import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedOperations
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsSheaf

/-!
# The genuine additive sheaf of closed native antiholomorphic forms

Sections are the original smooth anti-linear covectors satisfying the
actual coefficient PDE in all native charts.  The proved locality of
that equation supplies genuine sheaf gluing.  Forgetting closedness is
an injective morphism into the original native form sheaf.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual closed native forms with their literal additive restrictions. -/
def presheaf : TopCat.Presheaf AddCommGrpCat (TopCat.of M) where
  obj U := AddCommGrpCat.of (ClosedFormSection E M U.unop)
  map h := AddCommGrpCat.ofHom (restrictionLinearMap E M (leOfHom h.unop)).toAddMonoidHom
  map_id _ := rfl
  map_comp _ _ := rfl

instance presheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((presheaf E M).obj U) (fun _ => ∀ x : U.unop, Forms.Covector E M (x : M)) where
  coe s := s.val

/-- The additive sheaf condition is the proved local-predicate sheaf
condition for the original smoothness, anti-linearity, and actual PDE. -/
theorem presheaf_isSheaf : (presheaf E M).IsSheaf := by
  change CategoryTheory.Presheaf.IsSheaf
    (Opens.grothendieckTopology (TopCat.of M)) (presheaf E M)
  rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget AddCommGrpCat)]
  exact (typeSheaf E M).property

/-- The genuine additive sheaf defined by the actual closed-form PDE. -/
def sheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of M) where
  obj := presheaf E M
  property := presheaf_isSheaf E M

theorem sheaf_obj_eq (U : Opens M) :
    (sheaf E M).obj.obj (op U) = AddCommGrpCat.of (ClosedFormSection E M U) := rfl

instance sheaf_obj_coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((sheaf E M).obj.obj U) (fun _ => ∀ x : U.unop, Forms.Covector E M (x : M)) where
  coe s := s.val

instance sheaf_obj_module (U : (Opens (TopCat.of M))ᵒᵖ) :
    Module ℂ ((sheaf E M).obj.obj U) :=
  inferInstanceAs (Module ℂ (ClosedFormSection E M U.unop))

@[simp] theorem sheaf_restriction {U V : Opens M} (h : U ≤ V)
    (s : ClosedFormSection E M V) :
    (sheaf E M).obj.map (homOfLE h).op s = restriction E M h s := rfl

/-- Forgetting addition recovers exactly the original PDE-local-predicate sheaf. -/
theorem forget_sheaf :
    (CategoryTheory.sheafCompose _ (CategoryTheory.forget AddCommGrpCat)).obj (sheaf E M) =
      typeSheaf E M := rfl

/-- Compatible actual PDE solutions glue uniquely to a genuine closed
native form, without assuming or selecting a primitive. -/
theorem existsUnique_gluing {ι : Type} (U : ι → Opens M)
    (s : ∀ i, ClosedFormSection E M (U i))
    (hs : TopCat.Presheaf.IsCompatible (presheaf E M) U s) :
    ∃! t : ClosedFormSection E M (iSup U),
      ∀ i, restriction E M (le_iSup U i) t = s i := by
  obtain ⟨t, ht, huniq⟩ := (typeSheaf E M).existsUnique_gluing U s (by
    intro i j
    exact hs i j)
  exact ⟨t, ht, huniq⟩

/-- The inclusion forgets only the actual coefficient PDE and keeps
every original native smooth covector unchanged. -/
def inclusion : sheaf E M ⟶ Forms.sheaf E M where
  hom :=
    { app U := AddCommGrpCat.ofHom (toFormLinearMap E M U.unop).toAddMonoidHom
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        exact Forms.FormSection.ext E M fun _ => rfl }

@[simp] theorem inclusion_app (U : Opens M) (s : ClosedFormSection E M U) :
    (inclusion E M).hom.app (op U) s = ClosedFormSection.toForm E M s := rfl

@[simp] theorem inclusion_apply (U : Opens M) (s : ClosedFormSection E M U) (x : U) :
    (inclusion E M).hom.app (op U) s x = s x := rfl

/-- Forgetting the equation is a genuine monomorphism of sheaves. -/
instance inclusion_mono : Mono (inclusion E M) := by
  have h (U : (Opens (TopCat.of M))ᵒᵖ) : Mono ((inclusion E M).hom.app U) :=
    ConcreteCategory.mono_of_injective _ (toFormLinearMap_injective E M U.unop)
  have : Mono (inclusion E M).hom := NatTrans.mono_of_mono_app _
  exact (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of M)).mono_of_mono_map this

/-- The original native form lies in this inclusion precisely when it
satisfies the stated actual PDE; no additional exactness condition is hidden. -/
theorem exists_lift_iff_isClosed (U : Opens M) (s : Forms.FormSection E M U) :
    (∃ t : ClosedFormSection E M U, (inclusion E M).hom.app (op U) t = s) ↔
      IsClosed E M U s.val := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ClosedFormSection.isClosed E M t
  · intro hs
    exact ⟨sectionMk E M U s hs, rfl⟩

/-- Endomorphisms of the closed-form sheaf are determined by their
original pointwise native covector maps. -/
theorem sheafEnd_ext {f g : sheaf E M ⟶ sheaf E M}
    (h : ∀ (U : Opens M) (s : ClosedFormSection E M U) (x : U),
      f.hom.app (op U) s x = g.hom.app (op U) s x) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact ClosedFormSection.ext E M (h U.unop s)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms
