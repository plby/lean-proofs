import Wikipedia.HopfProblem.CuspNormalizationSheafReducedBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafReducedLocality

/-!
# The genuine reduced holomorphic-function sheaf on a subset

The ring presheaf consists of literal locally ambient-holomorphic
functions. Its sheaf condition comes from proved locality and the
unique pointwise gluing of actual functions. In particular this sheaf
is not defined as the kernel of a normalization or branch map.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafReduced

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H) (S : Set M)

/-- The presheaf of the actual reduced section rings, with literal
restriction of functions as its morphisms. -/
def presheaf : TopCat.Presheaf CommRingCat (TopCat.of S) where
  obj U := CommRingCat.of (Section I S U.unop)
  map h := CommRingCat.ofHom (restriction I S (leOfHom h.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

instance presheaf_obj_coeFun (U : (Opens (TopCat.of S))ᵒᵖ) :
    CoeFun ((presheaf I S).obj U) (fun _ => U.unop → ℂ) where
  coe f := f.val

theorem presheaf_obj_eq (U : Opens S) :
    (presheaf I S).obj (op U) = CommRingCat.of (Section I S U) := rfl

@[simp] theorem presheaf_restriction_apply {U V : Opens S} (h : U ≤ V)
    (f : Section I S V) (x : U) :
    (presheaf I S).map (homOfLE h).op f x = f (Set.inclusion h x) := rfl

/-- The local-extension predicate gives a genuine sheaf of actual
functions by the proved local-predicate gluing theorem. -/
def typeSheaf : TopCat.Sheaf (Type) (TopCat.of S) :=
  TopCat.subsheafToTypes (localPredicate I S)

/-- Forgetting the actual ring operations gives literally the
function presheaf of the proved local predicate. -/
theorem forget_presheaf :
    presheaf I S ⋙ forget CommRingCat = (typeSheaf I S).obj := rfl

/-- The genuine ring-valued reduced holomorphic-function sheaf of the subset. -/
def sheaf : TopCat.Sheaf CommRingCat (TopCat.of S) where
  obj := presheaf I S
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (typeSheaf I S).property

instance sheaf_obj_coeFun (U : (Opens (TopCat.of S))ᵒᵖ) :
    CoeFun ((sheaf I S).obj.obj U) (fun _ => U.unop → ℂ) where
  coe f := f.val

theorem sheaf_obj_eq (U : Opens S) :
    (sheaf I S).obj.obj (op U) = CommRingCat.of (Section I S U) := rfl

/-- Every actual ring of sections of the sheaf is reduced. -/
instance sheaf_obj_isReduced (U : (Opens (TopCat.of S))ᵒᵖ) :
    IsReduced ((sheaf I S).obj.obj U) := section_isReduced I S U.unop

/-- The sheaf section algebras use the actual constant complex functions. -/
instance sheaf_obj_algebra (U : (Opens (TopCat.of S))ᵒᵖ) :
    Algebra ℂ ((sheaf I S).obj.obj U) := section_algebra I S U.unop

/-- The actual additive sheaf underlying the reduced holomorphic-function sheaf. -/
def additiveSheaf : TopCat.Sheaf AddCommGrpCat (TopCat.of S) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).obj
    (sheaf I S)

theorem additiveSheaf_obj_eq (U : Opens S) :
    (additiveSheaf I S).obj.obj (op U) = AddCommGrpCat.of (Section I S U) := rfl

instance additiveSheaf_obj_module (U : (Opens (TopCat.of S))ᵒᵖ) :
    Module ℂ ((additiveSheaf I S).obj.obj U) :=
  inferInstanceAs (Module ℂ (Section I S U.unop))

end Wikipedia.HopfProblem.CuspNormalization.SheafReduced
