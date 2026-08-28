import Wikipedia.HopfProblem.HolomorphicExponentialSheafUnitsSections
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The exponential morphism of the genuine holomorphic sheaves

Ordinary complex exponentiation is holomorphic in the original charts.
Its value and inverse are the actual functions `exp ∘ f` and `exp ∘ (-f)`.
The exponential addition formula and literal restriction yield a natural
morphism from the additive holomorphic sheaf to its actual units sheaf.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {U : Opens M}

/-- Ordinary complex exponentiation of an actual holomorphic section. -/
def exponentialFunctionSection (f : HolomorphicFunctionSheaf.Section I M U) :
    HolomorphicFunctionSheaf.Section I M U :=
  ⟨fun x => Complex.exp (f x),
    (Complex.contDiff_exp (𝕜 := ℂ)).contMDiff.comp f.contMDiff⟩

@[simp]
theorem exponentialFunctionSection_apply
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    exponentialFunctionSection f x = Complex.exp (f x) := rfl

/-- The exponential as a genuine unit of the actual holomorphic section ring.
The inverse section is explicitly the exponential of the negative section. -/
def exponentialSection (f : HolomorphicFunctionSheaf.Section I M U) : UnitSection I M U :=
  Additive.ofMul
    { val := exponentialFunctionSection f
      inv := exponentialFunctionSection (-f)
      val_inv := by
        apply ContMDiffMap.ext
        intro x
        change Complex.exp (f x) * Complex.exp (-f x) = 1
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      inv_val := by
        apply ContMDiffMap.ext
        intro x
        change Complex.exp (-f x) * Complex.exp (f x) = 1
        rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero] }

@[simp]
theorem exponentialSection_val (f : HolomorphicFunctionSheaf.Section I M U) :
    unitSectionVal (exponentialSection f) = exponentialFunctionSection f := rfl

@[simp]
theorem exponentialSection_eval (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    unitSectionEval (exponentialSection f) x = Complex.exp (f x) := rfl

@[simp]
theorem exponentialSection_inverse_eval
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    unitSectionEval (-exponentialSection f) x = Complex.exp (-f x) := rfl

@[simp]
theorem exponentialSection_zero :
    exponentialSection (0 : HolomorphicFunctionSheaf.Section I M U) = 0 := by
  apply unitSection_ext
  intro x
  exact Complex.exp_zero

theorem exponentialSection_add (f g : HolomorphicFunctionSheaf.Section I M U) :
    exponentialSection (f + g) = exponentialSection f + exponentialSection g := by
  apply unitSection_ext
  intro x
  exact Complex.exp_add (f x) (g x)

@[simp]
theorem exponentialSection_neg (f : HolomorphicFunctionSheaf.Section I M U) :
    exponentialSection (-f) = -exponentialSection f := by
  apply unitSection_ext
  intro x
  rfl

/-- Exponentiation is compatible with the actual restriction morphisms. -/
theorem exponentialSection_restrict {V : Opens M} (h : U ≤ V)
    (f : HolomorphicFunctionSheaf.Section I M V) :
    (unitsSheaf I M).presheaf.map (homOfLE h).op (exponentialSection f) =
      exponentialSection ((HolomorphicFunctionSheaf.sheaf I M).presheaf.map
        (homOfLE h).op f) := by
  apply unitSection_ext
  intro x
  rfl

/-- The actual additive homomorphism on each open set. -/
def exponentialAddHom :
    HolomorphicFunctionSheaf.Section I M U →+ UnitSection I M U where
  toFun := exponentialSection
  map_zero' := exponentialSection_zero
  map_add' := exponentialSection_add

@[simp]
theorem exponentialAddHom_apply (f : HolomorphicFunctionSheaf.Section I M U) :
    exponentialAddHom f = exponentialSection f := rfl

variable (I M)

/-- The ordinary exponential is an actual morphism of abelian sheaves,
with zero in the target denoting the multiplicative unit section. -/
def exponential : HolomorphicFunctionSheaf.additiveSheaf I M ⟶ unitsSheaf I M where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom
        (exponentialAddHom (I := I) (M := M) (U := U.unop))
      naturality := fun U V h => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro f
        apply unitSection_ext
        intro x
        rfl }

@[simp]
theorem exponential_app (U : (Opens (TopCat.of M))ᵒᵖ)
    (f : (HolomorphicFunctionSheaf.additiveSheaf I M).presheaf.obj U) :
    (exponential I M).hom.app U f = exponentialSection f := rfl

/-- Evaluation of the actual sheaf morphism is ordinary scalar exponentiation. -/
@[simp]
theorem exponential_app_eval (U : (Opens (TopCat.of M))ᵒᵖ)
    (f : HolomorphicFunctionSheaf.Section I M U.unop) (x : U.unop) :
    unitSectionEval ((exponential I M).hom.app U f) x = Complex.exp (f x) := rfl

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
