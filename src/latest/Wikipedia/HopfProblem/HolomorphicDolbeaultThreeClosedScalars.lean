import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedSheaf
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsMultipliers

/-!
# Original complex scalar maps on closed native forms

Constant complex scalars preserve the actual native coefficient PDE.
Their sheaf endomorphisms are literal scalar multiplication of the
original real tangent covectors and commute with the actual inclusion
into all native antiholomorphic forms.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual complex scalar multiplication on closed native form sections,
as a genuine morphism of their additive sheaf. -/
def scalarSheafEnd (c : ℂ) : sheaf E M ⟶ sheaf E M where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom
        ({ toFun := fun s : ClosedFormSection E M U.unop => c • s
           map_zero' := smul_zero c
           map_add' := fun s t => smul_add c s t } :
          ClosedFormSection E M U.unop →+ ClosedFormSection E M U.unop)
      naturality := fun U V h => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        exact ClosedFormSection.ext E M fun _ => rfl }

@[simp] theorem scalarSheafEnd_app (c : ℂ) (U : Opens M) (s : ClosedFormSection E M U) :
    (scalarSheafEnd E M c).hom.app (op U) s = c • s := rfl

/-- The sheaf scalar action is the original complex endomorphism-ring action. -/
def scalarEnd : ℂ →+* End (sheaf E M) where
  toFun := scalarSheafEnd E M
  map_zero' := by
    apply sheafEnd_ext E M
    intro U s x
    exact zero_smul ℂ (s x)
  map_one' := by
    apply sheafEnd_ext E M
    intro U s x
    exact one_smul ℂ (s x)
  map_add' c d := by
    apply sheafEnd_ext E M
    intro U s x
    exact add_smul c d (s x)
  map_mul' c d := by
    apply sheafEnd_ext E M
    intro U s x
    exact mul_smul c d (s x)

@[simp] theorem scalarEnd_apply (c : ℂ) (U : Opens M)
    (s : ClosedFormSection E M U) (x : U) :
    ((scalarEnd E M c).asHom.hom.app (op U) s) x = c • s x := rfl

/-- The native sheaf-induced scalar map is exactly the original
pointwise complex module action on closed covector sections. -/
theorem scalarEnd_eq_smul (c : ℂ) (U : Opens M) (s : ClosedFormSection E M U) :
    (scalarEnd E M c).asHom.hom.app (op U) s = c • s := rfl

/-- The genuine inclusion of closed forms intertwines the original
scalar sheaf endomorphisms on both native form sheaves. -/
@[reassoc] theorem inclusion_scalar (c : ℂ) :
    (scalarEnd E M c).asHom ≫ inclusion E M =
      inclusion E M ≫ (Forms.scalarEnd E M c).asHom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact Forms.FormSection.ext E M fun _ => rfl

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms
