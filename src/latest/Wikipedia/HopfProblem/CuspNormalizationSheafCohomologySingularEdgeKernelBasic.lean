import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Restricting the actual scalar action to a categorical kernel

The existing additive categorical kernel of a linear map acquires the
ambient scalar action by its universal property.  Each scalar acts by
the unique lift of scalar multiplication composed with the original
kernel inclusion.  No cohomological comparison or dimension equivalence
is used to define this action, and the additive group is unchanged.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomology.SingularEdgeKernel

universe u v

variable {R : Type u} [Semiring R] {A B : AddCommGrpCat.{v}}
  [Module R A] [Module R B]

/-- Scalar multiplication on the actual ambient additive group. -/
def ambientScalarHom (c : R) : A ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun x => c • x
      map_zero' := smul_zero c
      map_add' := smul_add c }

variable (f : A ⟶ B) (hf : ∀ (c : R) (x : A), f (c • x) = c • f x)

/-- Scalars restrict to the actual categorical kernel by its universal property. -/
def kernelScalarHom (c : R) : kernel f ⟶ kernel f :=
  kernel.lift f (kernel.ι f ≫ ambientScalarHom c) (by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change f (c • kernel.ι f x) = 0
    rw [hf]
    have hx : f (kernel.ι f x) = 0 :=
      ConcreteCategory.congr_hom (kernel.condition f) x
    rw [hx, smul_zero])

/-- The restricted scalar map commutes with the original kernel inclusion. -/
@[reassoc]
theorem kernelScalarHom_comp_ι (c : R) :
    kernelScalarHom f hf c ≫ kernel.ι f =
      kernel.ι f ≫ ambientScalarHom c :=
  kernel.lift_ι _ _ _

/-- The restriction action before its module laws are bundled. -/
@[instance_reducible]
def kernelSMul : SMul R (kernel f : AddCommGrpCat.{v}) where
  smul c x := kernelScalarHom f hf c x

/-- The restriction action is exactly ambient scalar multiplication under inclusion. -/
theorem kernelSMul_ι (c : R) (x : (kernel f : AddCommGrpCat.{v})) :
    letI := kernelSMul f hf
    kernel.ι f (c • x) = c • kernel.ι f x :=
  ConcreteCategory.congr_hom (kernelScalarHom_comp_ι f hf c) x

/-- The original categorical kernel inherits only the restricted ambient module action. -/
@[instance_reducible]
def kernelModule : Module R (kernel f : AddCommGrpCat.{v}) := by
  letI := kernelSMul f hf
  exact Function.Injective.module R (kernel.ι f).hom
    ((AddCommGrpCat.mono_iff_injective (kernel.ι f)).mp inferInstance)
    (kernelSMul_ι f hf)

/-- The original kernel inclusion is scalar-linear for the restricted module. -/
theorem kernel_ι_smul (c : R) (x : (kernel f : AddCommGrpCat.{v})) :
    letI := kernelModule f hf
    kernel.ι f (c • x) = c • kernel.ι f x :=
  kernelSMul_ι f hf c x

/-- The existing inclusion, bundled as a linear map without changing its function. -/
def kernelιLinearMap :
    letI := kernelModule f hf
    (kernel f : AddCommGrpCat.{v}) →ₗ[R] A := by
  letI := kernelModule f hf
  exact
    { toFun := kernel.ι f
      map_add' := (kernel.ι f).hom.map_add
      map_smul' := kernel_ι_smul f hf }

/-- Bundling the inclusion as a linear map does not change the original additive map. -/
@[simp]
theorem kernelιLinearMap_toAddMonoidHom :
    letI := kernelModule f hf
    (kernelιLinearMap f hf).toAddMonoidHom = (kernel.ι f).hom := rfl

/-- In particular, the linear inclusion has the original value on every element. -/
@[simp]
theorem kernelιLinearMap_apply (x : (kernel f : AddCommGrpCat.{v})) :
    letI := kernelModule f hf
    kernelιLinearMap f hf x = kernel.ι f x := rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomology.SingularEdgeKernel
