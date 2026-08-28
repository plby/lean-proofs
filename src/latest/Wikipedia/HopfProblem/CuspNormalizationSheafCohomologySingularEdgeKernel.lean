import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologySingularEdgeKernelBasic
import Mathlib.Algebra.Module.Equiv.Defs

/-!
# Linear maps out of the actual categorical kernel

An existing additive kernel isomorphism is linear if its map is the
original kernel inclusion followed by an actual linear ambient map.
This proves linearity for the restricted module structure without
transporting any scalar action along that isomorphism.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomology.SingularEdgeKernel

universe u v

variable {R : Type u} [Semiring R] {A B D : AddCommGrpCat.{v}}
  [Module R A] [Module R B] [Module R D]
  (f : A ⟶ B) (hf : ∀ (c : R) (x : A), f (c • x) = c • f x)

/-- Restrict an actual linear ambient map to the original categorical kernel. -/
def linearMapFromKernel (p : A →ₗ[R] D) :
    letI := kernelModule f hf
    (kernel f : AddCommGrpCat.{v}) →ₗ[R] D := by
  letI := kernelModule f hf
  exact p.comp (kernelιLinearMap f hf)

/-- The restriction has the original inclusion followed by the ambient map as its value. -/
@[simp]
theorem linearMapFromKernel_apply (p : A →ₗ[R] D)
    (x : (kernel f : AddCommGrpCat.{v})) :
    letI := kernelModule f hf
    linearMapFromKernel f hf p x = p (kernel.ι f x) := rfl

/-- An existing additive kernel isomorphism is linear when its original map
is the kernel inclusion followed by an independently defined linear map. -/
def linearEquivFromKernel (e : kernel f ≅ D) (p : A →ₗ[R] D)
    (square : e.hom = kernel.ι f ≫ AddCommGrpCat.ofHom p.toAddMonoidHom) :
    letI := kernelModule f hf
    (kernel f : AddCommGrpCat.{v}) ≃ₗ[R] D := by
  letI := kernelModule f hf
  exact
    { e.addCommGroupIsoToAddEquiv with
      map_smul' := fun c x => by
        change e.hom (c • x) = c • e.hom x
        have he (z : (kernel f : AddCommGrpCat.{v})) :
            e.hom z = p (kernel.ι f z) :=
          ConcreteCategory.congr_hom square z
        rw [he (c • x), he x, kernel_ι_smul f hf c x]
        exact p.map_smul c (kernel.ι f x) }

/-- The linear upgrade retains the original additive equivalence exactly. -/
@[simp]
theorem linearEquivFromKernel_toAddEquiv
    (e : kernel f ≅ D) (p : A →ₗ[R] D)
    (square : e.hom = kernel.ι f ≫ AddCommGrpCat.ofHom p.toAddMonoidHom) :
    letI := kernelModule f hf
    (linearEquivFromKernel f hf e p square).toAddEquiv =
      e.addCommGroupIsoToAddEquiv := rfl

/-- The linear upgrade has the original forward map on elements. -/
@[simp]
theorem linearEquivFromKernel_apply
    (e : kernel f ≅ D) (p : A →ₗ[R] D)
    (square : e.hom = kernel.ι f ≫ AddCommGrpCat.ofHom p.toAddMonoidHom)
    (x : (kernel f : AddCommGrpCat.{v})) :
    letI := kernelModule f hf
    linearEquivFromKernel f hf e p square x = e.hom x := rfl

/-- The inverse is also the inverse of the original additive isomorphism. -/
@[simp]
theorem linearEquivFromKernel_symm_apply
    (e : kernel f ≅ D) (p : A →ₗ[R] D)
    (square : e.hom = kernel.ι f ≫ AddCommGrpCat.ofHom p.toAddMonoidHom) (y : D) :
    letI := kernelModule f hf
    (linearEquivFromKernel f hf e p square).symm y = e.inv y := rfl

/-- As a linear map, the upgraded isomorphism is the actual ambient restriction. -/
theorem linearEquivFromKernel_toLinearMap
    (e : kernel f ≅ D) (p : A →ₗ[R] D)
    (square : e.hom = kernel.ι f ≫ AddCommGrpCat.ofHom p.toAddMonoidHom) :
    letI := kernelModule f hf
    (linearEquivFromKernel f hf e p square).toLinearMap = linearMapFromKernel f hf p := by
  let := kernelModule f hf
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom square x

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomology.SingularEdgeKernel
