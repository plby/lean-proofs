import Mathlib.Algebra.Category.Grp.Limits

/-!
# Consequences of an isomorphism on the actual kernel

If the restriction of an original additive map to the original kernel
is an isomorphism, that map is surjective and is injective on that
kernel. The proof uses the canonical comparison with the literal
additive subgroup kernel, retaining its original inclusion.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge.Exact

universe u

variable {A B D : AddCommGrpCat.{u}} (f : A ⟶ B) (g : A ⟶ D)
  (e : kernel f ≅ D) (he : e.hom = kernel.ι f ≫ g)

include e he

/-- Surjectivity of the actual restriction implies surjectivity of the full map. -/
theorem surjective_of_kernel_iso : Function.Surjective g := by
  intro y
  obtain ⟨x, hx⟩ := e.addCommGroupIsoToAddEquiv.surjective y
  exact ⟨kernel.ι f x, (ConcreteCategory.congr_hom he x).symm.trans hx⟩

/-- The original map is injective on the literal zero fibre of the original map `f`. -/
theorem injective_on_kernel_of_iso : Set.InjOn g {x : A | f x = 0} := by
  let lift (x : A) (hx : f x = 0) : (kernel f : AddCommGrpCat.{u}) :=
    (AddCommGrpCat.kernelIsoKer f).inv ⟨x, hx⟩
  have hlift (x : A) (hx : f x = 0) : kernel.ι f (lift x hx) = x :=
    ConcreteCategory.congr_hom (AddCommGrpCat.kernelIsoKer_inv_comp_ι f) ⟨x, hx⟩
  intro x hx y hy hxy
  have heq : lift x hx = lift y hy := by
    apply e.addCommGroupIsoToAddEquiv.injective
    change e.hom (lift x hx) = e.hom (lift y hy)
    calc
      e.hom (lift x hx) = g (kernel.ι f (lift x hx)) :=
        ConcreteCategory.congr_hom he (lift x hx)
      _ = g x := congrArg g (hlift x hx)
      _ = g y := hxy
      _ = g (kernel.ι f (lift y hy)) := congrArg g (hlift y hy).symm
      _ = e.hom (lift y hy) := (ConcreteCategory.congr_hom he (lift y hy)).symm
  exact (hlift x hx).symm.trans ((congrArg (kernel.ι f) heq).trans (hlift y hy))

/-- In particular, a class in the literal kernel maps to zero exactly
when the original class itself is zero. -/
theorem zero_iff_of_kernel_iso (x : A) (hx : f x = 0) : g x = 0 ↔ x = 0 := by
  constructor
  · intro hg
    exact injective_on_kernel_of_iso f g e he hx f.hom.map_zero
      (hg.trans g.hom.map_zero.symm)
  · rintro rfl
    exact g.hom.map_zero

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologySingularEdge.Exact
