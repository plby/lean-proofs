import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ExtGlobal
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ExtAlgebra

/-!
# Genuine first sheaf cohomology vanishes from global lifting

Choose an actual injective presentation of an abelian sheaf and its
cokernel short exact sequence. Lifting global sections gives lifting of
morphisms from the constant integer sheaf through the degree-zero
cohomology comparison. The actual Ext exact sequence then proves that
degree-one sheaf cohomology is zero.

All sheafification, enough-injectives and small-Ext instances are supplied
by the installed theory of abelian sheaves on the small open-set site.
The only additional hypothesis is the stated global-lifting property.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}

/-- Global lifting for every short exact sequence beginning in `F` forces
the genuine first sheaf cohomology group of `F` to be zero. -/
theorem subsingleton_h1_of_globalLifting (F : AbelianSheaf X) (hlift : GlobalLifting F) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F 1) := by
  let p : InjectivePresentation F := Classical.arbitrary _
  have hS := p.shortExact_shortComplex
  have hglobal := hlift p.f (Limits.cokernel.π p.f) (Limits.cokernel.condition p.f) hS
  have hhom := hom_surjective_of_global_surjective (Limits.cokernel.π p.f) hglobal
  exact subsingleton_ext_one_of_shortExact (constantIntegerSheaf X) hS hhom

/-- Every actual degree-one cohomology class is zero under global lifting. -/
theorem h1_eq_zero_of_globalLifting (F : AbelianSheaf X) (hlift : GlobalLifting F)
    (x : CategoryTheory.Sheaf.H.{0} F 1) : x = 0 := by
  let := subsingleton_h1_of_globalLifting F hlift
  exact Subsingleton.elim x 0

/-- An equivalent formulation using short complexes with named first object. -/
theorem subsingleton_h1_of_shortExact_global_surjective (F : AbelianSheaf X)
    (hlift : ∀ (S : ShortComplex (AbelianSheaf X)), S.X₁ = F → S.ShortExact →
      Function.Surjective (S.g.hom.app (op (⊤ : Opens X)))) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} F 1) := by
  apply subsingleton_h1_of_globalLifting F
  intro G Q ι π h hS
  exact hlift (ShortComplex.mk ι π h) rfl hS

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
