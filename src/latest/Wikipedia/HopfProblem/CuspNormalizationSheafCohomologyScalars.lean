import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroScalars
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ExtGlobal

/-!
# Actual scalar actions on genuine sheaf cohomology

An action on a sheaf by actual scalar endomorphisms induces the scalar
action on its genuine `Ext` cohomology in every degree. The construction
uses the actual additive cohomology functor, so it does not assign an
unrelated vector-space structure through a later dimension calculation.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomology

universe u v u' v'

section Endomorphisms

variable {A : Type u} [Category.{v} A] [Preadditive A]
  {B : Type u'} [Category.{v'} B] [Preadditive B]

/-- An additive functor induces the actual ring homomorphism on
endomorphisms, with multiplication given by composition. -/
def mapEndRingHom (F : A ⥤ B) [F.Additive] (X : A) :
    End X →+* End (F.obj X) where
  toFun := F.map
  map_one' := F.map_id X
  map_mul' a b := F.map_comp b a
  map_zero' := F.map_zero X X
  map_add' _ _ := F.map_add

end Endomorphisms

section Modules

variable {R : Type} [Semiring R] (A : AddCommGrpCat.{0}) (ρ : R →+* End A)

/-- Actual scalar endomorphisms of an abelian group give its scalar
module structure by evaluation of those endomorphisms. -/
@[instance_reducible] def moduleOfScalarEnd : Module R A where
  smul r a := (ρ r).asHom a
  one_smul a := by
    change (ρ 1).asHom a = a
    rw [map_one]
    rfl
  mul_smul r s a := by
    change (ρ (r * s)).asHom a = (ρ r).asHom ((ρ s).asHom a)
    rw [map_mul]
    rfl
  smul_zero r := (ρ r).asHom.hom.map_zero
  smul_add r a b := (ρ r).asHom.hom.map_add a b
  add_smul r s a := by
    change (ρ (r + s)).asHom a = (ρ r).asHom a + (ρ s).asHom a
    rw [map_add]
    rfl
  zero_smul a := by
    change (ρ 0).asHom a = 0
    rw [map_zero]
    rfl

end Modules

section Cohomology

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  (ρ : ℂ →+* End F) (n : ℕ)

/-- The group structure is the existing one on genuine `Ext` groups. -/
instance cohomologyAddCommGroup : AddCommGroup (CategoryTheory.Sheaf.H.{0} F n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The actual scalar action on the genuine degree-`n` cohomology group. -/
@[instance_reducible] def cohomologyModule : Module ℂ (CategoryTheory.Sheaf.H.{0} F n) :=
  moduleOfScalarEnd ((CategoryTheory.Sheaf.functorH _ n).obj F)
    ((mapEndRingHom (CategoryTheory.Sheaf.functorH _ n) F).comp ρ)

/-- Scalar multiplication is precisely the map induced by the actual
scalar endomorphism of the original sheaf. -/
theorem cohomologyModule_smul (c : ℂ) (a : CategoryTheory.Sheaf.H.{0} F n) :
    letI := cohomologyModule F ρ n
    c • a = CategoryTheory.Sheaf.H.map (ρ c) n a := rfl

end Cohomology

section HolomorphicFunctions

open scoped ContDiff Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The literal scalar endomorphisms of the actual holomorphic-function
sheaf form the natural complex scalar action. -/
def holomorphicScalarEnd : ℂ →+* End (HolomorphicFunctionSheaf.additiveSheaf I M) where
  toFun := HolomorphicFunctionSheaf.scalarSheafEnd I M
  map_one' := HolomorphicFunctionSheaf.scalarSheafEnd_one I M
  map_mul' := HolomorphicFunctionSheaf.scalarSheafEnd_mul I M
  map_zero' := HolomorphicFunctionSheaf.scalarSheafEnd_zero I M
  map_add' := HolomorphicFunctionSheaf.scalarSheafEnd_add I M

/-- Every genuine holomorphic sheaf-cohomology group has the scalar
action induced by multiplication of actual holomorphic functions. -/
instance holomorphicCohomologyAddCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The induced module structure on the genuine cohomology of the
actual holomorphic-function sheaf. -/
@[instance_reducible] def holomorphicCohomologyModule (n : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) n) :=
  cohomologyModule (HolomorphicFunctionSheaf.additiveSheaf I M) (holomorphicScalarEnd I M) n

end HolomorphicFunctions

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomology
