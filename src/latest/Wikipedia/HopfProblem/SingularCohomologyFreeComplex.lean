import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Opposite
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The actual integral cochain dual of a chain complex

The functor in this file applies `Hom(-, ℤ)` to the chain modules and reverses
the differentials.  Its values are cochain complexes, not duals of homology
groups.  Every displayed differential and pullback is literal precomposition.
-/

noncomputable section

open CategoryTheory Opposite

namespace Wikipedia.HopfProblem.SingularCohomologyFree

universe u

/-- The additive contravariant integral module-dual functor. -/
def integralDualFunctor : (ModuleCat.{u} ℤ)ᵒᵖ ⥤ ModuleCat.{u} ℤ where
  obj M := ModuleCat.of ℤ (Module.Dual ℤ M.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id M := by
    ext φ x
    rfl
  map_comp f g := by
    ext φ x
    rfl

instance integralDualFunctor_additive : integralDualFunctor.{u}.Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    change (f + g).unop.hom.dualMap = f.unop.hom.dualMap + g.unop.hom.dualMap
    ext φ x
    exact φ.map_add (f.unop.hom x) (g.unop.hom x)

/-- Contravariant integral duality, with values in actual cochain complexes. -/
def dualFunctor : (ChainComplex (ModuleCat.{u} ℤ) ℕ)ᵒᵖ ⥤
    CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  HomologicalComplex.opFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) ⋙
    integralDualFunctor.mapHomologicalComplex (ComplexShape.up ℕ)

instance dualFunctor_additive : dualFunctor.{u}.Additive where
  map_add := by
    intro K L f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    change ((f + g).unop.f n).hom.dualMap =
      (f.unop.f n).hom.dualMap + (g.unop.f n).hom.dualMap
    ext φ x
    exact φ.map_add ((f.unop.f n).hom x) ((g.unop.f n).hom x)

/-- The cochain complex whose degree-`n` module is `Hom(Kₙ, ℤ)`. -/
abbrev dualComplex (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    CochainComplex (ModuleCat.{u} ℤ) ℕ where
  X n := ModuleCat.of ℤ (K.X n →ₗ[ℤ] ℤ)
  d i j := ModuleCat.ofHom (K.d j i).hom.dualMap
  shape i j hij := (dualFunctor.obj (op K)).shape i j hij
  d_comp_d' i j k _ _ := (dualFunctor.obj (op K)).d_comp_d i j k

@[simp] theorem dualComplex_X (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) :
    (dualComplex K).X n = ModuleCat.of ℤ (K.X n →ₗ[ℤ] ℤ) := rfl

@[simp] theorem dualComplex_d_apply (K : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    (i j : ℕ) (φ : K.X i →ₗ[ℤ] ℤ) :
    ((dualComplex K).d i j).hom φ = φ.comp (K.d j i).hom := rfl

theorem dualComplex_d_apply_apply (K : ChainComplex (ModuleCat.{u} ℤ) ℕ)
    (i j : ℕ) (φ : K.X i →ₗ[ℤ] ℤ) (x : K.X j) :
    (((dualComplex K).d i j).hom φ : K.X j →ₗ[ℤ] ℤ) x =
      φ ((K.d j i).hom x) := rfl

/-- A chain map acts on cochains by pullback. -/
def dualMap {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ L) :
    dualComplex L ⟶ dualComplex K :=
  dualFunctor.map f.op

@[simp] theorem dualMap_f_apply {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ L) (n : ℕ) (φ : L.X n →ₗ[ℤ] ℤ) :
    ((dualMap f).f n).hom φ = φ.comp (f.f n).hom := rfl

theorem dualMap_f_apply_apply {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ L) (n : ℕ) (φ : L.X n →ₗ[ℤ] ℤ) (x : K.X n) :
    (((dualMap f).f n).hom φ : K.X n →ₗ[ℤ] ℤ) x =
      φ ((f.f n).hom x) := rfl

@[simp] theorem dualMap_id (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    dualMap (𝟙 K) = 𝟙 (dualComplex K) := by
  exact dualFunctor.map_id (op K)

@[simp] theorem dualMap_comp {K L M : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f : K ⟶ L) (g : L ⟶ M) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f := by
  exact dualFunctor.map_comp g.op f.op

@[simp] theorem dualMap_zero (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ) :
    dualMap (0 : K ⟶ L) = 0 := by
  exact dualFunctor.map_zero (op L) (op K)

@[simp] theorem dualMap_add {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f g : K ⟶ L) : dualMap (f + g) = dualMap f + dualMap g := by
  exact dualFunctor.map_add

end Wikipedia.HopfProblem.SingularCohomologyFree
