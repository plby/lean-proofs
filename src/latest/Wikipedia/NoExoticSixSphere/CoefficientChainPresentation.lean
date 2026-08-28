import Wikipedia.NoExoticSixSphere.RelativeCoefficientComplex
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Finite presentations of the original coefficient chains

The actual coproduct inclusions yield a surjective map from finitely
supported simplex coefficients onto the native singular chain group.
This applies to arbitrary integral coefficient modules, not just free
ones, and supplies finite presentations needed for compact carriers.
-/

noncomputable section

open CategoryTheory Limits Simplicial
open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients

namespace NoExoticSixSphere.CoefficientChains

variable (A : ModuleCat.{0} ℤ) (X : Type) [TopologicalSpace X] (n : ℕ)

/-- The original singular chains with this coefficient module. -/
abbrev Chains := (coefficientComplex A X).X n

local instance finsuppModule : Module ℤ (SingularSimplex X n →₀ A) :=
  Finsupp.module _ _

/-- The native coproduct summand for an actual continuous singular simplex. -/
def simplex (σ : SingularSimplex X n) : A →ₗ[ℤ] Chains A X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (R := A) (simplexIndex X n σ)).hom

/-- The actual coproduct universal map, specified on each coefficient summand. -/
def lift {B : Type} [AddCommGroup B] [Module ℤ B]
    (f : SingularSimplex X n → A →ₗ[ℤ] B) : Chains A X n →ₗ[ℤ] B :=
  (Sigma.desc (fun s : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌ =>
    (ModuleCat.ofHom (f ((TopCat.of X).toSSetObjEquiv (.op ⦋n⦌) s)) :
      A ⟶ ModuleCat.of ℤ B)) :
    Chains A X n ⟶ ModuleCat.of ℤ B).hom

theorem lift_simplex {B : Type} [AddCommGroup B] [Module ℤ B]
    (f : SingularSimplex X n → A →ₗ[ℤ] B) (σ : SingularSimplex X n) (a : A) :
    lift A X n f (simplex A X n σ a) = f σ a := by
  have h := Sigma.ι_desc
    (fun s : (TopCat.toSSet.obj (TopCat.of X)) _⦋n⦌ =>
      (ModuleCat.ofHom (f ((TopCat.of X).toSSetObjEquiv (.op ⦋n⦌) s)) :
        A ⟶ ModuleCat.of ℤ B))
    (simplexIndex X n σ)
  have he := congrArg (fun g : A ⟶ ModuleCat.of ℤ B => g.hom a) h
  simpa only [lift, simplex, simplexIndex, Equiv.apply_symm_apply,
    SSet.ιChainComplex, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom] using! he

/-- Maps out of native chains are determined by all simplex coefficient summands. -/
theorem map_ext {B : Type} [AddCommGroup B] [Module ℤ B]
    {f g : Chains A X n →ₗ[ℤ] B}
    (h : ∀ (σ : SingularSimplex X n) (a : A),
      f (simplex A X n σ a) = g (simplex A X n σ a)) : f = g := by
  have hcat : (ModuleCat.ofHom f : Chains A X n ⟶ ModuleCat.of ℤ B) =
      ModuleCat.ofHom g := by
    apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj (TopCat.of X)) (R := A)
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change f (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := A) s).hom a) =
      g (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := A) s).hom a)
    have hs := h ((TopCat.of X).toSSetObjEquiv (.op ⦋n⦌) s) a
    simpa only [simplex, simplexIndex, Equiv.symm_apply_apply,
      ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using! hs
  exact congrArg ModuleCat.Hom.hom hcat

/-- Finite sums of original simplex summands. -/
def fromFinsupp : (SingularSimplex X n →₀ A) →ₗ[ℤ] Chains A X n :=
  Finsupp.lsum ℕ (simplex A X n)

theorem fromFinsupp_single (σ : SingularSimplex X n) (a : A) :
    fromFinsupp A X n (Finsupp.single σ a) = simplex A X n σ a := by
  exact Finsupp.lsum_single ℕ (simplex A X n) σ a

/-- Finitely supported coordinates obtained from the native universal property. -/
def repr : Chains A X n →ₗ[ℤ] (SingularSimplex X n →₀ A) :=
  lift A X n (fun σ => Finsupp.lsingle σ)

theorem fromFinsupp_repr (c : Chains A X n) : fromFinsupp A X n (repr A X n c) = c := by
  have he : (fromFinsupp A X n).comp (repr A X n) = LinearMap.id := by
    apply map_ext A X n
    intro σ a
    change fromFinsupp A X n (lift A X n _ (simplex A X n σ a)) = _
    rw [lift_simplex]
    exact fromFinsupp_single A X n σ a
  exact LinearMap.congr_fun he c

/-- Every native coefficient chain has a finite simplex presentation. -/
theorem fromFinsupp_surjective : Function.Surjective (fromFinsupp A X n) :=
  fun c => ⟨repr A X n c, fromFinsupp_repr A X n c⟩

variable {X} {Y : Type} [TopologicalSpace Y]

/-- Mapping an original simplex summand composes the actual continuous simplex. -/
theorem spaceMap_simplex (f : C(X, Y)) (σ : SingularSimplex X n) (a : A) :
    ((RelativeCoefficients.spaceMap A f).f n).hom (simplex A X n σ a) =
      simplex A Y n (f.comp σ) a := by
  have h := SSet.ι_chainComplexMap_f _ _
    (TopCat.toSSet.map (TopCat.ofHom f)) A (simplexIndex X n σ)
  exact congrArg (fun g => g.hom a) h

end NoExoticSixSphere.CoefficientChains
