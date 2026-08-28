import Wikipedia.HopfProblem.SingularMayerVietorisSequence
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Native singular chains and homology with finite cyclic coefficients

The coefficient object is `ModuleCat.of ℤ (ZMod p)` in Mathlib's actual
singular chain and homology functors.  Thus the groups below are singular
homology with coefficients `ℤ/p`, viewed as integral modules.  They are
not defined from the integral homology ranks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SphereHomologyCoefficients

open SingularMayerVietoris

/-- Mathlib's actual singular chain complex for an arbitrary integral coefficient module. -/
abbrev coefficientComplex (A : ModuleCat.{0} ℤ) (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj A).obj (TopCat.of X)

/-- The actual chain-complex map induced by a homomorphism of coefficient modules. -/
abbrev coefficientComplexMap {A B : ModuleCat.{0} ℤ} (f : A ⟶ B)
    (X : Type) [TopologicalSpace X] : coefficientComplex A X ⟶ coefficientComplex B X :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).map f).app (TopCat.of X)

/-- The native singular complex with coefficient object `ℤ/p`. -/
abbrev modComplex (p : ℕ) (X : Type) [TopologicalSpace X] :
    ChainComplex (ModuleCat ℤ) ℕ :=
  coefficientComplex (ModuleCat.of ℤ (ZMod p)) X

/-- Actual singular homology with finite cyclic coefficients, as an integral module. -/
abbrev ModHomology (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) : ModuleCat ℤ :=
  (modComplex p X).homology n

/-- This is the literal object returned by Mathlib's singular homology functor. -/
theorem ModHomology_eq_native (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    ModHomology p X n =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
        (ModuleCat.of ℤ (ZMod p))).obj (TopCat.of X)) := rfl

/-- The original integral singular complex agrees with the same coefficient functor at `ℤ`. -/
theorem coefficientComplex_int (X : Type) [TopologicalSpace X] :
    coefficientComplex (ModuleCat.of ℤ ℤ) X = FirstHurewicz.singularComplex X := rfl

/-- The actual coefficient reduction homomorphism. -/
def reductionCoefficient (p : ℕ) : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ (ZMod p) :=
  ModuleCat.ofHom (Int.castAddHom (ZMod p)).toIntLinearMap

@[simp] theorem reductionCoefficient_apply (p : ℕ) (z : ℤ) :
    reductionCoefficient p z = (z : ZMod p) := rfl

/-- Coefficient reduction on the actual integral singular chain complex. -/
abbrev reductionChainMap (p : ℕ) (X : Type) [TopologicalSpace X] :
    FirstHurewicz.singularComplex X ⟶ modComplex p X :=
  coefficientComplexMap (reductionCoefficient p) X

/-- Multiplication by the integer `p` on the original singular chain complex. -/
def multiplicationChainMap (p : ℕ) (X : Type) [TopologicalSpace X] :
    FirstHurewicz.singularComplex X ⟶ FirstHurewicz.singularComplex X :=
  (p : ℤ) • 𝟙 (FirstHurewicz.singularComplex X)

/-- The induced, genuine coefficient-change map on singular homology. -/
abbrev reductionHomologyMap (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularHomology X n →ₗ[ℤ] ModHomology p X n :=
  homologyLinearMap (reductionChainMap p X) n

/-- The first map of the coefficient sequence induces actual multiplication on homology. -/
theorem multiplicationChainMap_homology (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    homologyLinearMap (multiplicationChainMap p X) n =
      (p : ℤ) • (LinearMap.id : SingularHomology X n →ₗ[ℤ] SingularHomology X n) := by
  change ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
    ((p : ℤ) • 𝟙 (FirstHurewicz.singularComplex X))).hom = _
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]
  rfl

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The original continuous map induces the native coefficient homology map. -/
abbrev modHomologyMap (p : ℕ) (f : C(X, Y)) (n : ℕ) :
    ModHomology p X n →ₗ[ℤ] ModHomology p Y n :=
  ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ (ZMod p))).map (TopCat.ofHom f))).hom

@[simp] theorem modHomologyMap_id (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    modHomologyMap p (ContinuousMap.id X) n = LinearMap.id := by
  change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ (ZMod p))).map (𝟙 (TopCat.of X))).hom = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem modHomologyMap_comp (p : ℕ) (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    modHomologyMap p (g.comp f) n = (modHomologyMap p g n).comp (modHomologyMap p f n) := by
  change (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ (ZMod p))).map (TopCat.ofHom f ≫ TopCat.ofHom g)).hom = _
  rw [Functor.map_comp]
  rfl

/-- A proved homeomorphism induces the actual equivalence with these coefficient objects. -/
def modHomologyHomeomorphEquiv (p : ℕ) (e : X ≃ₜ Y) (n : ℕ) :
    ModHomology p X n ≃ₗ[ℤ] ModHomology p Y n :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ (ZMod p))).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e)).toLinearEquiv

@[simp] theorem modHomologyHomeomorphEquiv_apply (p : ℕ) (e : X ≃ₜ Y) (n : ℕ)
    (a : ModHomology p X n) :
    modHomologyHomeomorphEquiv p e n a = modHomologyMap p (e : C(X, Y)) n a := rfl

@[simp] theorem modHomologyHomeomorphEquiv_symm_apply (p : ℕ) (e : X ≃ₜ Y) (n : ℕ)
    (a : ModHomology p Y n) :
    (modHomologyHomeomorphEquiv p e n).symm a =
      modHomologyMap p (e.symm : C(Y, X)) n a := rfl

end Wikipedia.HopfProblem.SphereHomologyCoefficients
