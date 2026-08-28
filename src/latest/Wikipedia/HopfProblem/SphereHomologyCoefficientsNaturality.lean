import Wikipedia.HopfProblem.SphereHomologyCoefficientsBasic

/-!
# Naturality of the genuine singular coefficient-change maps

These identities are the naturality square in Mathlib's native singular
homology functor.  They identify reduction after an actual continuous map
with that same continuous map on finite-coefficient homology.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SphereHomologyCoefficients

open SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Coefficient reduction on homology is the literal component of the native coefficient functor. -/
theorem reductionHomologyMap_eq_native (p : ℕ) (X : Type) [TopologicalSpace X] (n : ℕ) :
    reductionHomologyMap p X n =
      (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).map
        (reductionCoefficient p)).app (TopCat.of X)).hom := rfl

/-- The genuine continuous-map coefficient-change square commutes in every degree. -/
theorem modHomologyMap_comp_reduction (p : ℕ) (f : C(X, Y)) (n : ℕ) :
    (modHomologyMap p f n).comp (reductionHomologyMap p X n) =
      (reductionHomologyMap p Y n).comp (singularHomologyMap f n) := by
  have h := congrArg ModuleCat.Hom.hom
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).map
      (reductionCoefficient p)).naturality (TopCat.ofHom f))
  exact h.symm

theorem modHomologyMap_reduction (p : ℕ) (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology X n) :
    modHomologyMap p f n (reductionHomologyMap p X n a) =
      reductionHomologyMap p Y n (singularHomologyMap f n a) :=
  LinearMap.congr_fun (modHomologyMap_comp_reduction p f n) a

/-- The actual homeomorphism-induced coefficient equivalence preserves reduced integral classes. -/
theorem modHomologyHomeomorphEquiv_reduction (p : ℕ) (e : X ≃ₜ Y) (n : ℕ)
    (a : SingularHomology X n) :
    modHomologyHomeomorphEquiv p e n (reductionHomologyMap p X n a) =
      reductionHomologyMap p Y n (singularHomologyMap (e : C(X, Y)) n a) :=
  modHomologyMap_reduction p (e : C(X, Y)) n a

end Wikipedia.HopfProblem.SphereHomologyCoefficients
