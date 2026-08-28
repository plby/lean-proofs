import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainHomotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Homotopy invariance of actual arbitrary-coefficient singular cochains

The original continuous homotopy yields the native integer singular chain
homotopy, which dualizes with arbitrary abelian coefficients.  The displayed
equivalences retain the original continuous-map pullbacks.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable (A : AddCommGrpCat.{0})
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Dualize the native singular-chain homotopy of the actual continuous homotopy. -/
def singularCochainHomotopy {f g : C(X, Y)} (H : f.Homotopy g) :
    _root_.Homotopy (singularPullback A f) (singularPullback A g) :=
  dualHomotopy A (PeriodTorusHigherHomology.singularChainHomotopy H)

/-- Homotopic continuous maps act equally on the actual cochain homology. -/
theorem homotopy_homologyMap_eq {f g : C(X, Y)} (H : f.Homotopy g) (n : ℕ) :
    HomologicalComplex.homologyMap (singularPullback A f) n =
      HomologicalComplex.homologyMap (singularPullback A g) n :=
  (singularCochainHomotopy A H).homologyMap_eq n

/-- The actual contravariant cochain homotopy equivalence of a topological one. -/
def homotopyEquivCochainHomotopyEquiv (e : X ≃ₕ Y) :
    _root_.HomotopyEquiv (singularCochainComplex Y A) (singularCochainComplex X A) where
  hom := singularPullback A e.toFun
  inv := singularPullback A e.invFun
  homotopyHomInvId := by
    simpa only [singularPullback_comp, singularPullback_id] using
      singularCochainHomotopy A (Classical.choice e.right_inv)
  homotopyInvHomId := by
    simpa only [singularPullback_comp, singularPullback_id] using
      singularCochainHomotopy A (Classical.choice e.left_inv)

@[simp]
theorem homotopyEquivCochainHomotopyEquiv_hom (e : X ≃ₕ Y) :
    (homotopyEquivCochainHomotopyEquiv A e).hom = singularPullback A e.toFun := rfl

@[simp]
theorem homotopyEquivCochainHomotopyEquiv_inv (e : X ≃ₕ Y) :
    (homotopyEquivCochainHomotopyEquiv A e).inv = singularPullback A e.symm.toFun := rfl

/-- A topological homotopy equivalence induces an actual cohomology isomorphism. -/
def homotopyEquivCohomologyIso (e : X ≃ₕ Y) (n : ℕ) :
    (singularCochainComplex Y A).homology n ≅ (singularCochainComplex X A).homology n :=
  (homotopyEquivCochainHomotopyEquiv A e).toHomologyIso n

@[simp]
theorem homotopyEquivCohomologyIso_hom (e : X ≃ₕ Y) (n : ℕ) :
    (homotopyEquivCohomologyIso A e n).hom =
      HomologicalComplex.homologyMap (singularPullback A e.toFun) n := rfl

/-- A genuine homeomorphism gives a strict isomorphism of native cochain complexes. -/
def homeomorphCochainIso (e : X ≃ₜ Y) :
    singularCochainComplex Y A ≅ singularCochainComplex X A where
  hom := singularPullback A (e : C(X, Y))
  inv := singularPullback A (e.symm : C(Y, X))
  hom_inv_id := by
    rw [← singularPullback_comp, Homeomorph.toContinuousMap_comp_symm,
      singularPullback_id]
  inv_hom_id := by
    rw [← singularPullback_comp, Homeomorph.symm_comp_toContinuousMap,
      singularPullback_id]

@[simp]
theorem homeomorphCochainIso_hom (e : X ≃ₜ Y) :
    (homeomorphCochainIso A e).hom = singularPullback A (e : C(X, Y)) := rfl

@[simp]
theorem homeomorphCochainIso_inv (e : X ≃ₜ Y) :
    (homeomorphCochainIso A e).inv = singularPullback A (e.symm : C(Y, X)) := rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
