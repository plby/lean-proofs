import Wikipedia.HopfProblem.SingularCohomologyFreeComplexSingular
import Wikipedia.HopfProblem.SingularCohomologyFreeComplexHomotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Homotopy invariance of actual integral singular cohomology

The native singular-chain homotopy dualizes to a homotopy of the actual
singular pullbacks.  Thus homotopic continuous maps act identically on
integral singular cohomology in every degree.  Genuine topological homotopy
equivalences induce contravariant cochain homotopy equivalences, and
homeomorphisms induce strict cochain isomorphisms.

No projectivity, freeness, or universal-coefficient hypothesis is used.
-/

noncomputable section

open CategoryTheory
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SingularCohomologyFree

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual singular cochain homotopy obtained by dualizing the native
singular-chain homotopy of a continuous homotopy. -/
def singularCochainHomotopy {f g : C(X, Y)} (H : f.Homotopy g) :
    _root_.Homotopy (singularPullback f) (singularPullback g) :=
  dualHomotopy (PeriodTorusHigherHomology.singularChainHomotopy H)

/-- Homotopic maps have equal actual cohomology pullbacks in every degree. -/
theorem homotopy_singularCohomologyPullback {f g : C(X, Y)}
    (H : f.Homotopy g) (n : ℕ) :
    singularCohomologyPullback f n = singularCohomologyPullback g n :=
  congrArg ModuleCat.Hom.hom ((singularCochainHomotopy H).homologyMap_eq n)

theorem homotopic_singularCohomologyPullback {f g : C(X, Y)}
    (h : f.Homotopic g) (n : ℕ) :
    singularCohomologyPullback f n = singularCohomologyPullback g n := by
  obtain ⟨H⟩ := h
  exact homotopy_singularCohomologyPullback H n

/-- An actual topological homotopy equivalence induces a cochain homotopy
equivalence in the opposite direction, with the literal singular pullbacks. -/
def homotopyEquivCochainHomotopyEquiv (e : X ≃ₕ Y) :
    _root_.HomotopyEquiv (singularCochainComplex Y) (singularCochainComplex X) where
  hom := singularPullback e.toFun
  inv := singularPullback e.invFun
  homotopyHomInvId := by
    simpa only [singularPullback_comp, singularPullback_id] using
      singularCochainHomotopy (Classical.choice e.right_inv)
  homotopyInvHomId := by
    simpa only [singularPullback_comp, singularPullback_id] using
      singularCochainHomotopy (Classical.choice e.left_inv)

@[simp] theorem homotopyEquivCochainHomotopyEquiv_hom (e : X ≃ₕ Y) :
    (homotopyEquivCochainHomotopyEquiv e).hom = singularPullback e.toFun := rfl

@[simp] theorem homotopyEquivCochainHomotopyEquiv_inv (e : X ≃ₕ Y) :
    (homotopyEquivCochainHomotopyEquiv e).inv = singularPullback e.symm.toFun := rfl

/-- The resulting contravariant equivalence on actual integral cohomology. -/
def homotopyEquivCohomologyEquiv (e : X ≃ₕ Y) (n : ℕ) :
    SingularCohomology Y n ≃ₗ[ℤ] SingularCohomology X n :=
  ((homotopyEquivCochainHomotopyEquiv e).toHomologyIso n).toLinearEquiv

@[simp] theorem homotopyEquivCohomologyEquiv_toLinearMap (e : X ≃ₕ Y) (n : ℕ) :
    (homotopyEquivCohomologyEquiv e n).toLinearMap =
      singularCohomologyPullback e.toFun n := rfl

@[simp] theorem homotopyEquivCohomologyEquiv_apply (e : X ≃ₕ Y) (n : ℕ)
    (a : SingularCohomology Y n) :
    homotopyEquivCohomologyEquiv e n a = singularCohomologyPullback e.toFun n a := rfl

@[simp] theorem homotopyEquivCohomologyEquiv_symm_apply (e : X ≃ₕ Y) (n : ℕ)
    (a : SingularCohomology X n) :
    (homotopyEquivCohomologyEquiv e n).symm a =
      singularCohomologyPullback e.symm.toFun n a := rfl

/-- A homeomorphism induces a strict isomorphism of the actual singular
cochain complexes, contravariantly. -/
def homeomorphCochainIso (e : X ≃ₜ Y) :
    singularCochainComplex Y ≅ singularCochainComplex X where
  hom := singularPullback (e : C(X, Y))
  inv := singularPullback (e.symm : C(Y, X))
  hom_inv_id := by
    rw [← singularPullback_comp, Homeomorph.toContinuousMap_comp_symm,
      singularPullback_id]
  inv_hom_id := by
    rw [← singularPullback_comp, Homeomorph.symm_comp_toContinuousMap,
      singularPullback_id]

@[simp] theorem homeomorphCochainIso_hom (e : X ≃ₜ Y) :
    (homeomorphCochainIso e).hom = singularPullback (e : C(X, Y)) := rfl

@[simp] theorem homeomorphCochainIso_inv (e : X ≃ₜ Y) :
    (homeomorphCochainIso e).inv = singularPullback (e.symm : C(Y, X)) := rfl

/-- A homeomorphism gives an integral linear equivalence on actual singular
cohomology, with forward map equal to its pullback. -/
def homeomorphCohomologyEquiv (e : X ≃ₜ Y) (n : ℕ) :
    SingularCohomology Y n ≃ₗ[ℤ] SingularCohomology X n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n).mapIso
    (homeomorphCochainIso e)).toLinearEquiv

@[simp] theorem homeomorphCohomologyEquiv_toLinearMap (e : X ≃ₜ Y) (n : ℕ) :
    (homeomorphCohomologyEquiv e n).toLinearMap =
      singularCohomologyPullback (e : C(X, Y)) n := rfl

@[simp] theorem homeomorphCohomologyEquiv_apply (e : X ≃ₜ Y) (n : ℕ)
    (a : SingularCohomology Y n) :
    homeomorphCohomologyEquiv e n a =
      singularCohomologyPullback (e : C(X, Y)) n a := rfl

@[simp] theorem homeomorphCohomologyEquiv_symm_apply (e : X ≃ₜ Y) (n : ℕ)
    (a : SingularCohomology X n) :
    (homeomorphCohomologyEquiv e n).symm a =
      singularCohomologyPullback (e.symm : C(Y, X)) n a := rfl

end Wikipedia.HopfProblem.SingularCohomologyFree
