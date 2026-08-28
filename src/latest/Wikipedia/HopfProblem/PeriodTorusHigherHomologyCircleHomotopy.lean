import Wikipedia.HopfProblem.SingularMayerVietorisSequence
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Homotopy.Equiv

/-!
# Actual singular homology under homotopy equivalences

Mathlib's singular-chain homotopy associated with a continuous-map homotopy
proves invariance of the actual integral singular homology map in every
degree. Consequently genuine homotopy equivalences and homeomorphisms
induce integral linear equivalences on the actual singular homology modules.
Their forward and inverse maps are exactly the induced singular homology maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris
open scoped ContinuousMap

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The actual homology functor sends the identity map to the identity in every degree. -/
@[simp] theorem singularHomologyMap_id (X : Type) [TopologicalSpace X] (n : ℕ) :
    singularHomologyMap (ContinuousMap.id X) n = LinearMap.id := by
  have h := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map_id (TopCat.of X)
  exact congrArg ModuleCat.Hom.hom h

/-- Functoriality of the actual singular homology maps in every degree. -/
theorem singularHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z)) (n : ℕ) :
    singularHomologyMap (g.comp f) n =
      (singularHomologyMap g n).comp (singularHomologyMap f n) := by
  have h := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) n).obj
    (ModuleCat.of ℤ ℤ)).map_comp (TopCat.ofHom f) (TopCat.ofHom g)
  exact congrArg ModuleCat.Hom.hom h

/-- An actual continuous homotopy gives a chain homotopy of the actual
integral singular chain maps, using Mathlib's simplicial prism construction. -/
def singularChainHomotopy {f g : C(X, Y)} (H : f.Homotopy g) :
    _root_.Homotopy (singularChainMap f) (singularChainMap g) :=
  TopCat.Homotopy.singularChainComplexFunctorObjMap
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (ModuleCat.of ℤ ℤ)

/-- Homotopic continuous maps induce equal actual singular homology maps. -/
theorem homotopy_homologyMap {f g : C(X, Y)} (H : f.Homotopy g) (n : ℕ) :
    singularHomologyMap f n = singularHomologyMap g n :=
  congrArg ModuleCat.Hom.hom ((singularChainHomotopy H).homologyMap_eq n)

/-- Homotopy invariance needs only the existence of an actual continuous homotopy. -/
theorem homotopic_homologyMap {f g : C(X, Y)} (h : f.Homotopic g) (n : ℕ) :
    singularHomologyMap f n = singularHomologyMap g n := by
  obtain ⟨H⟩ := h
  exact homotopy_homologyMap H n

/-- Genuine homotopy inverse maps induce inverse maps on actual integral
singular homology in every degree. -/
def homotopyInverseHomologyEquiv (f : C(X, Y)) (g : C(Y, X))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) (n : ℕ) :
    SingularHomology X n ≃ₗ[ℤ] SingularHomology Y n where
  toLinearMap := singularHomologyMap f n
  invFun := singularHomologyMap g n
  left_inv a := by
    have h := homotopic_homologyMap hgf n
    rw [singularHomologyMap_comp, singularHomologyMap_id] at h
    exact LinearMap.congr_fun h a
  right_inv a := by
    have h := homotopic_homologyMap hfg n
    rw [singularHomologyMap_comp, singularHomologyMap_id] at h
    exact LinearMap.congr_fun h a

@[simp] theorem homotopyInverseHomologyEquiv_apply (f : C(X, Y)) (g : C(Y, X))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) (n : ℕ)
    (a : SingularHomology X n) :
    homotopyInverseHomologyEquiv f g hgf hfg n a = singularHomologyMap f n a := rfl

@[simp] theorem homotopyInverseHomologyEquiv_symm_apply (f : C(X, Y)) (g : C(Y, X))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) (n : ℕ)
    (a : SingularHomology Y n) :
    (homotopyInverseHomologyEquiv f g hgf hfg n).symm a = singularHomologyMap g n a :=
  rfl

/-- A genuine topological homotopy equivalence gives the actual homology equivalence. -/
def homotopyEquivHomologyEquiv (e : X ≃ₕ Y) (n : ℕ) :
    SingularHomology X n ≃ₗ[ℤ] SingularHomology Y n :=
  homotopyInverseHomologyEquiv e.toFun e.invFun e.left_inv e.right_inv n

@[simp] theorem homotopyEquivHomologyEquiv_toLinearMap (e : X ≃ₕ Y) (n : ℕ) :
    (homotopyEquivHomologyEquiv e n).toLinearMap = singularHomologyMap e.toFun n := rfl

@[simp] theorem homotopyEquivHomologyEquiv_apply (e : X ≃ₕ Y) (n : ℕ)
    (a : SingularHomology X n) :
    homotopyEquivHomologyEquiv e n a = singularHomologyMap e.toFun n a := rfl

@[simp] theorem homotopyEquivHomologyEquiv_symm_apply (e : X ≃ₕ Y) (n : ℕ)
    (a : SingularHomology Y n) :
    (homotopyEquivHomologyEquiv e n).symm a = singularHomologyMap e.symm.toFun n a := rfl

@[simp] theorem homotopyEquivHomologyEquiv_symm (e : X ≃ₕ Y) (n : ℕ) :
    (homotopyEquivHomologyEquiv e n).symm = homotopyEquivHomologyEquiv e.symm n := by
  apply LinearEquiv.ext
  intro a
  rfl

/-- A genuine homeomorphism induces an equivalence of the actual singular homology groups. -/
def homeomorphHomologyEquiv (e : X ≃ₜ Y) (n : ℕ) :
    SingularHomology X n ≃ₗ[ℤ] SingularHomology Y n :=
  homotopyEquivHomologyEquiv e.toHomotopyEquiv n

@[simp] theorem homeomorphHomologyEquiv_toLinearMap (e : X ≃ₜ Y) (n : ℕ) :
    (homeomorphHomologyEquiv e n).toLinearMap = singularHomologyMap (e : C(X, Y)) n :=
  rfl

@[simp] theorem homeomorphHomologyEquiv_apply (e : X ≃ₜ Y) (n : ℕ)
    (a : SingularHomology X n) :
    homeomorphHomologyEquiv e n a = singularHomologyMap (e : C(X, Y)) n a := rfl

@[simp] theorem homeomorphHomologyEquiv_symm_apply (e : X ≃ₜ Y) (n : ℕ)
    (a : SingularHomology Y n) :
    (homeomorphHomologyEquiv e n).symm a = singularHomologyMap (e.symm : C(Y, X)) n a :=
  rfl

@[simp] theorem homeomorphHomologyEquiv_symm (e : X ≃ₜ Y) (n : ℕ) :
    (homeomorphHomologyEquiv e n).symm = homeomorphHomologyEquiv e.symm n := by
  apply LinearEquiv.ext
  intro a
  rfl

@[simp] theorem homeomorphHomologyEquiv_refl (X : Type) [TopologicalSpace X] (n : ℕ) :
    homeomorphHomologyEquiv (Homeomorph.refl X) n =
      LinearEquiv.refl ℤ (SingularHomology X n) := by
  apply LinearEquiv.ext
  intro a
  change singularHomologyMap (ContinuousMap.id X) n a = a
  rw [singularHomologyMap_id]
  rfl

theorem homeomorphHomologyEquiv_trans (e : X ≃ₜ Y) (f : Y ≃ₜ Z) (n : ℕ) :
    homeomorphHomologyEquiv (e.trans f) n =
      (homeomorphHomologyEquiv e n).trans (homeomorphHomologyEquiv f n) := by
  apply LinearEquiv.ext
  intro a
  change singularHomologyMap ((f : C(Y, Z)).comp (e : C(X, Y))) n a =
    singularHomologyMap (f : C(Y, Z)) n (singularHomologyMap (e : C(X, Y)) n a)
  rw [singularHomologyMap_comp]
  rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
