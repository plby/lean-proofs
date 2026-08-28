import Wikipedia.NoExoticSixSphere.RelativeSingularHomology
import Wikipedia.NoExoticSixSphere.ChainHomotopyDegreeShift
import Wikipedia.HopfProblem.OrbitPairHomotopyFiber
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The actual evaluation-prism map from fiber homology to relative homology

For a genuine subspace pair, the fiber's evaluation homotopy runs from
the included source projection to the chosen point of the subspace.
Both endpoint chain maps therefore vanish in the actual relative
complex. Its prism induces the degree-raising map constructed here.
No injectivity, surjectivity, or relative Hurewicz theorem is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open OrbitPair

namespace NoExoticSixSphere.RelativeFiberHomology

variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]

theorem through_subspace_zero (U : Set X) (f : C(Z, U)) :
    singularChainMap ((subtypeInclusion U).comp f) ≫ RelativeSingularHomology.projection U = 0 := by
  have h : singularChainMap ((subtypeInclusion U).comp f) =
      singularChainMap f ≫ RelativeSingularHomology.inclusion U := by
    ext n c
    exact LinearMap.congr_fun (inducedChain_comp f (subtypeInclusion U) n) c
  rw [h, Category.assoc, RelativeSingularHomology.inclusion_projection, comp_zero]

abbrev Fiber (U : Set X) (a : U) := HomotopyFiber.Space (subtypeInclusion U) a.val

def prism (U : Set X) (a : U) :
    _root_.Homotopy (0 : singularComplex (Fiber U a) ⟶ RelativeSingularHomology.complex U) 0 := by
  let H := (singularChainHomotopy
    (HomotopyFiber.projectionNullhomotopy (subtypeInclusion U) a).toHomotopy).compRight
      (RelativeSingularHomology.projection U)
  have h₀ := through_subspace_zero U (HomotopyFiber.projection (subtypeInclusion U) a.val)
  have h₁ : singularChainMap (ContinuousMap.const (Fiber U a) a.val) ≫
      RelativeSingularHomology.projection U = 0 :=
    through_subspace_zero U (ContinuousMap.const (Fiber U a) a)
  exact
    { hom := H.hom
      zero := H.zero
      comm := fun n ↦ by
        have h₀n := congrArg (fun g : singularComplex (Fiber U a) ⟶
          RelativeSingularHomology.complex U ↦ g.f n) h₀
        have h₁n := congrArg (fun g : singularComplex (Fiber U a) ⟶
          RelativeSingularHomology.complex U ↦ g.f n) h₁
        exact h₀n.symm.trans ((H.comm n).trans
          (congrArg (fun m ↦ dNext n H.hom + prevD n H.hom + m) h₁n)) }

theorem prism_apply (U : Set X) (a : U) (n : ℕ) (c : Chains (Fiber U a) n) :
    ChainHomotopyDegreeShift.prism (prism U a) n c =
      RelativeSingularHomology.quotientMap U (n + 1)
        (((singularChainHomotopy
          (HomotopyFiber.projectionNullhomotopy (subtypeInclusion U) a).toHomotopy).hom
            n (n + 1)).hom c) := rfl

def transgression (U : Set X) (a : U) (n : ℕ) :
    SingularHomology (Fiber U a) n →ₗ[ℤ] RelativeSingularHomology.Homology U (n + 1) :=
  ChainHomotopyDegreeShift.homologyMap (prism U a) n

theorem transgression_cycleClass (U : Set X) (a : U) (n : ℕ)
    (c : ModuleHomology.Cycle (singularComplex (Fiber U a)) n) :
    transgression U a n (ModuleHomology.cycleClass (singularComplex (Fiber U a)) n c) =
      ModuleHomology.cycleClass (RelativeSingularHomology.complex U) (n + 1)
        (ChainHomotopyDegreeShift.cycleMap (prism U a) n c) :=
  ChainHomotopyDegreeShift.homologyMap_cycleClass (prism U a) n c

end NoExoticSixSphere.RelativeFiberHomology
