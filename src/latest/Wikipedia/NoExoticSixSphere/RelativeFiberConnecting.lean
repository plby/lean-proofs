import Wikipedia.NoExoticSixSphere.RelativeFiberHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleConnectingCycles

/-!
# The evaluation prism and the actual relative connecting homomorphism

The boundary of the original evaluation prism is the included projected
cycle minus the included constant cycle. The genuine lift-boundary
formula for the pair sequence therefore identifies its connecting map
with projection minus the constant-map homology homomorphism.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris ModuleHomology
open PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

def ambientPrism (n : ℕ) : Chains (Fiber U a) n →ₗ[ℤ] Chains X (n + 1) :=
  ((singularChainHomotopy
    (HomotopyFiber.projectionNullhomotopy (subtypeInclusion U) a).toHomotopy).hom n (n + 1)).hom

theorem quotient_ambientPrism (n : ℕ) (c : Chains (Fiber U a) n) :
    RelativeSingularHomology.quotientMap U (n + 1) (ambientPrism U a n c) =
      ChainHomotopyDegreeShift.prism (prism U a) n c := rfl

theorem ambientPrism_boundary_cycle (n : ℕ) (c : Cycle (singularComplex (Fiber U a)) n) :
    ((singularComplex X).d (n + 1) n).hom (ambientPrism U a n c.val) =
      inducedChain (subtypeInclusion U) n
        (inducedChain (HomotopyFiber.projection (subtypeInclusion U) a.val) n c.val -
          inducedChain (ContinuousMap.const (Fiber U a) a) n c.val) := by
  let H : _root_.Homotopy
      (singularChainMap
        ((subtypeInclusion U).comp (HomotopyFiber.projection (subtypeInclusion U) a.val)))
      (singularChainMap (ContinuousMap.const (Fiber U a) a.val)) :=
    singularChainHomotopy (HomotopyFiber.projectionNullhomotopy (subtypeInclusion U) a).toHomotopy
  have h := H.comm n
  rw [dNext_nat, prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (n + 1) n by rfl)] at h
  have hh := congrArg (fun m : Chains (Fiber U a) n ⟶ Chains X n ↦ m.hom c.val) h
  change inducedChain
      ((subtypeInclusion U).comp (HomotopyFiber.projection (subtypeInclusion U) a.val)) n c.val =
    (H.hom (n - 1) n).hom (((singularComplex (Fiber U a)).d n (n - 1)).hom c.val) +
      ((singularComplex X).d (n + 1) n).hom (ambientPrism U a n c.val) +
        inducedChain (ContinuousMap.const (Fiber U a) a.val) n c.val at hh
  rw [cycle_condition _ n c] at hh
  rw [(H.hom (n - 1) n).hom.map_zero, zero_add] at hh
  have he := eq_sub_iff_add_eq.mpr hh.symm
  have hc : (ContinuousMap.const (Fiber U a) a.val : C(Fiber U a, X)) =
      (subtypeInclusion U).comp (ContinuousMap.const (Fiber U a) a) := rfl
  rw [hc, inducedChain_comp, inducedChain_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, ← map_sub] at he
  exact he

theorem connecting_transgression (n : ℕ) (z : SingularHomology (Fiber U a) n) :
    RelativeSingularHomology.connecting U n (transgression U a n z) =
      singularHomologyMap (HomotopyFiber.projection (subtypeInclusion U) a.val) n z -
        singularHomologyMap (ContinuousMap.const (Fiber U a) a) n z := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective (singularComplex (Fiber U a)) n z
  rw [transgression_cycleClass]
  let z₁ : Cycle (singularComplex U) n :=
    mapCycles (singularChainMap (HomotopyFiber.projection (subtypeInclusion U) a.val)) n c -
      mapCycles (singularChainMap (ContinuousMap.const (Fiber U a) a)) n c
  have hz₁ : inducedChain (subtypeInclusion U) n z₁.val =
      ((singularComplex X).d (n + 1) n).hom (ambientPrism U a n c.val) := by
    change inducedChain (subtypeInclusion U) n
      ((mapCycles (singularChainMap
        (HomotopyFiber.projection (subtypeInclusion U) a.val)) n c).val -
        (mapCycles (singularChainMap (ContinuousMap.const (Fiber U a) a)) n c).val) = _
    rw [mapCycles_val, mapCycles_val]
    exact (ambientPrism_boundary_cycle U a n c).symm
  have h := connectingMap_cycleClass (RelativeSingularHomology.sequence_shortExact U) n
    (ChainHomotopyDegreeShift.cycleMap (prism U a) n c) (ambientPrism U a n c.val)
    (quotient_ambientPrism U a n c.val) z₁ hz₁
  change RelativeSingularHomology.connecting U n
    (cycleClass (RelativeSingularHomology.complex U) (n + 1)
      (ChainHomotopyDegreeShift.cycleMap (prism U a) n c)) = _ at h
  rw [h]
  change cycleClass (singularComplex U) n
    (mapCycles (singularChainMap
      (HomotopyFiber.projection (subtypeInclusion U) a.val)) n c -
      mapCycles (singularChainMap (ContinuousMap.const (Fiber U a) a)) n c) = _
  rw [map_sub, ← homologyMap_cycleClass, ← homologyMap_cycleClass]

end NoExoticSixSphere.RelativeFiberHomology
