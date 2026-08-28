import Wikipedia.NoExoticSixSphere.RelativeNormalizedFiberBoundary
import Wikipedia.NoExoticSixSphere.RelativeIntegralChainSplitting
import Wikipedia.NoExoticSixSphere.RelativeFiberConnecting

/-!
# Descent of the actual fiber-class assignment to relative third homology

The checked assignment kills subspace chains and four-boundaries. It
therefore factors through the actual relative chains and their actual
categorical homology. The representative formula identifies its composite
with the original evaluation transgression, but recovery of the original
fiber class is not asserted.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open PeriodTorusHigherHomology

namespace NoExoticSixSphere.RelativeNormalizedFiberClasses

open RelativeSingularHomology RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (U : Set X) [SimplyConnectedSpace U] (a : U)
  (hπ : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))

def relativeChainOperator : (complex U).X 3 →ₗ[ℤ] SingularHomology (Fiber U a) 2 :=
  (classOperator U a hπ).comp (quotientSection U 3)

theorem relativeChainOperator_quotientMap (c : Chains X 3) :
    relativeChainOperator U a hπ (quotientMap U 3 c) = classOperator U a hπ c := by
  have hq : quotientMap U 3 (quotientSection U 3 (quotientMap U 3 c) - c) = 0 := by
    rw [map_sub, quotientMap_section, sub_self]
  have he := classOperator_supported U a hπ _ ((quotientMap_eq_zero_iff U 3 _).mp hq)
  rw [map_sub] at he
  exact sub_eq_zero.mp he

theorem relativeChainOperator_boundary (b : (complex U).X 4) :
    relativeChainOperator U a hπ (((complex U).d 4 3).hom b) = 0 := by
  obtain ⟨c, rfl⟩ := quotientMap_surjective U 4 b
  rw [boundary_quotientMap, relativeChainOperator_quotientMap, classOperator_boundary]

def homologyMap : Homology U 3 →ₗ[ℤ] SingularHomology (Fiber U a) 2 :=
  homologyDesc (complex U) 3
    ((relativeChainOperator U a hπ).comp (ModuleHomology.Cycle (complex U) 3).subtype)
    (relativeChainOperator_boundary U a hπ)

theorem homologyMap_cycleClass (c : ModuleHomology.Cycle (complex U) 3) :
    homologyMap U a hπ (ModuleHomology.cycleClass (complex U) 3 c) =
      relativeChainOperator U a hπ c.val :=
  homologyDesc_cycleClass (complex U) 3 _ _ c

theorem homologyMap_quotientCycle (c : Chains X 3)
    (hc : ((complex U).d 3 2).hom (quotientMap U 3 c) = 0) :
    homologyMap U a hπ (ModuleHomology.cycleClass (complex U) 3
      (ModuleHomology.mkCycle (complex U) 3 (quotientMap U 3 c) hc)) =
        classOperator U a hπ c := by
  rw [homologyMap_cycleClass, ModuleHomology.mkCycle_val, relativeChainOperator_quotientMap]

theorem homologyMap_simplex (smp : RelativeSimplexCycles.RelativeSimplex U 3) :
    homologyMap U a hπ (RelativeSimplexCycles.homologyClass U 2 smp) =
      simplexClass U a hπ smp.val := by
  change homologyMap U a hπ (ModuleHomology.cycleClass (complex U) 3
    (RelativeSimplexCycles.cycle U 2 smp)) = _
  rw [homologyMap_cycleClass]
  change relativeChainOperator U a hπ (quotientMap U 3 (simplexChain X 3 smp.val)) = _
  rw [relativeChainOperator_quotientMap, classOperator_simplex]

theorem homologyMap_transgression_cycle (c : ModuleHomology.Cycle (singularComplex (Fiber U a)) 2) :
    homologyMap U a hπ (transgression U a 2
      (ModuleHomology.cycleClass (singularComplex (Fiber U a)) 2 c)) =
        classOperator U a hπ (ambientPrism U a 2 c.val) := by
  rw [transgression_cycleClass, homologyMap_cycleClass, ChainHomotopyDegreeShift.cycleMap_val,
    ← quotient_ambientPrism, relativeChainOperator_quotientMap]

end NoExoticSixSphere.RelativeNormalizedFiberClasses
