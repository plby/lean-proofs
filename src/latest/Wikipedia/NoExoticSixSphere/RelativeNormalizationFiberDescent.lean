import Wikipedia.NoExoticSixSphere.RelativeNormalizationFiberAssignment
import Wikipedia.NoExoticSixSphere.RelativeIntegralChainSplitting
import Wikipedia.NoExoticSixSphere.RelativeFiberConnecting

/-!
# Descent of the actual normalized fiber assignment in every degree

Support and boundary vanishing factor the original chain assignment
through the actual relative chain complex and its categorical homology.
The representative formulas retain the original simplices and prism.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.RelativeNormalization.Data

open RelativeSingularHomology RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] {U : Set X} {a : U} {n : ℕ} (D : Data U a n)

def relativeChainOperator : (complex U).X (n + 3) →ₗ[ℤ] SingularHomology (Fiber U a) (n + 2) :=
  D.fiberClassOperator.comp (quotientSection U (n + 3))

theorem relativeChainOperator_quotientMap (c : Chains X (n + 3)) :
    D.relativeChainOperator (quotientMap U (n + 3) c) = D.fiberClassOperator c := by
  have hq : quotientMap U (n + 3)
      (quotientSection U (n + 3) (quotientMap U (n + 3) c) - c) = 0 := by
    rw [map_sub, quotientMap_section, sub_self]
  have he := D.fiberClassOperator_supported _ ((quotientMap_eq_zero_iff U (n + 3) _).mp hq)
  rw [map_sub] at he
  exact sub_eq_zero.mp he

theorem relativeChainOperator_boundary (b : (complex U).X (n + 4)) :
    D.relativeChainOperator (((complex U).d (n + 4) (n + 3)).hom b) = 0 := by
  obtain ⟨c, rfl⟩ := quotientMap_surjective U (n + 4) b
  rw [boundary_quotientMap, relativeChainOperator_quotientMap, fiberClassOperator_boundary]

def fiberHomologyMap : Homology U (n + 3) →ₗ[ℤ] SingularHomology (Fiber U a) (n + 2) :=
  homologyDesc (complex U) (n + 3)
    (D.relativeChainOperator.comp (ModuleHomology.Cycle (complex U) (n + 3)).subtype)
    D.relativeChainOperator_boundary

theorem fiberHomologyMap_cycleClass (c : ModuleHomology.Cycle (complex U) (n + 3)) :
    D.fiberHomologyMap (ModuleHomology.cycleClass (complex U) (n + 3) c) =
      D.relativeChainOperator c.val :=
  homologyDesc_cycleClass (complex U) (n + 3) _ _ c

theorem fiberHomologyMap_quotientCycle (c : Chains X (n + 3))
    (hc : ((complex U).d (n + 3) (n + 2)).hom (quotientMap U (n + 3) c) = 0) :
    D.fiberHomologyMap (ModuleHomology.cycleClass (complex U) (n + 3)
      (ModuleHomology.mkCycle (complex U) (n + 3) (quotientMap U (n + 3) c) hc)) =
        D.fiberClassOperator c := by
  rw [fiberHomologyMap_cycleClass, ModuleHomology.mkCycle_val, relativeChainOperator_quotientMap]

theorem fiberHomologyMap_simplex (smp : RelativeSimplexCycles.RelativeSimplex U (n + 3)) :
    D.fiberHomologyMap (RelativeSimplexCycles.homologyClass U (n + 2) smp) =
      D.simplexFiberClass smp.val := by
  change D.fiberHomologyMap (ModuleHomology.cycleClass (complex U) (n + 3)
    (RelativeSimplexCycles.cycle U (n + 2) smp)) = _
  rw [fiberHomologyMap_cycleClass]
  change D.relativeChainOperator (quotientMap U (n + 3) (simplexChain X (n + 3) smp.val)) = _
  rw [relativeChainOperator_quotientMap, fiberClassOperator_simplex]

theorem fiberHomologyMap_simplex_eq_fiberClass
    (smp : RelativeSimplexCycles.RelativeSimplex U (n + 3))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val) :
    D.fiberHomologyMap (RelativeSimplexCycles.homologyClass U (n + 2) smp) =
      RelativeSimplexFiberClass.fiberClass U a n smp hv := by
  rw [fiberHomologyMap_simplex, simplexFiberClass_eq_fiberClass D smp hv]

theorem fiberHomologyMap_transgression_cycle
    (c : ModuleHomology.Cycle (singularComplex (Fiber U a)) (n + 2)) :
    D.fiberHomologyMap (transgression U a (n + 2)
      (ModuleHomology.cycleClass (singularComplex (Fiber U a)) (n + 2) c)) =
        D.fiberClassOperator (ambientPrism U a (n + 2) c.val) := by
  rw [transgression_cycleClass, fiberHomologyMap_cycleClass, ChainHomotopyDegreeShift.cycleMap_val,
    ← quotient_ambientPrism, relativeChainOperator_quotientMap]

end NoExoticSixSphere.RelativeNormalization.Data
