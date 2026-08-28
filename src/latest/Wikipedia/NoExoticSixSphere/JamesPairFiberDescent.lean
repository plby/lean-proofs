import Wikipedia.NoExoticSixSphere.JamesPairFiberClasses
import Wikipedia.NoExoticSixSphere.RelativeNormalizedFiberDescent

/-!
# The descended actual fiber-homology map for the original James pair

All connectivity inputs are discharged. The actual normalized assignment
kills four-boundaries and induces a map from original relative third
homology to original fiber second homology. The pair's relative acyclicity
annihilates its assigned evaluation-prism classes. The later detection
module uses an ending-path pair to prove surjectivity of this descended
map, fiber homology vanishing, and transgression injectivity.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.JamesSphere.PairNormalization

open ComparisonCylinder RelativeSingularHomology

attribute [local instance] cylinderSimplyConnected sourceSimplyConnected

theorem fiber_signed_faces (n : ℕ) (a : sourceImage (n + 2))
    (smp : C(Simplex 4, Cylinder (n + 2))) :
    (∑ i : Fin 5, (-1 : ℤ) ^ i.val • simplexFiberClass n a (smp.comp (simplexFace 3 i))) = 0 :=
  RelativeNormalizedFiberClasses.signed_faces (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a) smp

theorem fiberClassOperator_boundary (n : ℕ) (a : sourceImage (n + 2))
    (c : Chains (Cylinder (n + 2)) 4) :
    fiberClassOperator n a (((singularComplex (Cylinder (n + 2))).d 4 3).hom c) = 0 :=
  RelativeNormalizedFiberClasses.classOperator_boundary _ _ _ c

def fiberHomologyMap (n : ℕ) (a : sourceImage (n + 2)) :
    Homology (sourceImage (n + 2)) 3 →ₗ[ℤ] SingularHomology (SourceFiber (n + 2) a) 2 :=
  RelativeNormalizedFiberClasses.homologyMap (sourceImage (n + 2)) a
    (inclusion_piTwo_surjective n a)

theorem fiberHomologyMap_quotientCycle (n : ℕ) (a : sourceImage (n + 2))
    (c : Chains (Cylinder (n + 2)) 3)
    (hc : ((complex (sourceImage (n + 2))).d 3 2).hom
      (quotientMap (sourceImage (n + 2)) 3 c) = 0) :
    fiberHomologyMap n a (ModuleHomology.cycleClass (complex (sourceImage (n + 2))) 3
      (ModuleHomology.mkCycle (complex (sourceImage (n + 2))) 3
        (quotientMap (sourceImage (n + 2)) 3 c) hc)) = fiberClassOperator n a c :=
  RelativeNormalizedFiberClasses.homologyMap_quotientCycle _ _ _ c hc

theorem fiberHomologyMap_simplex (n : ℕ) (a : sourceImage (n + 2))
    (smp : RelativeSimplexCycles.RelativeSimplex (sourceImage (n + 2)) 3) :
    fiberHomologyMap n a (RelativeSimplexCycles.homologyClass (sourceImage (n + 2)) 2 smp) =
      simplexFiberClass n a smp.val :=
  RelativeNormalizedFiberClasses.homologyMap_simplex _ _ _ smp

theorem fiberHomologyMap_transgression_cycle (n : ℕ) (a : sourceImage (n + 2))
    (c : ModuleHomology.Cycle (singularComplex (SourceFiber (n + 2) a)) 2) :
    fiberHomologyMap n a (RelativeFiberHomology.transgression (sourceImage (n + 2)) a 2
      (ModuleHomology.cycleClass (singularComplex (SourceFiber (n + 2) a)) 2 c)) =
        fiberClassOperator n a
          (RelativeFiberHomology.ambientPrism (sourceImage (n + 2)) a 2 c.val) :=
  RelativeNormalizedFiberClasses.homologyMap_transgression_cycle _ _ _ c

theorem fiberHomologyMap_apply_eq_zero (n : ℕ) (a : sourceImage (n + 2))
    (c : Homology (sourceImage (n + 2)) 3) : fiberHomologyMap n a c = 0 := by
  rw [relative_homology_eq_zero (n + 2) 3 (by omega) c, map_zero]

theorem assignedPrism_eq_zero (n : ℕ) (a : sourceImage (n + 2))
    (c : ModuleHomology.Cycle (singularComplex (SourceFiber (n + 2) a)) 2) :
    fiberClassOperator n a
      (RelativeFiberHomology.ambientPrism (sourceImage (n + 2)) a 2 c.val) = 0 := by
  rw [← fiberHomologyMap_transgression_cycle, fiberHomologyMap_apply_eq_zero]

end NoExoticSixSphere.JamesSphere.PairNormalization
