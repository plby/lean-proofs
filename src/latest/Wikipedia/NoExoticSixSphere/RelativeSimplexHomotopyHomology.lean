import Wikipedia.NoExoticSixSphere.SimplexHomotopyChainSupport

/-!
# Relative homology classes are preserved by coherent simplex homotopies

The endpoint and prism are the original singular-chain operators. A
subspace-preserving coherent family sends relative cycles to relative
cycles. Its genuine prism gives a boundary between the endpoint and
original representatives in the actual relative chain complex.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeSimplexHomotopyHomology

open RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (n : ℕ)
  (H : C(Simplex n, X) → C(I × Simplex n, X))
  (H' : C(Simplex (n + 1), X) → C(I × Simplex (n + 1), X))
  (hface : FaceCompatibleHomotopies n H H')
  (hU : ∀ smp, (∀ s, smp s ∈ U) → ∀ p, H smp p ∈ U)

include hface hU

theorem endpoint_cycle_condition (c : Chains X (n + 1))
    (hc : ((complex U).d (n + 1) n).hom (quotientMap U (n + 1) c) = 0) :
    ((complex U).d (n + 1) n).hom
      (quotientMap U (n + 1) (simplexEndpointOperator (n + 1) H' 1 c)) = 0 := by
  rw [boundary_quotientMap, simplexEndpointOperator_boundary n H H' hface]
  apply (quotientMap_eq_zero_iff U n _).mpr
  exact SimplexHomotopyChainSupport.endpoint_mem U n H hU 1 _
    ((relativeCycle_iff U (n + 1) n c).mp hc)

def endpointCycle (c : Chains X (n + 1))
    (hc : ((complex U).d (n + 1) n).hom (quotientMap U (n + 1) c) = 0) :
    ModuleHomology.Cycle (complex U) (n + 1) :=
  ModuleHomology.mkCycle (complex U) (n + 1)
    (quotientMap U (n + 1) (simplexEndpointOperator (n + 1) H' 1 c)) (by
      change ((complex U).d (n + 1) n).hom _ = 0
      exact endpoint_cycle_condition U n H H' hface hU c hc)

theorem prism_boundary_cycle (hzero : ∀ smp, timeSlice (H' smp) 0 = smp)
    (c : Chains X (n + 1))
    (hc : ((complex U).d (n + 1) n).hom (quotientMap U (n + 1) c) = 0) :
    ((complex U).d (n + 2) (n + 1)).hom
        (quotientMap U (n + 2) (simplexPrismOperator (n + 1) H' c)) =
      quotientMap U (n + 1) (simplexEndpointOperator (n + 1) H' 1 c) -
        quotientMap U (n + 1) c := by
  have hp : quotientMap U (n + 1)
      (simplexPrismOperator n H (((singularComplex X).d (n + 1) n).hom c)) = 0 := by
    apply (quotientMap_eq_zero_iff U (n + 1) _).mpr
    exact SimplexHomotopyChainSupport.prism_mem U n H hU _
      ((relativeCycle_iff U (n + 1) n c).mp hc)
  rw [boundary_quotientMap, simplexPrismOperator_boundary n H H' hface,
    simplexEndpointOperator_zero (n + 1) H' hzero, LinearMap.id_apply,
    map_sub, map_sub, hp, sub_zero]

theorem endpointCycle_class (hzero : ∀ smp, timeSlice (H' smp) 0 = smp)
    (c : Chains X (n + 1))
    (hc : ((complex U).d (n + 1) n).hom (quotientMap U (n + 1) c) = 0) :
    ModuleHomology.cycleClass (complex U) (n + 1)
        (endpointCycle U n H H' hface hU c hc) =
      ModuleHomology.cycleClass (complex U) (n + 1)
        (ModuleHomology.mkCycle (complex U) (n + 1) (quotientMap U (n + 1) c)
          (by exact hc)) := by
  apply (ModuleHomology.cycleClass_eq_iff (complex U) (n + 1) _ _).mpr
  exact ⟨quotientMap U (n + 2) (simplexPrismOperator (n + 1) H' c),
    prism_boundary_cycle U n H H' hface hU hzero c hc⟩

end NoExoticSixSphere.RelativeSimplexHomotopyHomology
