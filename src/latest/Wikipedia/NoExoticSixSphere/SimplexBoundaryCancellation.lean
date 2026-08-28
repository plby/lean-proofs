import Wikipedia.NoExoticSixSphere.SimplexBoundaryChains
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Signed cancellation of five coherent tetrahedron-boundary maps

Each two-face occurs twice with opposite signs. The hypothesis identifies
the original continuous maps on those shared two-faces. The resulting
chain equality and homology equality use the actual singular chains.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.SimplexBoundaryChains

variable {X : Type} [TopologicalSpace X]

theorem alternating_four_sum {A : Type*} [AddCommGroup A] (v : Fin 5 → Fin 4 → A)
    (h : ∀ i j : Fin 4, i ≤ j → v j.succ i = v i.castSucc j) :
    (∑ i : Fin 5, (-1 : ℤ) ^ i.val • ∑ j : Fin 4, (-1 : ℤ) ^ j.val • v i j) = 0 := by
  have h00 : v 1 0 = v 0 0 := h 0 0 (by decide)
  have h01 : v 2 0 = v 0 1 := h 0 1 (by decide)
  have h02 : v 3 0 = v 0 2 := h 0 2 (by decide)
  have h03 : v 4 0 = v 0 3 := h 0 3 (by decide)
  have h11 : v 2 1 = v 1 1 := h 1 1 (by decide)
  have h12 : v 3 1 = v 1 2 := h 1 2 (by decide)
  have h13 : v 4 1 = v 1 3 := h 1 3 (by decide)
  have h22 : v 3 2 = v 2 2 := h 2 2 (by decide)
  have h23 : v 4 2 = v 2 3 := h 2 3 (by decide)
  have h33 : v 4 3 = v 3 3 := h 3 3 (by decide)
  norm_num [Fin.sum_univ_succ]
  simp only [show (2 : Fin 3).succ = 3 by decide,
    show (2 : Fin 4).succ = 3 by decide, show (3 : Fin 4).succ = 4 by decide]
  rw [h00, h01, h02, h03, h11, h12, h13, h22, h23, h33]
  abel

theorem four_chain_cancel (F : Fin 5 → C(SimplexBoundary 3, X))
    (h : ∀ i j : Fin 4, i ≤ j →
      (F j.succ).comp (simplexFaceBoundary 2 i) =
        (F i.castSucc).comp (simplexFaceBoundary 2 j)) :
    (∑ i : Fin 5, (-1 : ℤ) ^ i.val • inducedChain (F i) 2 (chain 2)) = 0 := by
  have hi (i : Fin 5) : inducedChain (F i) 2 (chain 2) =
      ∑ j : Fin 4, (-1 : ℤ) ^ j.val •
        simplexChain X 2 ((F i).comp (simplexFaceBoundary 2 j)) := by
    rw [chain, map_sum]
    simp only [map_zsmul, inducedChain_simplex]
  simp_rw [hi]
  exact alternating_four_sum (fun i j ↦ simplexChain X 2 ((F i).comp (simplexFaceBoundary 2 j)))
    (fun i j hij ↦ congrArg (simplexChain X 2) (h i j hij))

theorem four_homology_cancel (F : Fin 5 → C(SimplexBoundary 3, X))
    (h : ∀ i j : Fin 4, i ≤ j →
      (F j.succ).comp (simplexFaceBoundary 2 i) =
        (F i.castSucc).comp (simplexFaceBoundary 2 j)) :
    (∑ i : Fin 5, (-1 : ℤ) ^ i.val • singularHomologyMap (F i) 2
      (ModuleHomology.cycleClass (singularComplex (SimplexBoundary 3)) 2 (cycle 1))) = 0 := by
  have hc : (∑ i : Fin 5, (-1 : ℤ) ^ i.val •
      ModuleHomology.mapCycles (singularChainMap (F i)) 2 (cycle 1)) = 0 := by
    apply Subtype.ext
    change (ModuleHomology.Cycle (singularComplex X) 2).subtype
      (∑ i : Fin 5, (-1 : ℤ) ^ i.val •
        ModuleHomology.mapCycles (singularChainMap (F i)) 2 (cycle 1)) = 0
    simp only [map_sum, map_zsmul, Submodule.subtype_apply, ModuleHomology.mapCycles_val]
    exact four_chain_cancel F h
  have he := congrArg (ModuleHomology.cycleClass (singularComplex X) 2) hc
  simpa only [map_sum, map_zsmul, map_zero, ← ModuleHomology.homologyMap_cycleClass] using he

end NoExoticSixSphere.SimplexBoundaryChains
