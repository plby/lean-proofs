import Wikipedia.HopfProblem.OrbitPairRealizationSimplex

/-!
# Naturality of the actual characteristic maps

The geometric realization of a simplicial-set morphism sends each native
characteristic simplex to the characteristic simplex of its image.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

theorem realizedMap_characteristic {S T : SSet} (f : S ⟶ T) (n : ℕ)
    (x : S _⦋n⦌) (t : Simplex n) :
    (SSet.toTop.map f) (characteristic S n x t) =
      characteristic T n (f.app (Opposite.op ⦋n⦌) x) t := by
  have h := NatTrans.congr_app (sSetTopAdj.unit.naturality f) (Opposite.op ⦋n⦌)
  have hx := ConcreteCategory.congr_hom h x
  exact (congrArg (fun y ↦ TopCat.toSSetObjEquiv (SSet.toTop.obj T)
    (Opposite.op ⦋n⦌) y t) hx).symm

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
