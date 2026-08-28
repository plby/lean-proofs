import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedInverse
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedSquareNormalization

/-!
# The constructed inverse recovers every native second homotopy class

The original fundamental square chain is exactly its lower triangle minus
its upper triangle. Vertex normalization fixes both triangles, and the
actual coherent edge homotopies recover the original native square class.
Quotient induction therefore proves the left-inverse identity.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The chain assignment on the genuine square fundamental cycle is the
original native homotopy class, before any homology quotient is taken. -/
theorem triangleClassOperator_squareChain (x : X) (p : GenLoop (Fin 2) X x) :
    triangleClassOperator x (squareChain p) = Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [squareChain_two_triangles, map_sub, triangleClassOperator_simplex,
    triangleClassOperator_simplex,
    normalizedTriangle_of_verticesBased x _ (lowerSquareTriangle_verticesBased p),
    normalizedTriangle_of_verticesBased x _ (upperSquareTriangle_verticesBased p)]
  exact squareNormalization_class p

@[simp] theorem hurewiczInverse_hurewiczMap_mk (x : X) (p : GenLoop (Fin 2) X x) :
    hurewiczInverse x (hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 2 X x))) =
      Additive.ofMul (⟦p⟧ : π_ 2 X x) := by
  rw [hurewiczMap_representative, hurewiczInverse_cycleClass]
  exact triangleClassOperator_squareChain x p

/-- The other inverse law holds on the actual native homotopy quotient. -/
@[simp] theorem hurewiczInverse_hurewiczMap (x : X) (a : Additive (π_ 2 X x)) :
    hurewiczInverse x (hurewiczMap x a) = a := by
  change hurewiczInverse x (hurewiczMap x (Additive.ofMul (Additive.toMul a))) =
    Additive.ofMul (Additive.toMul a)
  refine Quotient.inductionOn (Additive.toMul a) ?_
  intro p
  exact hurewiczInverse_hurewiczMap_mk x p

theorem hurewiczInverse_comp_hurewiczMap (x : X) :
    (hurewiczInverse x).comp (hurewiczMap x) = LinearMap.id := by
  ext a
  exact hurewiczInverse_hurewiczMap x a

/-- Genuine degree-two Hurewicz injectivity for a simply connected space. -/
theorem hurewiczMap_injective (x : X) : Function.Injective (hurewiczMap x) :=
  Function.LeftInverse.injective (hurewiczInverse_hurewiczMap x)

/-- The original integral linear Hurewicz map is bijective. -/
theorem hurewiczMap_bijective (x : X) : Function.Bijective (hurewiczMap x) :=
  ⟨hurewiczMap_injective x, hurewiczMap_surjective x⟩

/-- Bijectivity of the original multiplicatively written native `π₂` map. -/
theorem hurewiczPi2_bijective (x : X) : Function.Bijective (hurewiczPi2 x) := by
  constructor
  · intro a b h
    have h' : hurewiczMap x (Additive.ofMul a) = hurewiczMap x (Additive.ofMul b) :=
      congrArg Multiplicative.toAdd h
    exact congrArg Additive.toMul (hurewiczMap_injective x h')
  · intro c
    obtain ⟨a, ha⟩ := hurewiczMap_surjective x (Multiplicative.toAdd c)
    exact ⟨Additive.toMul a, congrArg Multiplicative.ofAdd ha⟩

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
