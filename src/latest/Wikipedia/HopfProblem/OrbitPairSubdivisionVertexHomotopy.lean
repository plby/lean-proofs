import Wikipedia.HopfProblem.OrbitPairSubdivisionGeometry

/-!
# A native geometric comparison fixing the original vertices

On a subdivided standard simplex, affine interpolation joins realization
of the actual last-vertex map to the barycentric map. Singleton chains
represent the original vertices, and these points remain fixed throughout
the homotopy. No claim of a global subdivision homeomorphism is made.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder
open scoped unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz RealizationSimplex AffineCoordinates SecondHurewicz.SimplyConnected

def singletonChain (n : ℕ) (i : Fin (n + 1)) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) where
  finset := {ULift.up i}
  comparable a b := le_total a.val b.val

theorem chainLastVertex_singleton (n : ℕ) (i : Fin (n + 1)) :
    chainLastVertex (singletonChain.{u} n i) = ULift.up i :=
  Finset.mem_singleton.mp (chainLastVertex_mem (singletonChain n i))

theorem chainBarycentre_singleton (n : ℕ) (i : Fin (n + 1)) :
    chainBarycentre n (singletonChain.{u} n i) = stdSimplex.vertex i := by
  classical
  have hf : (fun a : (singletonChain.{u} n i).finset ↦ a.val.down) =
      (fun _ ↦ i) := by
    funext a
    exact congrArg ULift.down (Finset.mem_singleton.mp a.property)
  unfold chainBarycentre
  rw [hf]
  exact simplex_map_const i _

def originalVertex (n : ℕ) (i : Fin (n + 1)) :
    SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋n⦌) :=
  vertex (nerve (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))))
    (ComposableArrows.mk₀ (singletonChain n i))

theorem barycentricMap_originalVertex (n : ℕ) (i : Fin (n + 1)) :
    barycentricMap.{u} n (originalVertex n i) = stdSimplex.vertex i :=
  (nerveInterpolation_vertex (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (chainBarycentre n) (singletonChain n i)).trans (chainBarycentre_singleton n i)

theorem realizedLastVertex_originalVertex (n : ℕ) (i : Fin (n + 1)) :
    realizedLastVertex.{u} n (originalVertex n i) = stdSimplex.vertex i := by
  have h := congrArg (fun f : C(SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋n⦌), Simplex n) ↦
    f (originalVertex n i)) (realizedLastVertex_eq_interpolation n)
  exact h.trans ((nerveInterpolation_vertex
    (NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))
    (fun A ↦ stdSimplex.vertex (chainLastVertex A).down) (singletonChain n i)).trans
      (congrArg (fun a : ULift.{u} (Fin (n + 1)) ↦ stdSimplex.vertex a.down)
        (chainLastVertex_singleton n i)))

def barycentricHomotopy (n : ℕ) :
    (realizedLastVertex.{u} n).HomotopyRel (barycentricMap n) (Set.range (originalVertex n)) where
  toFun p := tetrahedronSimplexBlend p.1 (realizedLastVertex n p.2) (barycentricMap n p.2)
  continuous_toFun :=
    (tetrahedronSimplexBlendMap (ContinuousMap.fst : C(Simplex n × Simplex n, Simplex n))
      ContinuousMap.snd).continuous.comp
        (continuous_fst.prodMk (((realizedLastVertex n).continuous.comp continuous_snd).prodMk
          ((barycentricMap n).continuous.comp continuous_snd)))
  map_zero_left z := tetrahedronSimplexBlend_zero _ _
  map_one_left z := tetrahedronSimplexBlend_one _ _
  prop' t z hz := by
    obtain ⟨i, rfl⟩ := hz
    change tetrahedronSimplexBlend t (realizedLastVertex n (originalVertex n i))
      (barycentricMap n (originalVertex n i)) = realizedLastVertex n (originalVertex n i)
    rw [realizedLastVertex_originalVertex, barycentricMap_originalVertex,
      tetrahedronSimplexBlend_self]

end Wikipedia.HopfProblem.OrbitPair.Subdivision
