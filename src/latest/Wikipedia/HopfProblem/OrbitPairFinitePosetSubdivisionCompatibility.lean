import Wikipedia.HopfProblem.OrbitPairFinitePosetSubdivisionHomeomorphism

/-!
# Compatibility of the actual finite-poset subdivision homeomorphisms

Vertex coordinates commute with every monotone map. The subdivision
homeomorphisms commute with injective monotone maps, because those maps
preserve the uniform distributions on faces. This distinction is needed
when assembling finite iterated subdivisions and their face inclusions.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex

variable (P : Type u) [PartialOrder P] [Fintype P]

theorem coordinates_naturality {Q : Type u} [PartialOrder Q] [Fintype Q]
    (f : P →o Q) (z : SSet.toTop.obj (nerve P)) :
    coordinates Q ((SSet.toTop.map (nerveMap f.monotone.functor)) z) =
      stdSimplex.map f (coordinates P z) := by
  obtain ⟨k, x, t, rfl⟩ := exists_characteristic (nerve P) z
  refine ((congrArg (coordinates Q)
    (realizedMap_characteristic (nerveMap f.monotone.functor) k x t)).trans
      (coordinates_characteristic Q k
        ((nerveMap f.monotone.functor).app (Opposite.op ⦋k⦌) x) t)).trans ?_
  exact (stdSimplex.map_comp_apply x.obj f t).symm.trans
    (congrArg (stdSimplex.map f) (coordinates_characteristic P k x t).symm)

theorem subdivisionMap_naturality {Q : Type u} [PartialOrder Q] [Fintype Q]
    (f : P →o Q) (hf : Function.Injective f)
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    subdivisionMap Q
      ((SSet.toTop.map (nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor)) z) =
      (SSet.toTop.map (nerveMap f.monotone.functor)) (subdivisionMap P z) := by
  apply coordinates_injective Q
  exact (coordinates_subdivisionMap Q _).trans
    ((subdivisionCoordinates_naturality P f hf z).trans
      ((congrArg (stdSimplex.map f) (coordinates_subdivisionMap P z).symm).trans
        (coordinates_naturality P f (subdivisionMap P z)).symm))

theorem subdivisionHomeomorph_naturality {Q : Type u} [PartialOrder Q] [Fintype Q]
    (f : P →o Q) (hf : Function.Injective f)
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    subdivisionHomeomorph Q
      ((SSet.toTop.map (nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor)) z) =
      (SSet.toTop.map (nerveMap f.monotone.functor)) (subdivisionHomeomorph P z) :=
  subdivisionMap_naturality P f hf z

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
