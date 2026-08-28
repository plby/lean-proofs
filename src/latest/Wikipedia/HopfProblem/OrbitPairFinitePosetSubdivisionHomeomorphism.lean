import Wikipedia.HopfProblem.OrbitPairFinitePosetSubdivisionNaturality

/-!
# Homeomorphism between native finite-poset subdivision realizations

Injectivity is transported through an injective finite linear extension
to the already checked standard-simplex barycentric map. Surjectivity is
proved by lifting each nondegenerate characteristic simplex through its
own standard subdivision. All maps and both spaces are native realizations.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder Topology
open scoped Classical

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex Subdivision

variable (P : Type u) [PartialOrder P] [Fintype P]

theorem subdivisionCoordinates_injective : Function.Injective (subdivisionCoordinates P) := by
  intro z w hzw
  let f := (linearEmbedding P).val
  have hf : Function.Injective f := (linearEmbedding P).property
  let F := nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor
  let : Mono F := chainNerveMap_mono f hf
  apply realizedMap_injective F
  apply barycentricMap_injective (Fintype.card P)
  exact (subdivisionCoordinates_standardComparison P (Fintype.card P) f hf z).trans
    ((congrArg (stdSimplex.map (fun p ↦ (f p).down)) hzw).trans
      (subdivisionCoordinates_standardComparison P (Fintype.card P) f hf w).symm)

theorem subdivisionMap_injective : Function.Injective (subdivisionMap P) := by
  intro z w hzw
  apply subdivisionCoordinates_injective P
  exact (coordinates_subdivisionMap P z).symm.trans
    ((congrArg (coordinates P) hzw).trans (coordinates_subdivisionMap P w))

theorem subdivisionMap_surjective : Function.Surjective (subdivisionMap P) := by
  intro y
  obtain ⟨k, x, t, ht, rfl⟩ := exists_positive_nonDegenerate (nerve P) y
  have hx := (PartialOrder.mem_nerve_nonDegenerate_iff_injective x.val).mp x.property
  let f : ULift.{u} (Fin (k + 1)) →o P :=
    { toFun := fun i ↦ x.val.obj i.down
      monotone' := fun i j hij ↦ x.val.monotone hij }
  have hf : Function.Injective f := by
    intro i j hij
    exact ULift.ext i j (hx hij)
  obtain ⟨z, hz⟩ := barycentricMap_surjective.{u} k t
  let q := (SSet.toTop.map (nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor)) z
  refine ⟨q, ?_⟩
  apply coordinates_injective P
  calc
    coordinates P (subdivisionMap P q) = subdivisionCoordinates P q :=
      coordinates_subdivisionMap P q
    _ = stdSimplex.map f (subdivisionCoordinates (ULift.{u} (Fin (k + 1))) z) :=
      subdivisionCoordinates_naturality (ULift.{u} (Fin (k + 1))) f hf z
    _ = stdSimplex.map x.val.obj
        (stdSimplex.map ULift.down (subdivisionCoordinates (ULift.{u} (Fin (k + 1))) z)) :=
      (stdSimplex.map_comp_apply ULift.down x.val.obj
        (subdivisionCoordinates (ULift.{u} (Fin (k + 1))) z)).symm
    _ = stdSimplex.map x.val.obj t :=
      congrArg (stdSimplex.map x.val.obj) ((subdivisionCoordinates_ulift k z).trans hz)
    _ = coordinates P (characteristic (nerve P) k x.val t) :=
      (coordinates_characteristic P k x.val t).symm

instance realizationT2 : T2Space (SSet.toTop.obj (nerve P)) :=
  (coordinates_isClosedEmbedding P).isEmbedding.t2Space

theorem subdivisionMap_isClosedEmbedding : IsClosedEmbedding (subdivisionMap P) :=
  (subdivisionMap P).continuous.isClosedEmbedding (subdivisionMap_injective P)

def subdivisionHomeomorph :
    SSet.toTop.obj (nerve (NonemptyFiniteChains P)) ≃ₜ SSet.toTop.obj (nerve P) :=
  (subdivisionMap_isClosedEmbedding P).isEmbedding.toHomeomorphOfSurjective
    (subdivisionMap_surjective P)

theorem subdivisionHomeomorph_apply (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    subdivisionHomeomorph P z = subdivisionMap P z := rfl

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
