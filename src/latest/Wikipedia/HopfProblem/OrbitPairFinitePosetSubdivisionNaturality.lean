import Wikipedia.HopfProblem.OrbitPairFinitePosetLinearEmbedding

/-!
# Naturality and standard-simplex comparison for finite-poset subdivision

Injective monotone vertex maps commute with the coordinate map of a
face-poset subdivision. For a finite linear order, projecting the ulifted
coordinates recovers the already verified native barycentric map.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder
open scoped Classical

namespace Wikipedia.HopfProblem.OrbitPair.FinitePoset

open FirstHurewicz RealizationSimplex AffineCoordinates Subdivision

variable (P : Type u) [PartialOrder P] [Fintype P]

theorem subdivisionCoordinates_naturality {Q : Type u} [PartialOrder Q] [Fintype Q]
    (f : P →o Q) (hf : Function.Injective f)
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    subdivisionCoordinates Q
      ((SSet.toTop.map (nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor)) z) =
      stdSimplex.map f (subdivisionCoordinates P z) := by
  obtain ⟨k, x, t, rfl⟩ := exists_characteristic (nerve (NonemptyFiniteChains P)) z
  have hl := subdivisionCoordinates_characteristic Q k
    ((nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor).app (Opposite.op ⦋k⦌) x) t
  have hr := subdivisionCoordinates_characteristic P k x t
  refine ((congrArg (subdivisionCoordinates Q)
    (realizedMap_characteristic
      (nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor) k x t)).trans hl).trans ?_
  have hv : (fun i : Fin (k + 1) ↦ chainDistribution Q ((x.obj i).map f)) =
      (fun i ↦ stdSimplex.map f (chainDistribution P (x.obj i))) :=
    funext (fun i ↦ chainDistribution_map P f hf (x.obj i))
  exact (congrArg (fun a ↦ weighted a t) hv).trans
    ((simplex_map_weighted f (fun i ↦ chainDistribution P (x.obj i)) t).symm.trans
      (congrArg (stdSimplex.map f) hr.symm))

theorem chainBarycentre_eq_map_distribution (n : ℕ)
    (A : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    chainBarycentre n A = stdSimplex.map ULift.down
      (chainDistribution (ULift.{u} (Fin (n + 1))) A) := by
  let : Nonempty A.finset := A.nonempty.to_subtype
  exact (stdSimplex.map_comp_apply (Subtype.val : A.finset → ULift.{u} (Fin (n + 1)))
    ULift.down (stdSimplex.barycenter : stdSimplex ℝ A.finset)).symm

theorem subdivisionCoordinates_ulift (n : ℕ)
    (z : SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋n⦌)) :
    stdSimplex.map ULift.down (subdivisionCoordinates (ULift.{u} (Fin (n + 1))) z) =
      barycentricMap n z := by
  obtain ⟨k, x, t, rfl⟩ := exists_characteristic (SimplexCategory.sd.{u}.obj ⦋n⦌) z
  have h := subdivisionCoordinates_characteristic (ULift.{u} (Fin (n + 1))) k x t
  refine (congrArg (stdSimplex.map ULift.down) h).trans ?_
  refine (simplex_map_weighted ULift.down
    (fun i ↦ chainDistribution (ULift.{u} (Fin (n + 1))) (x.obj i)) t).trans ?_
  have hv : (fun i : Fin (k + 1) ↦ stdSimplex.map ULift.down
      (chainDistribution (ULift.{u} (Fin (n + 1))) (x.obj i))) =
      (fun i ↦ chainBarycentre n (x.obj i)) :=
    funext (fun i ↦ (chainBarycentre_eq_map_distribution n (x.obj i)).symm)
  exact (congrArg (fun a ↦ weighted a t) hv).trans
    (nerveInterpolation_characteristic
      (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) (chainBarycentre n) k x t).symm

theorem subdivisionCoordinates_standardComparison (n : ℕ)
    (f : P →o ULift.{u} (Fin (n + 1))) (hf : Function.Injective f)
    (z : SSet.toTop.obj (nerve (NonemptyFiniteChains P))) :
    barycentricMap n
      ((SSet.toTop.map (nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor)) z) =
      stdSimplex.map (fun p ↦ (f p).down) (subdivisionCoordinates P z) :=
  (subdivisionCoordinates_ulift n _).symm.trans
    ((congrArg (stdSimplex.map ULift.down) (subdivisionCoordinates_naturality P f hf z)).trans
      (stdSimplex.map_comp_apply f ULift.down (subdivisionCoordinates P z)))

end Wikipedia.HopfProblem.OrbitPair.FinitePoset
