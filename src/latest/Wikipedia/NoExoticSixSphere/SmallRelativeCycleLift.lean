import Wikipedia.NoExoticSixSphere.RelativeSubspaceChainInjection
import Wikipedia.NoExoticSixSphere.SmallCoefficientChainRange

/-!
# Original relative cycles lifted inside the first subspace

The native small-chain image splits as the sum of actual chains on the
two pieces. The first summand represents the same relative chain, and
injectivity of the original pair inclusion proves its relative cycle
condition inside the first subspace.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCoefficients

open RelativeSingularHomology (overlapIn)
open SingularSubcomplex (SmallChains smallInclusionMap)

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ) (U V : Set X)

/-- Every original small-chain image is an actual sum of the two subspace-chain images. -/
theorem exists_small_chain_decomposition (n : ℕ) (c : SmallChains R U V n) :
    ∃ (u : CoefficientChains.Chains R U n) (v : CoefficientChains.Chains R V n),
      smallInclusionMap R U V n c = ((inclusion R U).f n).hom u + ((inclusion R V).f n).hom v := by
  obtain ⟨_, ⟨u, rfl⟩, _, ⟨v, rfl⟩, he⟩ := Submodule.mem_sup.mp
    (SingularSubcomplex.smallInclusion_mem_sup R U V n c)
  exact ⟨u, v, he.symm⟩

/-- The original relative projection kills the second summand of a small-chain decomposition. -/
theorem subtypePairMap_of_decomposition (n : ℕ) (c : SmallChains R U V n)
    (u : CoefficientChains.Chains R U n) (v : CoefficientChains.Chains R V n)
    (he : smallInclusionMap R U V n c =
      ((inclusion R U).f n).hom u + ((inclusion R V).f n).hom v) :
    ((subtypePairMap R U V).f n).hom (quotientMap R (overlapIn U V) n u) =
      quotientMap R V n (smallInclusionMap R U V n c) := by
  have hmap := congrArg (fun m => (m.f n).hom u)
    (projection_mapChain R (subtypeInclusion U)
      (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx))
  have hzero : quotientMap R V n (((inclusion R V).f n).hom v) = 0 :=
    congrArg (fun m => (m.f n).hom v) (cokernel.condition (inclusion R V))
  apply hmap.trans
  symm
  exact (congrArg (quotientMap R V n) he).trans
    (((quotientMap R V n).map_add _ _).trans
      ((congrArg (fun t => quotientMap R V n (((inclusion R U).f n).hom u) + t) hzero).trans
        (add_zero _)))

/-- An actual small representative of an ambient relative cycle lifts to a relative cycle in `U`. -/
theorem exists_small_relative_cycle (n : ℕ) (c : SmallChains R U V n)
    (z : ModuleHomology.Cycle (complex R V) n)
    (hz : z.val = quotientMap R V n (smallInclusionMap R U V n c)) :
    ∃ (u : CoefficientChains.Chains R U n) (v : CoefficientChains.Chains R V n)
      (y : ModuleHomology.Cycle (complex R (overlapIn U V)) n),
      smallInclusionMap R U V n c = ((inclusion R U).f n).hom u + ((inclusion R V).f n).hom v ∧
      y.val = quotientMap R (overlapIn U V) n u ∧
      ModuleHomology.mapCycles (subtypePairMap R U V) n y = z := by
  obtain ⟨u, v, he⟩ := exists_small_chain_decomposition R U V n c
  let f := subtypePairMap R U V
  have hmap : (f.f n).hom (quotientMap R (overlapIn U V) n u) = z.val :=
    (subtypePairMap_of_decomposition R U V n c u v he).trans hz.symm
  have hy : ((complex R (overlapIn U V)).d n (n - 1)).hom
      (quotientMap R (overlapIn U V) n u) = 0 := by
    apply subtypePairMap_injective R U V (n - 1)
    exact (congrArg (fun m => m.hom (quotientMap R (overlapIn U V) n u))
      (f.comm n (n - 1))).symm.trans
        ((congrArg ((complex R V).d n (n - 1)).hom hmap).trans
          ((ModuleHomology.cycle_condition (complex R V) n z).trans
            (f.f (n - 1)).hom.map_zero.symm))
  let y := ModuleHomology.mkCycle (complex R (overlapIn U V)) n
    (quotientMap R (overlapIn U V) n u) hy
  exact ⟨u, v, y, he, rfl, Subtype.ext ((ModuleHomology.mapCycles_val f n y).trans hmap)⟩

end NoExoticSixSphere.RelativeCoefficients
