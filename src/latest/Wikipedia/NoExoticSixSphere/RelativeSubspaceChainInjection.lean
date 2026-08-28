import Wikipedia.NoExoticSixSphere.SingularChainRangeIntersection
import Wikipedia.NoExoticSixSphere.RelativeSingularExcision
import Wikipedia.NoExoticSixSphere.RelativeCoefficientCycleRepresentatives

/-!
# Injectivity of the original subspace pair map on coefficient chains

The image of chains on the intersection is exactly the intersection
of the two subspace-chain images. Passing to the original relative
quotients therefore gives an injective map in every degree, without
an openness or covering assumption.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCoefficients

open RelativeSingularHomology (overlapIn overlapHomeomorph)

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ) (U V : Set X)

/-- The original inclusion of pairs `(U, U ∩ V) → (X, V)`. -/
abbrev subtypePairMap : complex R (overlapIn U V) ⟶ complex R V :=
  mapChain R (subtypeInclusion U)
    (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx)

abbrev intersectionLeftChain :
    SphereHomologyCoefficients.coefficientComplex R (U ∩ V : Set X) ⟶
      SphereHomologyCoefficients.coefficientComplex R U :=
  spaceMap R (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U))

theorem intersectionLeftChain_inclusion :
    intersectionLeftChain R U V ≫ inclusion R U = inclusion R (U ∩ V) :=
  ((SimplicialCoefficients.chains R).map_comp (SingularSubcomplex.intersectionLeft U V)
    (SingularSubcomplex.inclusion U)).symm.trans
      (congrArg (SimplicialCoefficients.chains R).map
        (SingularSubcomplex.intersectionLeft_inclusion U V))

/-- Intersection chains vanish in the actual relative quotient of the first subspace. -/
theorem quotientMap_intersectionLeft (n : ℕ)
    (b : CoefficientChains.Chains R (U ∩ V : Set X) n) :
    quotientMap R (overlapIn U V) n (((intersectionLeftChain R U V).f n).hom b) = 0 := by
  let e : C((U ∩ V : Set X), overlapIn U V) := (overlapHomeomorph U V).symm
  have he : (subtypeInclusion (overlapIn U V)).comp e =
      ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U) := by
    ext x
    rfl
  have hs : spaceMap R e ≫ inclusion R (overlapIn U V) = intersectionLeftChain R U V :=
    (spaceMap_comp R e (subtypeInclusion (overlapIn U V))).symm.trans (congrArg (spaceMap R) he)
  have hz : intersectionLeftChain R U V ≫ projection R (overlapIn U V) = 0 := by
    rw [← hs, Category.assoc]
    exact (congrArg (fun m => spaceMap R e ≫ m)
      (cokernel.condition (inclusion R (overlapIn U V)))).trans Limits.comp_zero
  exact congrArg (fun m => (m.f n).hom b) hz

/-- Vanishing under the original pair inclusion already means vanishing in the source quotient. -/
theorem subtypePairMap_eq_zero (n : ℕ) (x : (complex R (overlapIn U V)).X n)
    (hx : ((subtypePairMap R U V).f n).hom x = 0) : x = 0 := by
  obtain ⟨d, rfl⟩ := quotientMap_surjective R (overlapIn U V) n x
  have he := congrArg (fun m => (m.f n).hom d)
    (projection_mapChain R (subtypeInclusion U)
      (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hy => hy))
  have hV : ((inclusion R U).f n).hom d ∈ LinearMap.range ((inclusion R V).f n).hom :=
    (quotientMap_eq_zero_iff R V n _).mp (he.symm.trans hx)
  obtain ⟨b, hb⟩ := (SingularSubcomplex.inclusion_range_inter R U V n).ge ⟨⟨d, rfl⟩, hV⟩
  have hd : ((intersectionLeftChain R U V).f n).hom b = d := by
    apply (ModuleCat.mono_iff_injective ((inclusion R U).f n)).mp inferInstance
    exact (congrArg (fun m => (m.f n).hom b) (intersectionLeftChain_inclusion R U V)).trans hb
  exact (congrArg (quotientMap R (overlapIn U V) n) hd.symm).trans
    (quotientMap_intersectionLeft R U V n b)

/-- Every degree of the original subspace pair map is injective. -/
theorem subtypePairMap_injective (n : ℕ) :
    Function.Injective ((subtypePairMap R U V).f n).hom := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply subtypePairMap_eq_zero R U V n (x - y)
  exact (((subtypePairMap R U V).f n).hom.map_sub x y).trans
    ((congrArg (fun t => t - ((subtypePairMap R U V).f n).hom y) hxy).trans (sub_self _))

end NoExoticSixSphere.RelativeCoefficients
