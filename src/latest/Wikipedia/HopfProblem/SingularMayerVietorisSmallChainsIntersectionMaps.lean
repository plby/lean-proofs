import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsInclusions

/-!
# Singular-chain maps from the actual intersection

The two intersection inclusions induce injective chain maps, and their
composites with the ambient inclusions are the same actual singular-chain map.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

def intersectionToLeft (U V : Set X) :
    singularComplex (U ∩ V : Set X) ⟶ singularComplex U :=
  singularChainMap (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U))

def intersectionToRight (U V : Set X) :
    singularComplex (U ∩ V : Set X) ⟶ singularComplex V :=
  singularChainMap (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))

theorem intersectionToLeft_ambient (U V : Set X) :
    intersectionToLeft U V ≫ singularChainMap (subtypeInclusion U) =
      singularChainMap (subtypeInclusion (U ∩ V)) := by
  have h := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)))
      (TopCat.ofHom (subtypeInclusion U))
  exact h.symm

theorem intersectionToRight_ambient (U V : Set X) :
    intersectionToRight U V ≫ singularChainMap (subtypeInclusion V) =
      singularChainMap (subtypeInclusion (U ∩ V)) := by
  have h := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj
    (ModuleCat.of ℤ ℤ)).map_comp
      (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)))
      (TopCat.ofHom (subtypeInclusion V))
  exact h.symm

@[simp] theorem intersectionToLeft_ambient_apply (U V : Set X) (n : ℕ)
    (c : Chains (U ∩ V : Set X) n) :
    inducedChain (subtypeInclusion U) n (((intersectionToLeft U V).f n).hom c) =
      inducedChain (subtypeInclusion (U ∩ V)) n c :=
  congrArg (fun f => (f.f n).hom c) (intersectionToLeft_ambient U V)

@[simp] theorem intersectionToRight_ambient_apply (U V : Set X) (n : ℕ)
    (c : Chains (U ∩ V : Set X) n) :
    inducedChain (subtypeInclusion V) n (((intersectionToRight U V).f n).hom c) =
      inducedChain (subtypeInclusion (U ∩ V)) n c :=
  congrArg (fun f => (f.f n).hom c) (intersectionToRight_ambient U V)

theorem intersectionToLeft_f_injective (U V : Set X) (n : ℕ) :
    Function.Injective ((intersectionToLeft U V).f n).hom := by
  intro a b hab
  apply subtypeInclusion_chain_injective (U ∩ V) n
  calc
    _ = inducedChain (subtypeInclusion U) n (((intersectionToLeft U V).f n).hom a) :=
      (intersectionToLeft_ambient_apply U V n a).symm
    _ = inducedChain (subtypeInclusion U) n (((intersectionToLeft U V).f n).hom b) :=
      congrArg (inducedChain (subtypeInclusion U) n) hab
    _ = _ := intersectionToLeft_ambient_apply U V n b

theorem intersectionToRight_f_injective (U V : Set X) (n : ℕ) :
    Function.Injective ((intersectionToRight U V).f n).hom := by
  intro a b hab
  apply subtypeInclusion_chain_injective (U ∩ V) n
  calc
    _ = inducedChain (subtypeInclusion V) n (((intersectionToRight U V).f n).hom a) :=
      (intersectionToRight_ambient_apply U V n a).symm
    _ = inducedChain (subtypeInclusion V) n (((intersectionToRight U V).f n).hom b) :=
      congrArg (inducedChain (subtypeInclusion V) n) hab
    _ = _ := intersectionToRight_ambient_apply U V n b


end Wikipedia.HopfProblem.SingularMayerVietoris
