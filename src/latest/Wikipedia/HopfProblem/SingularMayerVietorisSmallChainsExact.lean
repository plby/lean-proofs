import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsAlgebra
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsCoverMaps
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsIntersectionMaps

/-!
# The actual short exact sequence of small singular chains

For arbitrary subsets `U` and `V`, the difference and sum maps give a short
exact sequence from the singular chains of `U ∩ V`, through the categorical
biproduct of the singular chains of `U` and `V`, to their actual small chains.
No open-cover or quasi-isomorphism hypothesis is used.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The two restrictions of the intersection inclusion agree as maps to small chains. -/
theorem intersection_toSmall_comm :
    intersectionToLeft U V ≫ toSmallLeft U V =
      intersectionToRight U V ≫ toSmallRight U V := by
  apply (cancel_mono (smallInclusion U V)).mp
  simp only [Category.assoc, toSmallLeft_inclusion, toSmallRight_inclusion,
    intersectionToLeft_ambient, intersectionToRight_ambient]

/-- Equality of chains from the two subspaces lifts to a chain on their actual intersection. -/
theorem toSmall_overlap_lift (n : ℕ) (x : Chains U n) (y : Chains V n)
    (hxy : ((toSmallLeft U V).f n).hom x = ((toSmallRight U V).f n).hom y) :
    ∃ z : Chains (U ∩ V : Set X) n,
      ((intersectionToLeft U V).f n).hom z = x ∧
        ((intersectionToRight U V).f n).hom z = y := by
  have hxy' : inducedChain (subtypeInclusion U) n x =
      inducedChain (subtypeInclusion V) n y :=
    congrArg (fun s : (smallComplex U V).X n => s.1) hxy
  have hy : inducedChain (subtypeInclusion U) n x ∈ supportedChainSubmodule V n := by
    rw [hxy']
    exact subtypeInclusion_chain_mem V n y
  have hi : inducedChain (subtypeInclusion U) n x ∈
      supportedChainSubmodule U n ⊓ supportedChainSubmodule V n :=
    ⟨subtypeInclusion_chain_mem U n x, hy⟩
  rw [supportedChainSubmodule_inf, ← subtypeInclusion_chain_range (U ∩ V) n] at hi
  obtain ⟨z, hz⟩ := hi
  refine ⟨z, ?_, ?_⟩
  · apply subtypeInclusion_chain_injective U n
    rw [intersectionToLeft_ambient_apply]
    exact hz
  · apply subtypeInclusion_chain_injective V n
    rw [intersectionToRight_ambient_apply]
    exact hz.trans hxy'

/-- The categorical biproduct of the two actual singular chain complexes. -/
def middleComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  singularComplex U ⊞ singularComplex V

/-- The difference of the two actual intersection inclusions. -/
def leftMap : singularComplex (U ∩ V : Set X) ⟶ middleComplex U V :=
  biprod.lift (intersectionToLeft U V) (-(intersectionToRight U V))

/-- The sum of the actual maps from the subspaces to small chains. -/
def rightMap : middleComplex U V ⟶ smallComplex U V :=
  biprod.desc (toSmallLeft U V) (toSmallRight U V)

@[simp] theorem leftMap_fst :
    leftMap U V ≫ (biprod.fst : middleComplex U V ⟶ singularComplex U) =
      intersectionToLeft U V :=
  biprod.lift_fst _ _

@[simp] theorem leftMap_snd :
    leftMap U V ≫ (biprod.snd : middleComplex U V ⟶ singularComplex V) =
      -(intersectionToRight U V) :=
  biprod.lift_snd _ _

@[simp] theorem inl_rightMap :
    (biprod.inl : singularComplex U ⟶ middleComplex U V) ≫ rightMap U V =
      toSmallLeft U V :=
  biprod.inl_desc _ _

@[simp] theorem inr_rightMap :
    (biprod.inr : singularComplex V ⟶ middleComplex U V) ≫ rightMap U V =
      toSmallRight U V :=
  biprod.inr_desc _ _

theorem leftMap_rightMap : leftMap U V ≫ rightMap U V = 0 := by
  change biprod.lift _ _ ≫ biprod.desc _ _ = 0
  rw [biprod.lift_desc, Preadditive.neg_comp, intersection_toSmall_comm, add_neg_cancel]

/-- The actual singular-chain short complex for the two subsets. -/
def chainSequence : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (leftMap U V) (rightMap U V) (leftMap_rightMap U V)

@[simp] theorem chainSequence_f : (chainSequence U V).f = leftMap U V := rfl

@[simp] theorem chainSequence_g : (chainSequence U V).g = rightMap U V := rfl

/-- The genuine small-chain Mayer–Vietoris sequence is short exact in every degree. -/
theorem chainSequence_shortExact : (chainSequence U V).ShortExact :=
  SmallChainBiprod.shortExactOfComplexes (intersectionToLeft U V) (intersectionToRight U V)
    (toSmallLeft U V) (toSmallRight U V) (intersection_toSmall_comm U V)
    (intersectionToLeft_f_injective U V) (toSmall_jointly_surjective U V)
    (toSmall_overlap_lift U V)

instance leftMap_mono : Mono (leftMap U V) :=
  (chainSequence_shortExact U V).mono_f

instance rightMap_epi : Epi (rightMap U V) :=
  (chainSequence_shortExact U V).epi_g

end Wikipedia.HopfProblem.SingularMayerVietoris
