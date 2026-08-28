import Wikipedia.NoExoticSixSphere.SingularSmallSubcomplex
import Wikipedia.NoExoticSixSphere.CoefficientChainPresentation

/-!
# The actual image of native small coefficient chains

The degreewise surjection in the original small-chain short exact
sequence expresses every small-chain image as a sum of two original
subspace-chain images. This statement keeps the native coefficient
complexes and their actual inclusion maps.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ) (U V : Set X)

/-- The original coefficient chains on the actual small singular simplicial set. -/
abbrev SmallChains (n : ℕ) := ((Small U V).chainComplex R).X n

/-- The degree map of the original small-simplex inclusion. -/
abbrev smallInclusionMap (n : ℕ) : SmallChains R U V n →ₗ[ℤ] CoefficientChains.Chains R X n :=
  (((SimplicialCoefficients.chains R).map (smallInclusion U V)).f n).hom

/-- The original small-chain image lies in the sum of the two actual subspace-chain images. -/
theorem smallInclusion_mem_sup (n : ℕ) (c : SmallChains R U V n) :
    smallInclusionMap R U V n c ∈
      LinearMap.range ((RelativeCoefficients.inclusion R U).f n).hom ⊔
        LinearMap.range ((RelativeCoefficients.inclusion R V).f n).hom := by
  let S := (smallChainSquare U V R).shortComplex
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp
    (smallChainSequence_shortExact U V R) n
  let : Epi (S.g.f n) := hd.epi_g
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (S.g.f n)).mp inferInstance c
  let a := ((biprod.fst : (singular U).chainComplex R ⊞ (singular V).chainComplex R ⟶
    (singular U).chainComplex R).f n).hom b
  let d := ((biprod.snd : (singular U).chainComplex R ⊞ (singular V).chainComplex R ⟶
    (singular V).chainComplex R).f n).hom b
  have hs : S.g ≫ (SimplicialCoefficients.chains R).map (smallInclusion U V) =
      biprod.desc (RelativeCoefficients.inclusion R U) (RelativeCoefficients.inclusion R V) := by
    change biprod.desc ((SimplicialCoefficients.chains R).map (toSmallLeft U V))
      ((SimplicialCoefficients.chains R).map (toSmallRight U V)) ≫ _ = _
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc_assoc, chainToSmallLeft_inclusion]
      exact (biprod.inl_desc (RelativeCoefficients.inclusion R U)
        (RelativeCoefficients.inclusion R V)).symm
    · simp only [biprod.inr_desc_assoc, chainToSmallRight_inclusion]
      exact (biprod.inr_desc (RelativeCoefficients.inclusion R U)
        (RelativeCoefficients.inclusion R V)).symm
  rw [biprod.desc_eq] at hs
  have he := congrArg (fun m => (m.f n).hom b) hs
  change smallInclusionMap R U V n ((S.g.f n).hom b) =
    ((RelativeCoefficients.inclusion R U).f n).hom a +
      ((RelativeCoefficients.inclusion R V).f n).hom d at he
  exact Submodule.mem_sup.mpr ⟨_, ⟨a, rfl⟩, _, ⟨d, rfl⟩,
    he.symm.trans (congrArg (smallInclusionMap R U V n) hb)⟩

end NoExoticSixSphere.SingularSubcomplex
