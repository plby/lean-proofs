import Wikipedia.NoExoticSixSphere.CoefficientChainPresentation
import Wikipedia.NoExoticSixSphere.RelativeCoefficientPairMaps

/-!
# Compact carriers for the native coefficient chains

A finite simplex presentation is carried by the finite union of the
images of its simplices. Each such image is compact, and the original
chain is the image of a chain on that actual compact subspace.
-/

noncomputable section

open CategoryTheory Set
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.CoefficientChains

variable (A : ModuleCat.{0} ℤ) (X : Type) [TopologicalSpace X] (n : ℕ)

/-- Every actual singular coefficient chain comes from a compact subspace. -/
theorem exists_compactCarrier (c : Chains A X n) :
    ∃ K : Set X, IsCompact K ∧ ∃ d : Chains A K n,
      ((RelativeCoefficients.inclusion A K).f n).hom d = c := by
  classical
  obtain ⟨f, rfl⟩ := fromFinsupp_surjective A X n c
  let K : Set X := ⋃ σ ∈ f.support, range σ
  have hK : IsCompact K := f.support.isCompact_biUnion
    (fun σ _ => isCompact_range σ.continuous)
  have hσ (σ : SingularSimplex X n) (h : σ ∈ f.support) : range σ ⊆ K :=
    fun _ hx => mem_iUnion₂.mpr ⟨σ, h, hx⟩
  let term (σ : SingularSimplex X n) : Chains A K n :=
    if h : range σ ⊆ K then simplex A K n (restrictSimplex K n σ h) (f σ) else 0
  refine ⟨K, hK, ∑ σ ∈ f.support, term σ, ?_⟩
  rw [map_sum]
  change ∑ σ ∈ f.support, ((RelativeCoefficients.inclusion A K).f n).hom (term σ) =
    ∑ σ ∈ f.support, simplex A X n σ (f σ)
  apply Finset.sum_congr rfl
  intro σ h
  dsimp only [term]
  rw [dif_pos (hσ σ h)]
  rw [spaceMap_simplex, subtypeInclusion_comp_restrictSimplex]

end NoExoticSixSphere.CoefficientChains
