import Wikipedia.NoExoticSixSphere.SubcomplexChainRange
import Wikipedia.NoExoticSixSphere.SingularSmallSubcomplex

/-!
# Support intersections for the original singular coefficient chains

The actual subspace chain inclusion has the same image as the inclusion
of its singular range subcomplex. Consequently, intersections of the
original subspace-chain images are the image of the intersection.
No openness, covering, or homological injectivity is assumed.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ)

/-- Passing to the range subcomplex retains the original subspace-chain image. -/
theorem chainImage_support (U : Set X) (n : ℕ) :
    SimplicialCoefficients.chainImage R (support U) n =
      LinearMap.range ((RelativeCoefficients.inclusion R U).f n).hom := by
  let f := (SimplicialCoefficients.chains R).map (supportIso U).hom
  have he : f ≫ (SimplicialCoefficients.chains R).map (support U).ι =
      RelativeCoefficients.inclusion R U := by
    dsimp [f]
    rw [← Functor.map_comp, supportIso_hom_inclusion]
    rfl
  apply le_antisymm
  · rintro c ⟨b, hb⟩
    obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective (f.f n)).mp inferInstance b
    refine ⟨a, ?_⟩
    exact (congrArg (fun m => (m.f n).hom a) he).symm.trans
      ((congrArg (SimplicialCoefficients.inclusionMap R (support U) n).hom ha).trans hb)
  · rintro c ⟨a, ha⟩
    exact ⟨(f.f n).hom a, (congrArg (fun m => (m.f n).hom a) he).trans ha⟩

/-- A chain supported in both actual subspaces comes from their actual intersection. -/
theorem inclusion_range_inter (U V : Set X) (n : ℕ) :
    LinearMap.range ((RelativeCoefficients.inclusion R (U ∩ V)).f n).hom =
      LinearMap.range ((RelativeCoefficients.inclusion R U).f n).hom ⊓
        LinearMap.range ((RelativeCoefficients.inclusion R V).f n).hom := by
  rw [← chainImage_support, support_inter, SimplicialCoefficients.chainImage_inf,
    chainImage_support, chainImage_support]
  rfl

/-- Original small-chain images are exactly the sum of the two subspace images. -/
theorem smallInclusion_range (U V : Set X) (n : ℕ) :
    LinearMap.range
        (((SimplicialCoefficients.chains R).map (smallInclusion U V)).f n).hom =
      LinearMap.range ((RelativeCoefficients.inclusion R U).f n).hom ⊔
        LinearMap.range ((RelativeCoefficients.inclusion R V).f n).hom := by
  exact (SimplicialCoefficients.chainImage_sup R (support U) (support V) n).trans
    (congrArg₂ (fun A B => A ⊔ B) (chainImage_support R U n) (chainImage_support R V n))

end NoExoticSixSphere.SingularSubcomplex
