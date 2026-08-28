import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# The original empty-support relative groups vanish

The inclusion of the whole space is induced by its actual subtype
homeomorphism, so its native singular-chain map is an isomorphism. Its
cokernel and all homology groups are zero, for any coefficient module.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M] (A : ModuleCat.{0} ℤ)

theorem inclusion_univ_isIso : IsIso (RelativeCoefficients.inclusion A (Set.univ : Set M)) := by
  have : IsIso (TopCat.ofHom
      (Wikipedia.HopfProblem.SingularMayerVietoris.subtypeInclusion (Set.univ : Set M))) :=
    inferInstanceAs (IsIso (TopCat.isoOfHomeo
      (X := TopCat.of (Set.univ : Set M)) (Y := TopCat.of M) (Homeomorph.Set.univ M)).hom)
  exact inferInstanceAs
    (IsIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj A).map
      (TopCat.ofHom
        (Wikipedia.HopfProblem.SingularMayerVietoris.subtypeInclusion (Set.univ : Set M)))))

theorem complex_empty_isZero : IsZero (Complex A (∅ : Set M)) := by
  have : IsIso (RelativeCoefficients.inclusion A (Set.univ : Set M)) := inclusion_univ_isIso A
  have h : IsZero (RelativeCoefficients.complex A (Set.univ : Set M)) :=
    isZero_cokernel_of_epi (RelativeCoefficients.inclusion A (Set.univ : Set M))
  change IsZero (RelativeCoefficients.complex A ((∅ : Set M)ᶜ))
  rw [Set.compl_empty]
  exact h

/-- Empty-support vanishing is for the original relative complex and arbitrary coefficients. -/
theorem homology_empty_subsingleton (n : ℕ) : Subsingleton (Homology A (∅ : Set M) n) :=
  ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map_isZero
      (complex_empty_isZero A))

end NoExoticSixSphere.SupportedRelativeHomology
