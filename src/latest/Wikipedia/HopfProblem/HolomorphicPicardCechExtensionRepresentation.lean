import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionComparisonMaps
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClass
import Wikipedia.HopfProblem.HolomorphicPicardExtLocalCocycle
import Wikipedia.HopfProblem.HolomorphicPicardExtEquivalence

/-!
# Every genuine first sheaf-cohomology class comes from an actual cocycle

The actual derived-category class is represented by a genuine extension.
Its epimorphism supplies local lifts of the literal integer one. Their
sign-corrected differences give an actual cocycle on a point-indexed
cover. The independently constructed extension comparison fixes both
endpoints, so its genuine extension class is precisely the given class.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}}

/-- Every actual `Sheaf.H F 1` class is the constructed extension class
of a literal Čech cocycle on a genuine open cover. No representability,
local splitting, or comparison hypothesis is imposed. -/
theorem exists_classOf_eq (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (ξ : CategoryTheory.Sheaf.H.{0} F 1) :
    ∃ (U : X → Opens X) (hU : ∀ x : X, ∃ i : X, x ∈ U i)
      (c : CechOneCocycle F U), classOf c hU = ξ := by
  obtain ⟨U, t, hmem, ht, c, hc⟩ := ExtExtensions.exists_representative_cocycle F ξ
  let hU : ∀ x : X, ∃ i : X, x ∈ U i := fun x => ⟨x, hmem x⟩
  let S := ExtExtensions.sheafRepresentativeComplex F ξ
  have hS : S.ShortExact := ExtExtensions.sheafRepresentativeComplex_shortExact F ξ
  have hdiff : ∀ i j : X,
      res S.X₂ inf_le_right (t j) - res S.X₂ inf_le_left (t i) =
        S.f.hom.app (op (U i ⊓ U j)) (c.value i j) := fun i j => (hc i j).symm
  let m := comparison c hU S.f t hdiff
  have hi : inclusion c ≫ m = S.f := inclusion_comparison c hU S.f t hdiff
  have hp : m ≫ S.g = projection c :=
    comparison_projection c hU S.f S.g S.zero t ht hdiff
  have hclass : classOf c hU = hS.extClass :=
    ExtExtensions.extClass_eq_of_middle_map (complex_shortExact c hU) hS m hi hp
  exact ⟨U, hU, c, hclass.trans (ExtExtensions.sheafRepresentativeComplex_extClass F ξ)⟩

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
