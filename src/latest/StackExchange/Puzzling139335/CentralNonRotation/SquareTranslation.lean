import StackExchange.Puzzling139335.CentralNonRotation.FixedImage
import StackExchange.Puzzling139335.CentralNonRotation.SquareTranslationAxis
import StackExchange.Puzzling139335.TranslationCancellation

/-!
# The center exclusion when the congruence squares to a translation

The central conjugation identity is derived from boundedness of the actual
two-piece union. A zero square displacement forces the isometry to fix the
center. A nonzero displacement permits the proved integrable-density
cancellation argument. Thus neither case assumes an axis or centroid relation.
-/

open Set

namespace Puzzling139335.CentralNonRotation

/-- For a centrally symmetric two-piece union with finite common outer
contacts, a congruence whose square is a translation excludes the center
from both piece interiors. -/
theorem not_mem_interiors_of_central_square_translation
    {P : Set Plane} (hP : IsJordanRegion P)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (c v : Plane)
    (hg2 : ∀ x, g (g x) = x + v)
    (hdis : Disjoint (interior P) (interior (g '' P)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' (P ∪ g '' P) = P ∪ g '' P)
    (hcontact : (P ∩ g '' P ∩ frontier (P ∪ g '' P)).Finite) :
    c ∉ interior P ∧ c ∉ interior (g '' P) := by
  by_cases hv : v = 0
  · have hdisp := square_translation_eq_twice_displacement g c v hg2
      hP.isCompact hP.nonempty hsym
    have hfix : g c = c := by
      ext i
      have hi := congrArg (fun p : Plane => p i) hdisp
      rw [hv] at hi
      change 0 = ((g c) i - c i) + ((g c) i - c i) at hi
      linarith
    exact not_mem_interiors_of_fixed P g hfix hdis
  · let h := AffineIsometryEquiv.pointReflection ℝ c
    have hconj : ∀ x, h (g (h x)) = g.symm x :=
      pointReflection_conjugate_eq_symm_of_square_translation g c v hg2
        hP.isCompact hP.nonempty hsym
    have himage : g '' P = h '' P :=
      hP.image_eq_of_dihedral_union_symmetry_of_finite g h hv hg2
        (AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) c)
        hconj hdis hsym hcontact
    have hdis' : Disjoint (interior P) (interior (h '' P)) := by
      rwa [← himage]
    have hnot := not_mem_interiors_of_fixed P h
      (AffineIsometryEquiv.pointReflection_self (𝕜 := ℝ) c) hdis'
    rwa [← himage] at hnot

end Puzzling139335.CentralNonRotation
