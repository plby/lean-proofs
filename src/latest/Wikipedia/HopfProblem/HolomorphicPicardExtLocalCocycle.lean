import Wikipedia.HopfProblem.HolomorphicPicardExtRepresentation
import Wikipedia.HopfProblem.HolomorphicPicardExtIntegerOne
import Wikipedia.HopfProblem.HolomorphicPicardCechAlgebra

/-!
# Actual local cocycles extracted from native sheaf cohomology

A native degree-one sheaf cohomology class is represented by a genuine
extension with quotient the literal constant `ULift ℤ` sheaf.  Local lifts
of its actual integer section `1` give a point-indexed open cover and an
actual difference cocycle.  Negating that cocycle gives the convention
in which its image is the second lift minus the first lift.

This constructs cocycles and the stated equations in the representative
extension.  It does not assume or assert a Čech-to-derived comparison.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)

/-- The actual extension representing a native `H¹` class. Its endpoints
are literally `F` and the constant `ULift ℤ` sheaf used by `Sheaf.H`. -/
abbrev sheafRepresentativeComplex (ξ : CategoryTheory.Sheaf.H.{0} F 1) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  representativeComplex (A := F) (B := constantIntegerSheaf X) ξ

/-- The native sheaf category supplies enough injectives and small Ext;
there are no additional representation or injectivity assumptions. -/
theorem sheafRepresentativeComplex_shortExact (ξ : CategoryTheory.Sheaf.H.{0} F 1) :
    (sheafRepresentativeComplex F ξ).ShortExact :=
  representativeComplex_shortExact ξ

/-- The represented class is the given native sheaf cohomology class. -/
theorem sheafRepresentativeComplex_extClass (ξ : CategoryTheory.Sheaf.H.{0} F 1) :
    (sheafRepresentativeComplex_shortExact F ξ).extClass = ξ :=
  representativeComplex_extClass ξ

/-- Actual local lifts of the literal integer section `1` and their
kernel-valued overlap differences exist for every native `H¹` class. -/
theorem exists_representative_difference_cocycle (ξ : CategoryTheory.Sheaf.H.{0} F 1) :
    ∃ (U : X → Opens X)
      (t : ∀ x, Section (sheafRepresentativeComplex F ξ).X₂ (U x)),
      (∀ x, x ∈ U x) ∧
      (∀ x, (sheafRepresentativeComplex F ξ).g.hom.app (op (U x)) (t x) =
        constantIntegerOne X (U x)) ∧
      ∃ c : CechOneCocycle F U, ∀ i j,
        (sheafRepresentativeComplex F ξ).f.hom.app (op (U i ⊓ U j)) (c.value i j) =
          overlapDifference (sheafRepresentativeComplex F ξ).X₂ U t i j := by
  let S := sheafRepresentativeComplex F ξ
  have hS : S.ShortExact := sheafRepresentativeComplex_shortExact F ξ
  let : Epi S.g := hS.epi_g
  obtain ⟨U, t, hU, ht⟩ := exists_local_lifts S.g (constantIntegerOne X ⊤)
  obtain ⟨c, hc⟩ := exists_difference_cocycle hS U (constantIntegerOne X ⊤) t ht
  refine ⟨U, t, hU, ?_, c, hc⟩
  intro x
  exact (ht x).trans (constantIntegerOne_restrict X le_top)

/-- With the extension-gluing convention, the image of the cocycle is the
second local lift minus the first one.  It is the negative of the actual
overlap-difference cocycle above. -/
theorem exists_representative_cocycle (ξ : CategoryTheory.Sheaf.H.{0} F 1) :
    ∃ (U : X → Opens X)
      (t : ∀ x, Section (sheafRepresentativeComplex F ξ).X₂ (U x)),
      (∀ x, x ∈ U x) ∧
      (∀ x, (sheafRepresentativeComplex F ξ).g.hom.app (op (U x)) (t x) =
        constantIntegerOne X (U x)) ∧
      ∃ c : CechOneCocycle F U, ∀ i j,
        (sheafRepresentativeComplex F ξ).f.hom.app (op (U i ⊓ U j)) (c.value i j) =
          res (sheafRepresentativeComplex F ξ).X₂ inf_le_right (t j) -
            res (sheafRepresentativeComplex F ξ).X₂ inf_le_left (t i) := by
  obtain ⟨U, t, hU, ht, c, hc⟩ := exists_representative_difference_cocycle F ξ
  refine ⟨U, t, hU, ht, -c, ?_⟩
  intro i j
  rw [Cech.neg_value, map_neg, hc, overlapDifference, neg_sub]

end Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions
