import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClass
import Wikipedia.HopfProblem.HolomorphicPicardExtEquivalence

/-!
# Equal genuine Čech extension classes give actual extension isomorphisms

The extensions are the constructed sheafifications of the literal cocycle
data.  Equality of their native degree-one cohomology classes gives an
actual middle-object isomorphism fixing the original kernel sheaf and
the literal constant-integer quotient.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechClassInjectivity

open HolomorphicFunctionSheaf.SphereH1 CechExtension

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c d : CechOneCocycle F U)
  (hU : ∀ x : X, ∃ i : ι, x ∈ U i)

/-- The actual cohomology equality produces a genuine isomorphism of the
constructed extension sheaves, respecting both original arrows. -/
theorem exists_extension_iso_of_classOf_eq
    (h : CechExtension.classOf c hU = CechExtension.classOf d hU) :
    ∃ e : extensionSheaf c ≅ extensionSheaf d,
      inclusion c ≫ e.hom = inclusion d ∧ e.hom ≫ projection d = projection c := by
  change (complex_shortExact c hU).extClass = (complex_shortExact d hU).extClass at h
  exact ExtExtensions.exists_middle_iso_of_extClass_eq
    (complex_shortExact c hU) (complex_shortExact d hU) h

end Wikipedia.HopfProblem.HolomorphicPicard.CechClassInjectivity
