import Wikipedia.HopfProblem.HolomorphicPicardCechClassInjectivityBasic
import Wikipedia.HopfProblem.HolomorphicPicardCechClassInjectivityLocal
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSplittingLocal
import Wikipedia.HopfProblem.HolomorphicPicardCechCoboundaryClass

/-!
# Equality of actual cohomology classes detects same-cover coboundaries

An actual isomorphism of the cocycle extensions compares their explicit
local degree-one lifts.  Their differences lift through the original
kernel sheaf and give an actual zero-cochain solving `c - d`.  Conversely,
the constructed change-of-splitting map preserves the genuine Ext class.
This proof does not use additivity of the Čech-to-derived class map.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechClassInjectivity

open HolomorphicFunctionSheaf.SphereH1 CechExtension

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c d : CechOneCocycle F U)
  (hU : ∀ x : X, ∃ i : ι, x ∈ U i)

/-- Equal native cohomology classes on the same cover differ by the
coboundary of actual local sections of the original sheaf. -/
theorem solvable_sub_of_classOf_eq
    (h : CechExtension.classOf c hU = CechExtension.classOf d hU) :
    (c - d).Solvable := by
  obtain ⟨e, hi, hp⟩ := exists_extension_iso_of_classOf_eq c d hU h
  exact solvable_sub_of_middle_map c d
    (inclusion c) (projection c) (inclusion d) (projection d)
    (inclusion_projection d) (complex_shortExact d hU)
    e.hom hi hp (localDegreeOneSection c) (localDegreeOneSection d)
    (fun i => (projection_localDegreeOneSection c i).trans
      (projection_localDegreeOneSection d i).symm)
    (localDegreeOneSection_difference c) (localDegreeOneSection_difference d)

/-- Equality in genuine sheaf `H¹` is exactly the actual coboundary
relation on cocycles on this fixed open cover. -/
theorem classOf_eq_iff_solvable_sub :
    CechExtension.classOf c hU = CechExtension.classOf d hU ↔ (c - d).Solvable :=
  ⟨solvable_sub_of_classOf_eq c d hU,
    CechExtension.classOf_eq_of_solvable_sub c d hU⟩

/-- The native class map identifies precisely the same pairs as the
actual cover-cohomology quotient, without assuming a comparison theorem. -/
theorem classOf_eq_iff_coverClass_eq :
    CechExtension.classOf c hU = CechExtension.classOf d hU ↔
      Cech.classOf F U c = Cech.classOf F U d :=
  (classOf_eq_iff_solvable_sub c d hU).trans
    (Cech.class_eq_class_iff F U c d).symm

end Wikipedia.HopfProblem.HolomorphicPicard.CechClassInjectivity
