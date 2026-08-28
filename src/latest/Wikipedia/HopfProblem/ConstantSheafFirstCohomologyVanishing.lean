import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyExtensionGlobal
import Wikipedia.HopfProblem.HolomorphicPicardExtRepresentation
import Wikipedia.HopfProblem.HolomorphicPicardExtSplit
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ExtGlobal

/-!
# Genuine first cohomology of a constant sheaf on a simply connected space

Every native degree-one Ext class is represented by an actual short exact
sequence ending in Mathlib's constant lifted-integer sheaf. The proved
covering-space continuation lifts its global sections. The native
degree-zero comparison turns this into a section of the epimorphism, so
the actual extension class is zero.

No identification with singular cohomology, acyclicity assumption, or
assumed classification of local systems occurs in this argument.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]

/-- The actual Mathlib degree-one sheaf cohomology class of a native
constant additive sheaf is zero on a simply connected, locally
path-connected space. The coefficient group is arbitrary. -/
theorem native_h1_eq_zero (A : AddCommGrpCat.{0})
    (ξ : CategoryTheory.Sheaf.H.{0} (Constant.sheaf X A) 1) : ξ = 0 := by
  obtain ⟨E, ι, π, hzero, hS, hξ⟩ :=
    HolomorphicPicard.ExtExtensions.exists_shortExact_extClass
      (A := Constant.sheaf X A)
      (B := Constant.sheaf X (AddCommGrpCat.of (ULift.{0} ℤ))) ξ
  have hglobal := Extension.integer_global_sections_surjective A ι π hzero hS
  obtain ⟨s, hs⟩ := hom_surjective_of_global_surjective π hglobal (𝟙 _)
  rw [← hξ]
  exact (HolomorphicPicard.ExtExtensions.extClass_eq_zero_iff_exists_section hS).mpr ⟨s, hs⟩

/-- Vanishing for the literal native constant sheaf and the original Ext
definition of first sheaf cohomology. -/
theorem native_h1_subsingleton (A : AddCommGrpCat.{0}) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (Constant.sheaf X A) 1) :=
  subsingleton_of_forall_eq 0 (native_h1_eq_zero A)

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology
