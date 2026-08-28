import Wikipedia.NoExoticSixSphere.EmptySupportedHomology
import Wikipedia.NoExoticSixSphere.ModTwoDualBiproduct
import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology

/-!
# The actual mod-two cohomology of empty support vanishes

The original whole-subspace inclusion is an isomorphism. Its actual
relative chain cokernel is zero, and the original additive dual and
cohomology functors preserve this zero object. The ambient space is
arbitrary; only the support is empty.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable (X : Type) [TopologicalSpace X]

/-- Empty support has the original zero relative cochain complex. -/
theorem complex_empty_isZero : IsZero (complex (∅ : Set X)) :=
  ModTwoDualComplex.cochainDualFunctor.map_isZero
    (SupportedRelativeHomology.complex_empty_isZero (M := X) (ModuleCat.of ℤ ℤ)).op

/-- Actual cohomology with empty support is zero in every degree. -/
theorem cohomology_empty_subsingleton (p : ℕ) : Subsingleton (Cohomology (∅ : Set X) p) :=
  ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) p).map_isZero
      (complex_empty_isZero X))

theorem cohomology_empty_eq_zero (p : ℕ) (a : Cohomology (∅ : Set X) p) : a = 0 :=
  (cohomology_empty_subsingleton X p).elim a 0

end NoExoticSixSphere.SupportedModTwoCohomology
