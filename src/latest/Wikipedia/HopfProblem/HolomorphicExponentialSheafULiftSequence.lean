import Wikipedia.HopfProblem.HolomorphicExponentialSheafSequence

/-!
# The exponential sequence with the native sheaf-cohomology integer source

Mathlib's sheaf cohomology uses the constant sheaf with value `ULift ℤ`.
The canonical constant-sheaf isomorphism transports the proved exponential
sequence to that literal source. Its integer normalization is retained
on the actual sheafification representatives.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The same genuine integer inclusion with the native lifted source. -/
def integerULiftInclusion :
    (show TopCat.Sheaf AddCommGrpCat (TopCat.of M) from integerULiftSheaf (TopCat.of M)) ⟶
      HolomorphicFunctionSheaf.additiveSheaf I M :=
  (integerSheafULiftIso (TopCat.of M)).inv ≫ integerInclusion I M

theorem integerULiftInclusion_app_unit_apply (U : Opens M) (n : ULift.{0} ℤ) (x : U) :
    (fun f : HolomorphicFunctionSheaf.Section I M U => f x)
      ((integerULiftInclusion I M).hom.app (op U)
        ((integerULiftUnit (TopCat.of M)).app (op U) n)) =
        (n.down : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  change (fun f : HolomorphicFunctionSheaf.Section I M U => f x)
    ((integerInclusion I M).hom.app (op U)
    ((integerSheafULiftIso (TopCat.of M)).inv.hom.app (op U)
      ((integerULiftUnit (TopCat.of M)).app (op U) n))) = _
  rw [integerSheafULiftIso_inv_app_unit, integerInclusion_app_unit_apply]

theorem integerULiftInclusion_exponential :
    integerULiftInclusion I M ≫ exponential I M = 0 := by
  let S := exponentialComplex I M
  let e : S.X₁ ≅
      (show TopCat.Sheaf AddCommGrpCat (TopCat.of M) from integerULiftSheaf (TopCat.of M)) :=
    integerSheafULiftIso (TopCat.of M)
  have h : (e.inv ≫ S.f) ≫ S.g = 0 := by
    rw [Category.assoc, S.zero, comp_zero]
  exact h

/-- The sequence with exactly the native `ULift ℤ` constant sheaf. -/
abbrev exponentialULiftComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of M)) :=
  ShortComplex.mk (integerULiftInclusion I M) (exponential I M)
    (integerULiftInclusion_exponential I M)

/-- The canonical comparison is an actual isomorphism of short complexes. -/
def exponentialComplexULiftIso : exponentialComplex I M ≅ exponentialULiftComplex I M := by
  let S := exponentialComplex I M
  let T := exponentialULiftComplex I M
  let e : S.X₁ ≅ T.X₁ := integerSheafULiftIso (TopCat.of M)
  refine ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) ?_ ?_
  · change e.hom ≫ (e.inv ≫ S.f) = S.f ≫ 𝟙 _
    exact (e.hom_inv_id_assoc S.f).trans (Category.comp_id S.f).symm
  · exact (Category.id_comp S.g).trans (Category.comp_id S.g).symm

/-- Short exactness with the literal constant source used by `Sheaf.H`. -/
theorem exponentialULiftComplex_shortExact : (exponentialULiftComplex I M).ShortExact :=
  ShortComplex.shortExact_of_iso (exponentialComplexULiftIso I M)
    (exponentialComplex_shortExact I M)

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
