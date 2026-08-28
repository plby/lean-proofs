import Wikipedia.HopfProblem.SheafLerayLowDegreesBasic
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Transport of actual low-degree exact complexes

These elementary categorical comparisons retain all three morphisms
when the native Ext and resolution-homology groups are identified with
the corresponding genuine sheaf-cohomology groups.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

variable (S : ShortComplex AddCommGrpCat.{0}) {A B C : AddCommGrpCat.{0}}
  (e₁ : S.X₁ ≅ A) (e₂ : S.X₂ ≅ B) (e₃ : S.X₃ ≅ C)

/-- Transport a genuine complex along given isomorphisms of its terms. -/
def transportComplex : ShortComplex AddCommGrpCat.{0} :=
  ShortComplex.mk (e₁.inv ≫ S.f ≫ e₂.hom) (e₂.inv ≫ S.g ≫ e₃.hom) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, S.zero_assoc, zero_comp, comp_zero])

/-- The term isomorphisms identify the actual differentials. -/
def transportComplexIso : S ≅ transportComplex S e₁ e₂ e₃ :=
  ShortComplex.isoMk e₁ e₂ e₃
    (by simp only [transportComplex, Iso.hom_inv_id_assoc])
    (by simp only [transportComplex, Iso.hom_inv_id_assoc])

/-- Exactness is unchanged by the canonical term comparisons. -/
theorem transportComplex_exact (hS : S.Exact) : (transportComplex S e₁ e₂ e₃).Exact :=
  ShortComplex.exact_of_iso (transportComplexIso S e₁ e₂ e₃) hS

/-- A monomorphic first map remains monomorphic under these comparisons. -/
instance transportComplex_f_mono [Mono S.f] : Mono (transportComplex S e₁ e₂ e₃).f := by
  change Mono (e₁.inv ≫ S.f ≫ e₂.hom)
  infer_instance

end Wikipedia.HopfProblem.SheafLerayLowDegrees
