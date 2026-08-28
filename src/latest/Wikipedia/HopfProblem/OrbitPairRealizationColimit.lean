import Wikipedia.HopfProblem.OrbitPairRealizationSimplex
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# The actual realization as a colimit of geometric simplices

The existing left Kan extension is pointwise. Its native colimit legs are
identified with the characteristic maps defined through the adjunction
unit. Thus the characteristic simplices jointly cover the realization and
detect its topology, not only an auxiliary space.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable (S : SSet.{u})

local instance : Category.{0} (CostructuredArrow SSet.stdSimplex.{u} S) :=
  inferInstanceAs (Category.{0} (CostructuredArrow uliftYoneda.{u} S))

def simplexCocone :
    Cocone (CostructuredArrow.proj SSet.stdSimplex.{u} S ⋙ SimplexCategory.toTop.{u}) :=
  (Functor.LeftExtension.mk SSet.toTop.{u} SSet.toTopSimplex.inv).coconeAt S

def isColimitSimplexCocone : IsColimit (simplexCocone S) := by
  letI : Functor.HasPointwiseLeftKanExtension SSet.stdSimplex.{u} SimplexCategory.toTop.{u} :=
    inferInstanceAs
      (Functor.HasPointwiseLeftKanExtension uliftYoneda.{u} SimplexCategory.toTop.{u})
  exact Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    SSet.toTop SSet.toTopSimplex.inv S

theorem characteristic_eq_cocone_leg
    (a : CostructuredArrow SSet.stdSimplex.{u} S) (t : SimplexCategory.toTop.{u}.obj a.left) :
    characteristic S a.left.len (SSet.yonedaEquiv a.hom) t.down =
      (simplexCocone S).ι.app a t := by
  have h :
      ((sSetTopAdj.unit.app S).app (Opposite.op a.left) (SSet.yonedaEquiv a.hom)).down =
        (simplexCocone S).ι.app a := by
    rw [sSetTopAdj_unit_app_app_down, Equiv.symm_apply_apply]
    rfl
  exact ConcreteCategory.congr_hom h t

theorem exists_characteristic (y : SSet.toTop.obj S) :
    ∃ (n : ℕ) (x : S _⦋n⦌) (t : Simplex n), characteristic S n x t = y := by
  obtain ⟨a, t, ht⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (isColimitSimplexCocone S)) y
  exact ⟨a.left.len, SSet.yonedaEquiv a.hom, t.down,
    (characteristic_eq_cocone_leg S a t).trans ht⟩

theorem continuous_iff_characteristic {Y : Type*} [TopologicalSpace Y]
    (f : SSet.toTop.obj S → Y) :
    Continuous f ↔ ∀ (n : ℕ) (x : S _⦋n⦌), Continuous (f ∘ characteristic S n x) := by
  constructor
  · intro hf n x
    exact hf.comp (characteristic S n x).continuous
  · intro hf
    apply (TopCat.continuous_iff_of_isColimit (simplexCocone S)
      (isColimitSimplexCocone S) f).mpr
    intro a
    have h := (hf a.left.len (SSet.yonedaEquiv a.hom)).comp continuous_uliftDown
    exact h.congr (fun t ↦ congrArg f (characteristic_eq_cocone_leg S a t))

theorem isOpen_iff_characteristic (U : Set (SSet.toTop.obj S)) :
    IsOpen U ↔ ∀ (n : ℕ) (x : S _⦋n⦌), IsOpen (characteristic S n x ⁻¹' U) := by
  constructor
  · intro hU n x
    exact hU.preimage (characteristic S n x).continuous
  · intro hU
    apply (TopCat.isOpen_iff_of_isColimit (simplexCocone S)
      (isColimitSimplexCocone S) U).mpr
    intro a
    have he :
        (fun t : SimplexCategory.toTop.{u}.obj a.left ↦
          characteristic S a.left.len (SSet.yonedaEquiv a.hom) t.down) =
          (simplexCocone S).ι.app a :=
      funext (characteristic_eq_cocone_leg S a)
    rw [← he]
    exact (hU a.left.len (SSet.yonedaEquiv a.hom)).preimage continuous_uliftDown

theorem isClosed_iff_characteristic (U : Set (SSet.toTop.obj S)) :
    IsClosed U ↔ ∀ (n : ℕ) (x : S _⦋n⦌), IsClosed (characteristic S n x ⁻¹' U) := by
  simp only [← isOpen_compl_iff, isOpen_iff_characteristic, Set.preimage_compl]

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
