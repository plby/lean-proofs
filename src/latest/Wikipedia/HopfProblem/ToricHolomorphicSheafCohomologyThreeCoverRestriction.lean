import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverNaturality

/-!
# Identities and cancellations for actual open restrictions

All maps are literal maps of the original section or cohomology presheaf.
Mutual open inclusions give inverse restrictions; these facts handle the
distributive-lattice equalities in the two Mayer--Vietoris squares.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)

theorem sectionRestrict_id (A : Opens X) (s : Sections F A) :
    sectionRestrict F (le_refl A) s = s := by
  change F.obj.map (𝟙 (op A)) s = s
  exact ConcreteCategory.congr_hom (F.obj.map_id (op A)) s

theorem sectionRestrict_inverse {A B : Opens X} (hAB : A ≤ B) (hBA : B ≤ A)
    (s : Sections F A) : sectionRestrict F hAB (sectionRestrict F hBA s) = s :=
  Eq.trans (sectionRestrict_comp F hAB hBA s) (sectionRestrict_id F A s)

theorem cohomologyRestrict_id (n : ℕ) (A : Opens X)
    (a : CategoryTheory.Sheaf.H'.{0} F n A) : cohomologyRestrict F n (le_refl A) a = a := by
  change (F.cohomologyPresheaf n).map (𝟙 (op A)) a = a
  exact ConcreteCategory.congr_hom ((F.cohomologyPresheaf n).map_id (op A)) a

theorem cohomologyRestrict_inverse (n : ℕ) {A B : Opens X}
    (hAB : A ≤ B) (hBA : B ≤ A) (a : CategoryTheory.Sheaf.H'.{0} F n A) :
    cohomologyRestrict F n hAB (cohomologyRestrict F n hBA a) = a :=
  Eq.trans (cohomologyRestrict_comp F n hAB hBA a) (cohomologyRestrict_id F n A a)

theorem cohomologyRestrict_injective_of_mutual (n : ℕ) {A B : Opens X}
    (hAB : A ≤ B) (hBA : B ≤ A) : Function.Injective (cohomologyRestrict F n hAB) := by
  intro a b h
  exact Eq.trans (cohomologyRestrict_inverse F n hBA hAB a).symm
    (Eq.trans (congrArg (cohomologyRestrict F n hBA) h)
      (cohomologyRestrict_inverse F n hBA hAB b))

theorem cohomologyRestrict_surjective_of_mutual (n : ℕ) {A B : Opens X}
    (hAB : A ≤ B) (hBA : B ≤ A) : Function.Surjective (cohomologyRestrict F n hAB) := by
  intro a
  exact ⟨cohomologyRestrict F n hBA a, cohomologyRestrict_inverse F n hAB hBA a⟩

theorem cohomologyRestrict_injective_of_composite (n : ℕ) {A B C : Opens X}
    (hAB : A ≤ B) (hBC : B ≤ C)
    (h : Function.Injective (cohomologyRestrict F n (hAB.trans hBC))) :
    Function.Injective (cohomologyRestrict F n hBC) := by
  intro a b hab
  apply h
  exact Eq.trans (cohomologyRestrict_comp F n hAB hBC a).symm
    (Eq.trans (congrArg (cohomologyRestrict F n hAB) hab)
      (cohomologyRestrict_comp F n hAB hBC b))

theorem cohomologyRestrict_surjective_of_composite (n : ℕ) {A B C : Opens X}
    (hAB : A ≤ B) (hBA : B ≤ A) (hBC : B ≤ C)
    (h : Function.Surjective (cohomologyRestrict F n (hAB.trans hBC))) :
    Function.Surjective (cohomologyRestrict F n hBC) := by
  intro b
  obtain ⟨c, hc⟩ := h (cohomologyRestrict F n hAB b)
  refine ⟨c, ?_⟩
  apply cohomologyRestrict_injective_of_mutual F n hAB hBA
  exact Eq.trans (cohomologyRestrict_comp F n hAB hBC c) hc

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
