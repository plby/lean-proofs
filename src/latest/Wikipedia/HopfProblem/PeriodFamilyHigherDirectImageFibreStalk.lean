import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreStalkCocone

/-!
# The genuine higher-direct-image stalk-to-fibre map

The native right-derived sheaf pushforward has already been compared
with its actual neighborhood cohomology presheaf. Composing that proved
stalk comparison with the genuine closed-fibre restriction constructs
the usual additive map from the actual higher-direct-image stalk to
the original fibre's Ext cohomology. No base-change bijectivity or
dimension hypothesis is supplied.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood

open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X Y : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)
  {F : AbelianSheaf X} {G : AbelianSheaf T} (κ : F ⟶ (pushforward i).obj G)
  (f : X ⟶ Y) (y : Y) (hfi : ∀ t : T, f (i t) = y)

/-- The actual stalk of the genuine right-derived pushforward. -/
abbrev derivedStalk (n : ℕ) : AddCommGrpCat.{0} :=
  TopCat.Presheaf.stalk (SheafHigherDirectImage.sheaf f F n).obj y

/-- The genuine stalk-to-fibre cohomology map in every degree. -/
def derivedStalkEvaluation (n : ℕ) :
    derivedStalk (F := F) f y n ⟶ AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} G n) :=
  (SheafHigherDirectImage.stalkCohomologyPresheafIso f F n y).hom ≫
    presheafStalkEvaluation i hi hfinite κ f y hfi n

/-- An original neighborhood class gives a class in the actual higher-direct-image stalk. -/
def derivedNeighborhoodGerm (n : ℕ) (U : Opens Y) (hy : y ∈ U) :
    CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U) ⟶
      derivedStalk (F := F) f y n :=
  TopCat.Presheaf.germ (sourceCohomologyPresheaf (F := F) f n) U y hy ≫
    (SheafHigherDirectImage.stalkCohomologyPresheafIso f F n y).inv

/-- The actual derived-stalk map retains the original representative's fibre restriction. -/
theorem derivedStalkEvaluation_germ (n : ℕ) (U : Opens Y) (hy : y ∈ U) :
    derivedNeighborhoodGerm (F := F) f y n U hy ≫
      derivedStalkEvaluation i hi hfinite κ f y hfi n =
        AddCommGrpCat.ofHom
          (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
            (fibre_mem_preimage i f y hfi U hy) n) := by
  change (TopCat.Presheaf.germ (sourceCohomologyPresheaf (F := F) f n) U y hy ≫
      (SheafHigherDirectImage.stalkCohomologyPresheafIso f F n y).inv) ≫
    ((SheafHigherDirectImage.stalkCohomologyPresheafIso f F n y).hom ≫
      presheafStalkEvaluation i hi hfinite κ f y hfi n) = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact presheafStalkEvaluation_germ i hi hfinite κ f y hfi n U hy

theorem derivedStalkEvaluation_germ_apply (n : ℕ) (U : Opens Y) (hy : y ∈ U)
    (a : CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U)) :
    derivedStalkEvaluation i hi hfinite κ f y hfi n
      (derivedNeighborhoodGerm (F := F) f y n U hy a) =
        cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
          (fibre_mem_preimage i f y hfi U hy) n a :=
  ConcreteCategory.congr_hom
    (derivedStalkEvaluation_germ i hi hfinite κ f y hfi n U hy) a

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood
