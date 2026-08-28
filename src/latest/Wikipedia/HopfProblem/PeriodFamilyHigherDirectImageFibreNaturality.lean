import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreNaturalityCocone
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreStalk
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageStalkNaturalityStalk

/-!
# The actual derived-stalk-to-fibre map is coefficient-natural

The original right-derived coefficient map, original stalk comparison,
and original finite closed-fibre restriction give the same commuting
coefficient square in every cohomological degree. The source map is
the native right-derived map, not a map defined by transport through
the stalk comparison.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood

open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X Y : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)
  {F F' : AbelianSheaf X} {G G' : AbelianSheaf T}
  (κ : F ⟶ (pushforward i).obj G) (κ' : F' ⟶ (pushforward i).obj G')
  (a : F ⟶ F') (b : G ⟶ G')
  (hsq : a ≫ κ' = κ ≫ (pushforward i).map b)
  (f : X ⟶ Y) (y : Y) (hfi : ∀ t : T, f (i t) = y)

include hsq

/-- The genuine all-degree evaluation map intertwines the native
right-derived coefficient map with the original fibre cohomology map. -/
theorem derivedStalkEvaluation_naturality (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
        (((SheafHigherDirectImage.functor f n).map a).hom) ≫
      derivedStalkEvaluation i hi hfinite κ' f y hfi n =
    derivedStalkEvaluation i hi hfinite κ f y hfi n ≫
      AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map b n) := by
  let eF := SheafHigherDirectImage.stalkCohomologyPresheafIso f F n y
  let eF' := SheafHigherDirectImage.stalkCohomologyPresheafIso f F' n y
  let d := (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
    (((SheafHigherDirectImage.functor f n).map a).hom)
  let p := (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (sourceCohomologyMap f a n)
  let v := presheafStalkEvaluation i hi hfinite κ f y hfi n
  let v' := presheafStalkEvaluation i hi hfinite κ' f y hfi n
  let h := AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map b n)
  have hc : d ≫ eF'.hom = eF.hom ≫ p :=
    StalkNaturality.stalkCohomologyPresheafIso_hom_naturality f a n y
  have hv : p ≫ v' = v ≫ h :=
    presheafStalkEvaluation_naturality i hi hfinite κ κ' a b hsq f y hfi n
  change d ≫ (eF'.hom ≫ v') = (eF.hom ≫ v) ≫ h
  exact (Category.assoc d eF'.hom v').symm.trans
    ((congrArg (fun k => k ≫ v') hc).trans
      ((Category.assoc eF.hom p v').trans
        ((congrArg (fun k => eF.hom ≫ k) hv).trans
          (Category.assoc eF.hom v h).symm)))

/-- The same genuine coefficient naturality on every actual stalk
element, without requiring a chosen neighborhood or global representative. -/
theorem derivedStalkEvaluation_naturality_apply (n : ℕ)
    (x : ↥(derivedStalk (F := F) f y n)) :
    derivedStalkEvaluation i hi hfinite κ' f y hfi n
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
          (((SheafHigherDirectImage.functor f n).map a).hom) x) =
      CategoryTheory.Sheaf.H.map b n (derivedStalkEvaluation i hi hfinite κ f y hfi n x) :=
  ConcreteCategory.congr_hom
    (derivedStalkEvaluation_naturality i hi hfinite κ κ' a b hsq f y hfi n) x

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood
