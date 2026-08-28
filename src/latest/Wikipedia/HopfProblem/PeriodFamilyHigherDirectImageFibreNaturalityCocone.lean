import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreNaturalityBasic
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreStalkCocone

/-!
# Coefficient naturality of the genuine cohomology-presheaf stalk evaluation

The original coefficient maps induce the usual maps on the actual
inverse-image cohomology presheaves. The proved neighborhood fibre
restriction square then descends through the original stalk colimit.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood

open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} {F F' : AbelianSheaf X}

/-- The original coefficient map on the actual full-preimage cohomology presheaves. -/
abbrev sourceCohomologyMap (f : X ⟶ Y) (a : F ⟶ F') (n : ℕ) :
    sourceCohomologyPresheaf (F := F) f n ⟶
      sourceCohomologyPresheaf (F := F') f n :=
  Functor.whiskerLeft (Opens.map f).op
    ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) n).map a)

variable {T : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)
  {G G' : AbelianSheaf T}
  (κ : F ⟶ (pushforward i).obj G) (κ' : F' ⟶ (pushforward i).obj G')
  (a : F ⟶ F') (b : G ⟶ G')
  (hsq : a ≫ κ' = κ ≫ (pushforward i).map b)
  (f : X ⟶ Y) (y : Y) (hfi : ∀ t : T, f (i t) = y)

include hsq

/-- The genuine cohomology-presheaf stalk-to-fibre map preserves every
original coefficient square in all cohomological degrees. -/
theorem presheafStalkEvaluation_naturality (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map (sourceCohomologyMap f a n) ≫
      presheafStalkEvaluation i hi hfinite κ' f y hfi n =
    presheafStalkEvaluation i hi hfinite κ f y hfi n ≫
      AddCommGrpCat.ofHom (CategoryTheory.Sheaf.H.map b n) := by
  apply TopCat.Presheaf.stalk_hom_ext (sourceCohomologyPresheaf (F := F) f n)
  intro U hy
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact (congrArg (presheafStalkEvaluation i hi hfinite κ' f y hfi n)
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy (sourceCohomologyMap f a n) x)).trans
      ((presheafStalkEvaluation_germ_apply i hi hfinite κ' f y hfi n U hy
        ((sourceCohomologyMap f a n).app (op U) x)).trans
          ((cohomologyEvaluation_naturality i κ κ' a b hsq hi hfinite
            ((Opens.map f).obj U) (fibre_mem_preimage i f y hfi U hy) n x).trans
              (congrArg (CategoryTheory.Sheaf.H.map b n)
                (presheafStalkEvaluation_germ_apply i hi hfinite κ f y hfi n U hy x)).symm))

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood
