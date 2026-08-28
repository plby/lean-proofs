import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreEvaluation
import Wikipedia.HopfProblem.SheafHigherDirectImageStalk

/-!
# Actual neighborhood fibre restrictions define a stalk map

All inverse images of neighborhoods of the given base point contain
the entire fibre. The original Ext restriction maps form a genuine
cocone, so they induce an additive map out of the actual cohomology-
presheaf stalk. This is a map, not a base-change isomorphism assertion.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood

open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X Y : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)
  {F : AbelianSheaf X} {G : AbelianSheaf T} (κ : F ⟶ (pushforward i).obj G)
  (f : X ⟶ Y) (y : Y) (hfi : ∀ t : T, f (i t) = y)

/-- The actual base cohomology presheaf evaluated on full inverse-image opens. -/
abbrev sourceCohomologyPresheaf (n : ℕ) : TopCat.Presheaf AddCommGrpCat.{0} Y :=
  (Opens.map f).op ⋙ CategoryTheory.Sheaf.cohomologyPresheaf F n

omit [T2Space T] in
include hfi in
/-- Every actual inverse-image neighborhood contains the entire original fibre. -/
theorem fibre_mem_preimage (U : Opens Y) (hy : y ∈ U) (t : T) :
    i t ∈ (Opens.map f).obj U := by
  change f (i t) ∈ U
  rw [hfi t]
  exact hy

/-- The actual fibre restrictions form a cocone over the original neighborhood system. -/
def evaluationCocone (n : ℕ) :
    Cocone ((OpenNhds.inclusion y).op ⋙ sourceCohomologyPresheaf (F := F) f n) where
  pt := AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} G n)
  ι :=
    { app U := AddCommGrpCat.ofHom
        (X := ↥(CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U.unop.val)))
        (Y := CategoryTheory.Sheaf.H.{0} G n)
        (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U.unop.val)
          (fibre_mem_preimage i f y hfi U.unop.val U.unop.property) n)
      naturality U V r := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro a
        exact cohomologyEvaluation_restrict i hi hfinite κ
          ((Opens.map f).map ((OpenNhds.inclusion y).map r.unop))
          (fibre_mem_preimage i f y hfi V.unop.val V.unop.property)
          (fibre_mem_preimage i f y hfi U.unop.val U.unop.property) n a }

/-- The genuine colimit universal property gives the actual cohomology-presheaf stalk map. -/
def presheafStalkEvaluation (n : ℕ) :
    TopCat.Presheaf.stalk (sourceCohomologyPresheaf (F := F) f n) y ⟶
      AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} G n) :=
  colimit.desc _ (evaluationCocone i hi hfinite κ f y hfi n)

/-- On an actual neighborhood germ this map is the original Ext fibre restriction. -/
theorem presheafStalkEvaluation_germ (n : ℕ) (U : Opens Y) (hy : y ∈ U) :
    TopCat.Presheaf.germ (sourceCohomologyPresheaf (F := F) f n) U y hy ≫
      presheafStalkEvaluation i hi hfinite κ f y hfi n =
        AddCommGrpCat.ofHom
          (cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
            (fibre_mem_preimage i f y hfi U hy) n) :=
  colimit.ι_desc (evaluationCocone i hi hfinite κ f y hfi n) (op ⟨U, hy⟩)

theorem presheafStalkEvaluation_germ_apply (n : ℕ) (U : Opens Y) (hy : y ∈ U)
    (a : CategoryTheory.Sheaf.H'.{0} F n ((Opens.map f).obj U)) :
    presheafStalkEvaluation i hi hfinite κ f y hfi n
      (TopCat.Presheaf.germ (sourceCohomologyPresheaf (F := F) f n) U y hy a) =
        cohomologyEvaluation i hi hfinite κ ((Opens.map f).obj U)
          (fibre_mem_preimage i f y hfi U hy) n a :=
  ConcreteCategory.congr_hom
    (presheafStalkEvaluation_germ i hi hfinite κ f y hfi n U hy) a

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood
