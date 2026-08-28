import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageGlobalRestriction
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreStalk

/-!
# Genuine global classes in the actual higher-direct-image stalk

An original global Ext class gives its original neighborhood class and
then an actual derived-sheaf stalk germ. This germ is independent of the
chosen neighborhood. The finite closed fibre evaluation is exactly the
original global coefficient restriction followed by the genuine Ext
comparison, not a newly chosen map between vector spaces.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.GlobalRestriction

open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X) (y : Y) (n : ℕ)

/-- The genuine derived-stalk germ of an original global cohomology class. -/
def globalStalkClass :
    CategoryTheory.Sheaf.H.{0} F n →+ ↥(FibreNeighborhood.derivedStalk (F := F) f y n) :=
  (FibreNeighborhood.derivedNeighborhoodGerm (F := F) f y n ⊤ (by trivial)).hom.comp
    (restrictionMap F ((Opens.map f).obj ⊤) n)

/-- The original global class gives the same actual germ on every neighborhood. -/
theorem globalStalkClass_eq_neighborhood (U : Opens Y) (hy : y ∈ U)
    (a : CategoryTheory.Sheaf.H.{0} F n) :
    globalStalkClass f F y n a =
      FibreNeighborhood.derivedNeighborhoodGerm (F := F) f y n U hy
        (restrictionMap F ((Opens.map f).obj U) n a) := by
  let r : U ⟶ (⊤ : Opens Y) := homOfLE le_top
  have hr := restrictionMap_restrict F ((Opens.map f).map r) n a
  have hg := TopCat.Presheaf.germ_res_apply
    (FibreNeighborhood.sourceCohomologyPresheaf (F := F) f n) r y hy
    (restrictionMap F ((Opens.map f).obj ⊤) n a)
  exact congrArg (SheafHigherDirectImage.stalkCohomologyPresheafIso f F n y).inv
    (hg.symm.trans (congrArg
      (TopCat.Presheaf.germ (FibreNeighborhood.sourceCohomologyPresheaf (F := F) f n) U y hy)
      hr))

variable {T : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)
  {G : AbelianSheaf T} (κ : F ⟶ (pushforward i).obj G) (hfi : ∀ t : T, f (i t) = y)

/-- The actual stalk evaluation retains the original global restriction
class, in every degree and for the original coefficient map. -/
theorem derivedStalkEvaluation_global (a : CategoryTheory.Sheaf.H.{0} F n) :
    FibreNeighborhood.derivedStalkEvaluation i hi hfinite κ f y hfi n
        (globalStalkClass f F y n a) =
      cohomologyEquiv i hi hfinite G n (CategoryTheory.Sheaf.H.map κ n a) :=
  (FibreNeighborhood.derivedStalkEvaluation_germ_apply i hi hfinite κ f y hfi n ⊤
    (by trivial) (restrictionMap F ((Opens.map f).obj ⊤) n a)).trans
      (cohomologyEvaluation_restriction i hi hfinite ((Opens.map f).obj ⊤)
        (FibreNeighborhood.fibre_mem_preimage i f y hfi ⊤ (by trivial)) κ n a)

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.GlobalRestriction
