import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSheafBasic
import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyConstantStalk
import Mathlib.Topology.Sheaves.Abelian

/-!
# The actual constant augmentation is monic

At any point, a constant-sheaf stalk element has an original constant
representative. Equality of its images in the sheafified cochains is
equality of the original cochain germs. Restricting to a common actual
neighborhood and evaluating at its original singular vertex distinguishes
the two coefficients. No local contractibility is needed for this part.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalExact

open FirstHurewicz

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- The original constant representative maps to its original constant
zero-cochain, followed by the native sheafification unit. -/
theorem sheafAugmentation_app_unit (U : Opens X) (a : A) :
    (sheafAugmentation X A).hom.app (op U)
        ((ConstantSheafFirstCohomology.Constant.unit X A).app (op U) a) =
      (cochainSheafUnit X A 0).app (op U) (constantCochain U A a) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (constantUnit_sheafAugmentation X A) (op U)) a

/-- The genuine augmentation is injective on every original stalk. -/
theorem sheafAugmentation_stalk_injective (x : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (sheafAugmentation X A).hom) := by
  change Function.Injective (fun a : TopCat.Presheaf.stalk (C := AddCommGrpCat)
    (ConstantSheafFirstCohomology.Constant.sheaf X A).obj x =>
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (sheafAugmentation X A).hom a)
  intro a b hab
  let e := ConstantSheafFirstCohomology.Constant.stalkEquiv X A x
  have ha : a = TopCat.Presheaf.germ
      (ConstantSheafFirstCohomology.Constant.sheaf X A).obj ⊤ x trivial
        ((ConstantSheafFirstCohomology.Constant.unit X A).app (op ⊤) (e a)) := by
    apply e.injective
    exact (ConstantSheafFirstCohomology.Constant.stalkEquiv_germ_unit X A x ⊤ trivial (e a)).symm
  have hb : b = TopCat.Presheaf.germ
      (ConstantSheafFirstCohomology.Constant.sheaf X A).obj ⊤ x trivial
        ((ConstantSheafFirstCohomology.Constant.unit X A).app (op ⊤) (e b)) := by
    apply e.injective
    exact (ConstantSheafFirstCohomology.Constant.stalkEquiv_germ_unit X A x ⊤ trivial (e b)).symm
  have hmap (t : A) := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (F := (ConstantSheafFirstCohomology.Constant.sheaf X A).obj)
    (G := (cochainSheaf X A 0).obj) ⊤ x trivial (sheafAugmentation X A).hom
      ((ConstantSheafFirstCohomology.Constant.unit X A).app (op ⊤) t)
  have hmap' (t : A) :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (sheafAugmentation X A).hom
        (TopCat.Presheaf.germ (ConstantSheafFirstCohomology.Constant.sheaf X A).obj
          ⊤ x trivial ((ConstantSheafFirstCohomology.Constant.unit X A).app (op ⊤) t)) =
      TopCat.Presheaf.germ (cochainSheaf X A 0).obj ⊤ x trivial
        ((cochainSheafUnit X A 0).app (op ⊤) (constantCochain (⊤ : Opens X) A t)) :=
    (hmap t).trans (congrArg
      (TopCat.Presheaf.germ (C := AddCommGrpCat) (cochainSheaf X A 0).obj ⊤ x trivial)
      (sheafAugmentation_app_unit X A ⊤ t))
  let μ := (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map (sheafAugmentation X A).hom
  have hσ := (hmap' (e a)).symm.trans
    ((congrArg μ ha).symm.trans (hab.trans ((congrArg μ hb).trans (hmap' (e b)))))
  have hg := (Sheafification.germ_unit_eq_iff (cochainPresheaf X A 0) ⊤ ⊤ x
    trivial trivial (constantCochain (⊤ : Opens X) A (e a))
    (constantCochain (⊤ : Opens X) A (e b))).mp hσ
  obtain ⟨V, hxV, i, j, hij⟩ := (cochainPresheaf X A 0).germ_eq x
    (U := ⊤) (V := ⊤) trivial trivial _ _ hg
  change (singularPullback A ((Opens.toTopCat X).map i).hom).f 0
      (constantCochain (⊤ : Opens X) A (e a)) =
    (singularPullback A ((Opens.toTopCat X).map j).hom).f 0
      (constantCochain (⊤ : Opens X) A (e b)) at hij
  have hconst : constantCochain V A (e a) = constantCochain V A (e b) :=
    (singularPullback_constant A ((Opens.toTopCat X).map i).hom (e a)).symm.trans
      (hij.trans (singularPullback_constant A ((Opens.toTopCat X).map j).hom (e b)))
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact e.injective (constantCochain_injective V A hconst)

/-- The original sheaf augmentation is a monomorphism on every space. -/
theorem sheafAugmentation_mono : Mono (sheafAugmentation X A) := by
  apply (TopCat.Presheaf.mono_iff_stalk_mono (sheafAugmentation X A)).mpr
  intro x
  exact (AddCommGrpCat.mono_iff_injective _).mpr (sheafAugmentation_stalk_injective X A x)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalExact
