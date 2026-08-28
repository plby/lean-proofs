import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyExtensionLocal
import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyEtale

/-!
# Global lifting in actual constant-sheaf extensions

The middle sheaf of an extension of native constant sheaves has a genuine
étale covering. Simply connected covering-space lifting extends an actual
middle stalk element to a global section. Connectedness then detects the
image of that section in the original constant integer sheaf.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Extension

variable {X : TopCat.{0}} [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]

/-- The second arrow in an actual extension of a constant abelian sheaf
by the constant integer sheaf is surjective on genuine global sections. -/
theorem integer_global_sections_surjective
    (A : AddCommGrpCat.{0}) {E : TopCat.Sheaf AddCommGrpCat.{0} X}
    (ι : Constant.sheaf X A ⟶ E)
    (π : E ⟶ Constant.sheaf X (AddCommGrpCat.of (ULift.{0} ℤ)))
    (hzero : ι ≫ π = 0) (hS : (ShortComplex.mk ι π hzero).ShortExact) :
    Function.Surjective (π.hom.app (op (⊤ : Opens X))) := by
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  have hbij := locally_germ_bijective A ι π hzero hS
  have hπ : Function.Surjective ((stalkFunctor X x₀).map π) :=
    (AddCommGrpCat.epi_iff_surjective _).mp (stalk_shortExact hS x₀).epi_g
  intro q
  obtain ⟨g, hg⟩ := hπ
    (TopCat.Presheaf.germ (Constant.sheaf X (AddCommGrpCat.of (ULift.{0} ℤ))).obj
      ⊤ x₀ trivial q)
  obtain ⟨s, hs⟩ := Etale.exists_global_section_with_germ_of_germ_bijective E hbij x₀ g
  refine ⟨s, ?_⟩
  apply Constant.germ_injective X (AddCommGrpCat.of (ULift.{0} ℤ))
    ⊤ isPreconnected_univ x₀ trivial
  have hn := ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkFunctor_map_germ ⊤ x₀ trivial π.hom) s
  have hs' : TopCat.Presheaf.germ E.obj ⊤ x₀ trivial s = g := hs
  exact hn.symm.trans ((congrArg
    (fun z : TopCat.Presheaf.stalk (C := AddCommGrpCat) E.obj x₀ =>
      ((stalkFunctor X x₀).map π) z) hs').trans hg)

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Extension
