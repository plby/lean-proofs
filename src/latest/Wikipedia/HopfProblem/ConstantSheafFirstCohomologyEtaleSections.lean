import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyEtaleBasic

/-!
# Gluing continuous étale sections in the original sheaf

The local representatives of a continuous section of the étale projection
have equal germs on overlaps.  Separation and gluing in the original sheaf
therefore give a unique original global section with precisely those germs.
No sheaf of functions or replacement stalk model is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Etale

universe u v w

variable {X : TopCat.{u}} {C : Type v} [Category.{u} C]
  {CC : C → Type u} {FC : C → C → Type w}
  [∀ A B, FunLike (FC A B) (CC A) (CC B)] [ConcreteCategory C FC]
  [HasColimits.{u} C] [PreservesFilteredColimits (forget C)]
  [HasLimits C] [PreservesLimits (forget C)] [(forget C).ReflectsIsomorphisms]

/-- A continuous section of the actual étale projection comes from a
unique global section of the original sheaf. -/
theorem existsUnique_global_section_of_etale_section (F : TopCat.Sheaf C X)
    (σ : C(X, F.presheaf.EtaleSpace)) (hσ : ∀ x : X, (σ x).base = x) :
    ∃! s : ToType (F.presheaf.obj (op ⊤)),
      ∀ x : X, sectionGerm F.presheaf ⊤ s ⟨x, trivial⟩ = σ x := by
  choose U hx s hs using etaleSection_localGerms F.presheaf σ hσ
  have hcompatible : TopCat.Presheaf.IsCompatible F.presheaf U s := by
    intro a b
    apply TopCat.Presheaf.section_ext F (U a ⊓ U b)
    intro x hxU
    rw [F.presheaf.germ_res_apply, F.presheaf.germ_res_apply]
    exact (sectionGerm_eq_iff F.presheaf (U a) (U b) (s a) (s b) x hxU.1 hxU.2).mp
      ((hs a x hxU.1).symm.trans (hs b x hxU.2))
  have hcover : (⊤ : Opens X) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  let i : ∀ x : X, U x ⟶ (⊤ : Opens X) := fun _ => homOfLE le_top
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing' U ⊤ i hcover s hcompatible
  have htGerm (x : X) : sectionGerm F.presheaf ⊤ t ⟨x, trivial⟩ = σ x := by
    calc
      sectionGerm F.presheaf ⊤ t ⟨x, trivial⟩ =
          sectionGerm F.presheaf (U x) (s x) ⟨x, hx x⟩ := by
        apply (sectionGerm_eq_iff F.presheaf ⊤ (U x) t (s x) x trivial (hx x)).mpr
        rw [← F.presheaf.germ_res_apply (i x) x (hx x) t, ht x]
      _ = σ x := (hs x x (hx x)).symm
  refine ⟨t, htGerm, ?_⟩
  intro q hq
  apply TopCat.Presheaf.section_ext F ⊤
  intro x hxTop
  exact (sectionGerm_eq_iff F.presheaf ⊤ ⊤ q t x hxTop hxTop).mp
    ((hq x).trans (htGerm x).symm)

/-- The original global section obtained by genuine sheaf gluing. -/
def sectionOfEtaleSection (F : TopCat.Sheaf C X)
    (σ : C(X, F.presheaf.EtaleSpace)) (hσ : ∀ x : X, (σ x).base = x) :
    ToType (F.presheaf.obj (op ⊤)) :=
  (existsUnique_global_section_of_etale_section F σ hσ).choose

/-- The gluing preserves the entire stalk element at every point. -/
theorem sectionOfEtaleSection_germ (F : TopCat.Sheaf C X)
    (σ : C(X, F.presheaf.EtaleSpace)) (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    sectionGerm F.presheaf ⊤ (sectionOfEtaleSection F σ hσ) ⟨x, trivial⟩ = σ x :=
  (existsUnique_global_section_of_etale_section F σ hσ).choose_spec.1 x

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Etale
