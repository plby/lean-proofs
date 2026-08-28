import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverBasic

/-!
# Naturality of the genuine open-set Mayer--Vietoris connecting maps

Inclusions of two pairs of actual opens induce a map of the actual
free-open-sheaf short exact sequences. Naturality of their genuine Ext
classes therefore proves naturality of the original connecting maps.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

section Generic

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

theorem biprod_lift_map_comm {P Q A B A' B' : C}
    (p : P ⟶ Q) (a : A ⟶ A') (b : B ⟶ B')
    (f : P ⟶ A) (g : P ⟶ B) (f' : Q ⟶ A') (g' : Q ⟶ B')
    (hf : p ≫ f' = f ≫ a) (hg : p ≫ g' = g ≫ b) :
    p ≫ biprod.lift f' (-g') = biprod.lift f (-g) ≫ biprod.map a b := by
  apply biprod.hom_ext
  · simpa only [Category.assoc, biprod.lift_fst, biprod.map_fst,
      biprod.lift_fst_assoc] using hf
  · simpa only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp]
        using congrArg Neg.neg hg

theorem biprod_map_desc_comm {P Q A B A' B' : C}
    (p : P ⟶ Q) (a : A ⟶ A') (b : B ⟶ B')
    (f : A ⟶ P) (g : B ⟶ P) (f' : A' ⟶ Q) (g' : B' ⟶ Q)
    (hf : a ≫ f' = f ≫ p) (hg : b ≫ g' = g ≫ p) :
    biprod.map a b ≫ biprod.desc f' g' = biprod.desc f g ≫ p := by
  apply biprod.hom_ext'
  · simpa only [biprod.inl_map_assoc, Category.assoc, biprod.inl_desc,
      biprod.inl_desc_assoc] using hf
  · simpa only [biprod.inr_map_assoc, Category.assoc, biprod.inr_desc,
      biprod.inr_desc_assoc] using hg

end Generic

section GenericExt

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_connecting_precomp_naturality {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) {Y : C} (n : ℕ)
    (a : Ext T.X₁ Y n) :
    (Ext.mk₀ φ.τ₃).comp (hT.extClass.comp a (Nat.add_comm 1 n)) (zero_add (n + 1)) =
      hS.extClass.comp ((Ext.mk₀ φ.τ₁).comp a (zero_add n)) (Nat.add_comm 1 n) := by
  exact Eq.trans
    (Ext.comp_assoc (Ext.mk₀ φ.τ₃) hT.extClass a
      (zero_add 1) (Nat.add_comm 1 n) (Nat.add_comm 1 n)).symm
    (Eq.trans
      (congrArg (fun e : Ext S.X₃ T.X₁ 1 => e.comp a (Nat.add_comm 1 n))
        (hS.extClass_naturality hT φ).symm)
      (Ext.comp_assoc_of_second_deg_zero hS.extClass (Ext.mk₀ φ.τ₁) a (Nat.add_comm 1 n)))

end GenericExt

variable {X : TopCat.{0}}

/-- Actual restriction in Mathlib's original cohomology presheaf. -/
abbrev cohomologyRestrict (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)
    {A B : Opens X} (h : A ≤ B) :
    CategoryTheory.Sheaf.H'.{0} F n B →+ CategoryTheory.Sheaf.H'.{0} F n A :=
  ((F.cohomologyPresheaf n).map (homOfLE h).op).hom

theorem cohomologyRestrict_comp (F : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C)
    (a : CategoryTheory.Sheaf.H'.{0} F n C) :
    cohomologyRestrict F n hAB (cohomologyRestrict F n hBC a) =
      cohomologyRestrict F n (hAB.trans hBC) a := by
  change (F.cohomologyPresheaf n).map (homOfLE hAB).op
    ((F.cohomologyPresheaf n).map (homOfLE hBC).op a) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem freeOpen_map_paths {A B C D : Opens X}
    (f : A ⟶ B) (g : B ⟶ D) (p : A ⟶ C) (q : C ⟶ D) :
    (SheafHigherDirectImage.Sections.freeOpenFunctor X).map f ≫
      (SheafHigherDirectImage.Sections.freeOpenFunctor X).map g =
    (SheafHigherDirectImage.Sections.freeOpenFunctor X).map p ≫
      (SheafHigherDirectImage.Sections.freeOpenFunctor X).map q := by
  let G := SheafHigherDirectImage.Sections.freeOpenFunctor X
  exact Eq.trans (G.map_comp f g).symm
    (Eq.trans (congrArg (fun h : A ⟶ D => G.map h) (Subsingleton.elim (f ≫ g) (p ≫ q)))
      (G.map_comp p q))

/-- Inclusions of the two opens induce a genuine morphism of the
actual Mayer--Vietoris free-sheaf short exact sequences. -/
def squareMap {A B U V : Opens X} (hA : A ≤ U) (hB : B ≤ V) :
    (MayerVietoris.square A B).shortComplex ⟶
      (MayerVietoris.square U V).shortComplex where
  τ₁ := (SheafHigherDirectImage.Sections.freeOpenFunctor X).map
    (homOfLE (inf_le_inf hA hB))
  τ₂ := biprod.map
    ((SheafHigherDirectImage.Sections.freeOpenFunctor X).map (homOfLE hA))
    ((SheafHigherDirectImage.Sections.freeOpenFunctor X).map (homOfLE hB))
  τ₃ := (SheafHigherDirectImage.Sections.freeOpenFunctor X).map
    (homOfLE (sup_le_sup hA hB))
  comm₁₂ := by
    apply biprod_lift_map_comm
    all_goals
      change (SheafHigherDirectImage.Sections.freeOpenFunctor X).map _ ≫
        (SheafHigherDirectImage.Sections.freeOpenFunctor X).map _ =
          (SheafHigherDirectImage.Sections.freeOpenFunctor X).map _ ≫
            (SheafHigherDirectImage.Sections.freeOpenFunctor X).map _
      exact freeOpen_map_paths _ _ _ _
  comm₂₃ := by
    apply biprod_map_desc_comm
    all_goals
      change (SheafHigherDirectImage.Sections.freeOpenFunctor X).map _ ≫
        (SheafHigherDirectImage.Sections.freeOpenFunctor X).map _ =
          (SheafHigherDirectImage.Sections.freeOpenFunctor X).map _ ≫
            (SheafHigherDirectImage.Sections.freeOpenFunctor X).map _
      exact freeOpen_map_paths _ _ _ _

/-- Actual Ext connecting classes commute with the actual open restrictions. -/
theorem connecting_naturality (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {A B U V : Opens X} (hA : A ≤ U) (hB : B ≤ V) (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{0} F n (U ⊓ V)) :
    cohomologyRestrict F (n + 1) (sup_le_sup hA hB)
      (MayerVietoris.connecting F U V n a) =
        MayerVietoris.connecting F A B n
          (cohomologyRestrict F n (inf_le_inf hA hB) a) := by
  let φ := squareMap hA hB
  let hS := (MayerVietoris.square A B).shortComplex_shortExact
  let hT := (MayerVietoris.square U V).shortComplex_shortExact
  change (Ext.mk₀ φ.τ₃).comp (hT.extClass.comp a (Nat.add_comm 1 n)) (zero_add (n + 1)) =
    hS.extClass.comp ((Ext.mk₀ φ.τ₁).comp a (zero_add n)) (Nat.add_comm 1 n)
  exact ext_connecting_precomp_naturality hS hT φ n a

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
