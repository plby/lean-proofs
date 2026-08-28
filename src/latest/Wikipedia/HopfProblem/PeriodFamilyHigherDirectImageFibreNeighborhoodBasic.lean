import Wikipedia.HopfProblem.SheafHigherDirectImageSectionsBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardComparison

/-!
# Actual sections on neighborhoods of an entire closed fibre

An open set containing the image of a map pulls back to the whole
source. The actual free sheaf on that open therefore represents the
same sections of a pushforward as the source's integer sheaf represents
globally. These are canonical maps of the original sheaves, not a
replacement definition of a fibre or its cohomology.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood

open HolomorphicSheafCohomology.OpenRestriction
open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X : TopCat.{0}} (i : T ⟶ X) (U : Opens X)
  (hU : ∀ t : T, i t ∈ U)

include hU in
/-- The literal inverse-image open is the whole fibre. -/
theorem inverseImage_eq_top : (Opens.map i).obj U = ⊤ := by
  ext t
  constructor
  · intro _
    trivial
  · intro _
    exact hU t

/-- Actual pushforward sections on the given neighborhood are the original global sections. -/
def sectionsEquiv (G : AbelianSheaf T) :
    ((pushforward i).obj G).obj.obj (op U) ≃+ G.obj.obj (op (⊤ : Opens T)) :=
  (G.obj.mapIso (eqToIso (congrArg op (inverseImage_eq_top i U hU)))).addCommGroupIsoToAddEquiv

/-- The section comparison preserves every genuine coefficient-sheaf map. -/
theorem sectionsEquiv_naturality {F G : AbelianSheaf T} (g : F ⟶ G)
    (s : ((pushforward i).obj F).obj.obj (op U)) :
    sectionsEquiv i U hU G (((pushforward i).map g).hom.app (op U) s) =
      g.hom.app (op (⊤ : Opens T)) (sectionsEquiv i U hU F s) := by
  change G.obj.map (eqToHom (congrArg op (inverseImage_eq_top i U hU)))
      (g.hom.app (op ((Opens.map i).obj U)) s) =
    g.hom.app (op (⊤ : Opens T))
      (F.obj.map (eqToHom (congrArg op (inverseImage_eq_top i U hU))) s)
  exact (g.hom.naturality_apply
    (eqToHom (congrArg op (inverseImage_eq_top i U hU))) s).symm

/-- The two genuine section-representing objects give the actual morphism comparison. -/
def homEquiv (G : AbelianSheaf T) :
    (integerSheaf T ⟶ G) ≃ (freeOpen U ⟶ (pushforward i).obj G) :=
  (homGlobalEquiv T G).toEquiv.trans
    ((sectionsEquiv i U hU G).toEquiv.symm.trans
      (freeHomEquiv U ((pushforward i).obj G)).symm)

/-- The representing-map comparison retains the literal original global section. -/
theorem homEquiv_sections (G : AbelianSheaf T) (a : integerSheaf T ⟶ G) :
    sectionsEquiv i U hU G
      (freeHomEquiv U ((pushforward i).obj G) (homEquiv i U hU G a)) =
        homGlobalEquiv T G a := by
  change sectionsEquiv i U hU G
    (freeHomEquiv U ((pushforward i).obj G)
      ((freeHomEquiv U ((pushforward i).obj G)).symm
        ((sectionsEquiv i U hU G).symm (homGlobalEquiv T G a)))) = _
  rw [Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- The actual comparison is natural in the original coefficient sheaf. -/
theorem homEquiv_naturality {F G : AbelianSheaf T}
    (a : integerSheaf T ⟶ F) (g : F ⟶ G) :
    homEquiv i U hU G (a ≫ g) = homEquiv i U hU F a ≫ (pushforward i).map g := by
  apply (freeHomEquiv U ((pushforward i).obj G)).injective
  apply (sectionsEquiv i U hU G).injective
  rw [homEquiv_sections, freeHomEquiv_naturality, sectionsEquiv_naturality,
    homEquiv_sections]
  exact homGlobalEquiv_naturality T a g

/-- The canonical map from the free neighborhood sheaf to the pushed-forward integer sheaf. -/
def integerUnit : freeOpen U ⟶ (pushforward i).obj (integerSheaf T) :=
  homEquiv i U hU (integerSheaf T) (𝟙 _)

/-- Composing this canonical map with a genuine coefficient morphism gives the comparison. -/
theorem integerUnit_comp {G : AbelianSheaf T} (a : integerSheaf T ⟶ G) :
    integerUnit i U hU ≫ (pushforward i).map a = homEquiv i U hU G a :=
  (homEquiv_naturality i U hU (𝟙 _) a).symm.trans
    (congrArg (homEquiv i U hU G) (Category.id_comp a))

/-- The representing map is genuinely bijective, before passing to higher Ext. -/
theorem integerUnit_bijective (G : AbelianSheaf T) :
    Function.Bijective (fun a : integerSheaf T ⟶ G =>
      integerUnit i U hU ≫ (pushforward i).map a) := by
  have he : (fun a : integerSheaf T ⟶ G =>
      integerUnit i U hU ≫ (pushforward i).map a) = homEquiv i U hU G :=
    funext (integerUnit_comp i U hU)
  rw [he]
  exact (homEquiv i U hU G).bijective

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreNeighborhood
