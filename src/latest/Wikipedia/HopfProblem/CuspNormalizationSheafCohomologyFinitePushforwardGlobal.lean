import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardExact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Limits.Preorder

/-!
# The actual global-section comparison for pushforward

The top open set pulls back to the top open set, so the literal global
sections of an actual pushforward agree with the original global
sections. The actual constant-integer-sheaf adjunction turns this into
a natural equivalence of morphism groups. Its value at the identity is
the canonical constant-integer map used for the higher Ext comparison.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward

/-- The genuine integer sheaf appearing in Mathlib's definition of `Sheaf.H`. -/
abbrev integerSheaf (X : TopCat.{0}) : AbelianSheaf X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift.{0} ℤ))

/-- The actual small Grothendieck sheaf category supplies the required Ext instance. -/
instance abelianSheaf_hasExt (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

/-- The actual constant-sheaf adjunction identifies morphisms from the
integer sheaf with literal global sections. -/
def homGlobalEquiv (X : TopCat.{0}) (F : AbelianSheaf X) :
    (integerSheaf X ⟶ F) ≃+ F.obj.obj (op (⊤ : Opens X)) := by
  let K : AddCommGrpCat ⥤ AbelianSheaf X :=
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat
  let Γ : AbelianSheaf X ⥤ AddCommGrpCat :=
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op (⊤ : Opens X))
  let adj : K ⊣ Γ := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat
    (show IsTerminal (⊤ : Opens X) from isTerminalTop)
  let _ : Γ.Additive := ⟨by intros; rfl⟩
  let _ : K.Additive := adj.left_adjoint_additive
  exact (adj.homAddEquiv _ F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- The actual global-section representation is natural in the sheaf. -/
theorem homGlobalEquiv_naturality (X : TopCat.{0}) {F G : AbelianSheaf X}
    (h : integerSheaf X ⟶ F) (g : F ⟶ G) :
    homGlobalEquiv X G (h ≫ g) = g.hom.app (op (⊤ : Opens X)) (homGlobalEquiv X F h) := by
  simp only [homGlobalEquiv, AddEquiv.trans_apply]
  rfl

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- Global sections of the genuine pushforward are literally the
original global sections, since inverse image preserves the top open set. -/
def globalSectionsEquiv (F : AbelianSheaf X) :
    ((pushforward f).obj F).obj.obj (op (⊤ : Opens Y)) ≃+
      F.obj.obj (op (⊤ : Opens X)) := AddEquiv.refl _

/-- The natural degree-zero morphism equivalence associated to actual pushforward. -/
def homPushforwardEquiv (F : AbelianSheaf X) :
    (integerSheaf X ⟶ F) ≃+ (integerSheaf Y ⟶ (pushforward f).obj F) :=
  (homGlobalEquiv X F).trans
    ((globalSectionsEquiv f F).symm.trans (homGlobalEquiv Y ((pushforward f).obj F)).symm)

/-- The representing-morphism equivalence preserves the actual global section. -/
theorem homPushforwardEquiv_global (F : AbelianSheaf X) (h : integerSheaf X ⟶ F) :
    homGlobalEquiv Y ((pushforward f).obj F) (homPushforwardEquiv f F h) =
      homGlobalEquiv X F h :=
  (homGlobalEquiv Y ((pushforward f).obj F)).apply_symm_apply _

/-- The morphism comparison commutes with every actual sheaf morphism. -/
theorem homPushforwardEquiv_naturality {F G : AbelianSheaf X}
    (h : integerSheaf X ⟶ F) (g : F ⟶ G) :
    homPushforwardEquiv f G (h ≫ g) =
      homPushforwardEquiv f F h ≫ (pushforward f).map g := by
  apply (homGlobalEquiv Y ((pushforward f).obj G)).injective
  exact (homPushforwardEquiv_global f G (h ≫ g)).trans
    ((homGlobalEquiv_naturality X h g).trans
      ((congrArg (g.hom.app (op (⊤ : Opens X)))
        (homPushforwardEquiv_global f F h).symm).trans
        (homGlobalEquiv_naturality Y (homPushforwardEquiv f F h)
          ((pushforward f).map g)).symm))

/-- The canonical actual integer-sheaf map into its pushforward. -/
def integerUnit : integerSheaf Y ⟶ (pushforward f).obj (integerSheaf X) :=
  homPushforwardEquiv f (integerSheaf X) (𝟙 _)

/-- Postcomposition of the canonical integer map is exactly the
proved representing-morphism equivalence. -/
theorem integerUnit_comp {F : AbelianSheaf X} (h : integerSheaf X ⟶ F) :
    integerUnit f ≫ (pushforward f).map h = homPushforwardEquiv f F h :=
  (homPushforwardEquiv_naturality f (𝟙 _) h).symm.trans
    (congrArg (homPushforwardEquiv f F) (Category.id_comp h))

/-- The actual degree-zero map to pushforward is bijective, without
any finiteness or separation assumptions on the continuous map. -/
theorem integerUnit_bijective (F : AbelianSheaf X) :
    Function.Bijective (fun h : integerSheaf X ⟶ F => integerUnit f ≫ (pushforward f).map h) := by
  have heq : (fun h : integerSheaf X ⟶ F => integerUnit f ≫ (pushforward f).map h) =
      homPushforwardEquiv f F := funext (integerUnit_comp f)
  rw [heq]
  exact (homPushforwardEquiv f F).bijective

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward
