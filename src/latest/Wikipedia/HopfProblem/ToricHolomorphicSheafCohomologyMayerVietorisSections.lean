import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyMayerVietorisBasic
import Wikipedia.HopfProblem.SheafHigherDirectImageSectionsBasic

/-!
# The actual degree-zero Mayer–Vietoris map is the difference of section restrictions

The comparison uses the genuine free-open-sheaf representation and its
proved naturality under actual inclusions of opens.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.MayerVietoris

open OpenRestriction

variable {X : TopCat.{0}}

theorem zeroEquiv_mk₀ (U : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (h : freeOpen U ⟶ F) :
    zeroEquiv U F (Ext.mk₀ h) = freeHomAddEquiv U F h :=
  congrArg (freeHomAddEquiv U F)
    ((Ext.addEquiv₀ (C := TopCat.Sheaf AddCommGrpCat.{0} X)
      (X := freeOpen U) (Y := F)).apply_symm_apply h)

/-- The actual Ext-zero comparison commutes with restriction to an actual open. -/
theorem zeroEquiv_naturality_open {U V : Opens X} (i : U ⟶ V)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (a : CategoryTheory.Sheaf.H'.{0} F 0 V) :
    zeroEquiv U F ((F.cohomologyPresheaf 0).map i.op a) =
      F.obj.map i.op (zeroEquiv V F a) := by
  obtain ⟨h, rfl⟩ := (Ext.mk₀_bijective
    (C := TopCat.Sheaf AddCommGrpCat.{0} X) (freeOpen V) F).surjective a
  have hc : (F.cohomologyPresheaf 0).map i.op (Ext.mk₀ h) =
      Ext.mk₀ ((SheafHigherDirectImage.Sections.freeOpenFunctor X).map i ≫ h) :=
    Ext.mk₀_comp_mk₀ _ _
  exact Eq.trans (congrArg (zeroEquiv U F) hc)
    (Eq.trans (zeroEquiv_mk₀ U F _)
      (Eq.trans (SheafHigherDirectImage.Sections.freeHomAddEquiv_naturality_open i F h)
        (congrArg (F.obj.map i.op) (zeroEquiv_mk₀ V F h).symm)))

variable (F : TopCat.Sheaf AddCommGrpCat.{0} X) (U V : Opens X)

/-- The literal difference of the two restriction maps on actual sections. -/
def sectionsDifference :
    F.obj.obj (op U) × F.obj.obj (op V) →+ F.obj.obj (op (U ⊓ V)) where
  toFun s := F.obj.map (homOfLE (show U ⊓ V ≤ U from inf_le_left)).op s.1 -
    F.obj.map (homOfLE (show U ⊓ V ≤ V from inf_le_right)).op s.2
  map_zero' := by
    change F.obj.map _ (0 : F.obj.obj (op U)) - F.obj.map _ (0 : F.obj.obj (op V)) = 0
    simp only [map_zero, sub_self]
  map_add' a b := by
    change F.obj.map _ (a.1 + b.1) - F.obj.map _ (a.2 + b.2) = _
    rw [map_add, map_add]
    abel

/-- The actual degree-zero Mayer–Vietoris morphism is precisely the section difference. -/
theorem zeroEquiv_restrictionDifference
    (a : CategoryTheory.Sheaf.H'.{0} F 0 U) (b : CategoryTheory.Sheaf.H'.{0} F 0 V) :
    zeroEquiv (U ⊓ V) F (restrictionDifference F U V 0
      ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨a, b⟩)) =
      sectionsDifference F U V (zeroEquiv U F a, zeroEquiv V F b) := by
  have h := (square U V).fromBiprod_biprodIsoProd_inv_apply F a b
  exact Eq.trans (congrArg (zeroEquiv (U ⊓ V) F) h)
    (Eq.trans (map_sub (zeroEquiv (U ⊓ V) F) _ _)
      (congrArg₂ (fun x y : F.obj.obj (op (U ⊓ V)) => x - y)
        (zeroEquiv_naturality_open (homOfLE inf_le_left) F a)
        (zeroEquiv_naturality_open (homOfLE inf_le_right) F b)))

/-- Surjectivity of the actual section difference gives surjectivity of
the genuine degree-zero Mayer–Vietoris map. -/
theorem restrictionDifference_zero_surjective
    (h : Function.Surjective (sectionsDifference F U V)) :
    Function.Surjective (restrictionDifference F U V 0) := by
  intro x
  obtain ⟨s, hs⟩ := h (zeroEquiv (U ⊓ V) F x)
  let a := (zeroEquiv U F).symm s.1
  let b := (zeroEquiv V F).symm s.2
  refine ⟨(AddCommGrpCat.biprodIsoProd _ _).inv ⟨a, b⟩, ?_⟩
  apply (zeroEquiv (U ⊓ V) F).injective
  exact Eq.trans (zeroEquiv_restrictionDifference F U V a b) (by
    simpa only [a, b, AddEquiv.apply_symm_apply] using hs)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.MayerVietoris
