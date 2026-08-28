import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyConstantBasic
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.Topology.Sheaves.Sheafify

/-!
# Native constant additive sheaf stalks

The constant-presheaf stalk is computed as a colimit over the connected
category of neighborhoods.  The actual sheafification unit is an isomorphism
on stalks.  Consequently the resulting identification with the coefficient
group works on every small space, with no local connectedness assumption.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory Limits TopCat

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Constant

/-- The colimit stalk of the original constant presheaf is its coefficient. -/
def presheafStalkIso (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (x : X) :
    (presheaf X A).stalk x ≅ A := by
  letI : IsConnected (OpenNhds x)ᵒᵖ := IsFiltered.isConnected _
  exact IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ presheaf X A))
    (isColimitConstCocone (OpenNhds x)ᵒᵖ A)

@[reassoc (attr := simp)]
theorem presheaf_germ_stalkIso_hom (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (x : X) (U : Opens X) (hx : x ∈ U) :
    (presheaf X A).germ U x hx ≫ (presheafStalkIso X A x).hom = 𝟙 A := by
  let : IsConnected (OpenNhds x)ᵒᵖ := IsFiltered.isConnected _
  exact colimit.comp_coconePointUniqueUpToIso_hom
    (F := (OpenNhds.inclusion x).op ⋙ presheaf X A)
    (isColimitConstCocone (OpenNhds x)ᵒᵖ A) (op (⟨U, hx⟩ : OpenNhds x))

instance unit_stalk_isIso (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (x : X) :
    IsIso ((Presheaf.stalkFunctor AddCommGrpCat x).map (unit X A)) :=
  Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat (presheaf X A)

/-- The native constant-sheaf stalk is canonically the coefficient group. -/
def stalkIso (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (x : X) :
    Presheaf.stalk (C := AddCommGrpCat) (sheaf X A).obj x ≅ A :=
  (asIso ((Presheaf.stalkFunctor AddCommGrpCat x).map (unit X A))).symm ≪≫
    presheafStalkIso X A x

@[reassoc (attr := simp)]
theorem unit_stalk_stalkIso_hom (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (x : X) :
    (Presheaf.stalkFunctor AddCommGrpCat x).map (unit X A) ≫
      (stalkIso X A x).hom = (presheafStalkIso X A x).hom := by
  change (Presheaf.stalkFunctor AddCommGrpCat x).map (unit X A) ≫
    inv ((Presheaf.stalkFunctor AddCommGrpCat x).map (unit X A)) ≫
      (presheafStalkIso X A x).hom = _
  exact IsIso.hom_inv_id_assoc _ _

@[reassoc (attr := simp)]
theorem unit_germ_stalkIso_hom (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (x : X) (U : Opens X) (hx : x ∈ U) :
    (unit X A).app (op U) ≫ Presheaf.germ (sheaf X A).obj U x hx ≫
      (stalkIso X A x).hom = 𝟙 A := by
  exact (Presheaf.stalkFunctor_map_germ_assoc U x hx (unit X A)
    (stalkIso X A x).hom).symm.trans
      ((congrArg (fun f => (presheaf X A).germ U x hx ≫ f)
        (unit_stalk_stalkIso_hom X A x)).trans
          (presheaf_germ_stalkIso_hom X A x U hx))

/-- The same native stalk identification as an additive equivalence. -/
def stalkEquiv (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (x : X) :
    Presheaf.stalk (C := AddCommGrpCat) (sheaf X A).obj x ≃+ A :=
  (stalkIso X A x).addCommGroupIsoToAddEquiv

@[simp]
theorem stalkEquiv_germ_unit (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (x : X) (U : Opens X) (hx : x ∈ U) (a : A) :
    stalkEquiv X A x
      (Presheaf.germ (sheaf X A).obj U x hx ((unit X A).app (op U) a)) = a :=
  ConcreteCategory.congr_hom (unit_germ_stalkIso_hom X A x U hx) a

theorem stalkEquiv_symm_eq_germ_unit (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (x : X) (U : Opens X) (hx : x ∈ U) (a : A) :
    (stalkEquiv X A x).symm a =
      Presheaf.germ (sheaf X A).obj U x hx ((unit X A).app (op U) a) := by
  apply (stalkEquiv X A x).injective
  exact ((stalkEquiv X A x).apply_symm_apply a).trans
    (stalkEquiv_germ_unit X A x U hx a).symm

/-- A constant section on any neighborhood represents every stalk element. -/
theorem germ_surjective (X : TopCat.{0}) (A : AddCommGrpCat.{0})
    (U : Opens X) (x : X) (hx : x ∈ U) :
    Function.Surjective (Presheaf.germ (sheaf X A).obj U x hx) := by
  intro s
  refine ⟨(unit X A).app (op U) (stalkEquiv X A x s), ?_⟩
  apply (stalkEquiv X A x).injective
  exact stalkEquiv_germ_unit X A x U hx (stalkEquiv X A x s)

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology.Constant
