import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroSheaf
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZero
import Wikipedia.HopfProblem.SheafHigherDirectImageBasic

/-!
# The native degree-zero derived pushforward of a period family

Forgetting the proved actual ring-sheaf isomorphism gives the genuine
additive pushforward comparison. Mathlib's canonical degree-zero
right-derived comparison then identifies the original `R⁰f_*O` with
the base holomorphic sheaf. Both original scalar endomorphisms and
every actual restriction map are preserved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IB" => modelWithCornersSelf ℂ V
local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The original additive holomorphic sheaf on the given base. -/
abbrev baseAdditiveSheaf (_P : HolomorphicPeriodMap V B) :=
  HolomorphicFunctionSheaf.additiveSheaf IB B

/-- The actual additive holomorphic sheaf in the unchanged family quotient atlas. -/
def totalAdditiveSheaf (P : HolomorphicPeriodMap V B) :
    TopCat.Sheaf AddCommGrpCat (TopCat.of P.TotalSpace) := by
  letI := P.totalChartedSpace
  exact HolomorphicFunctionSheaf.additiveSheaf IT P.TotalSpace

/-- The genuine additive sheaf pushforward along the original projection. -/
abbrev additiveDirectImage (P : HolomorphicPeriodMap V B) :=
  (SheafHigherDirectImage.pushforward (projectionMap P)).obj (totalAdditiveSheaf P)

/-- The original base holomorphic scalar endomorphism. -/
def baseScalarEnd (P : HolomorphicPeriodMap V B) (c : ℂ) :
    baseAdditiveSheaf P ⟶ baseAdditiveSheaf P :=
  HolomorphicFunctionSheaf.scalarSheafEnd IB B c

/-- The original total-space holomorphic scalar endomorphism, in its native atlas. -/
def totalScalarEnd (P : HolomorphicPeriodMap V B) (c : ℂ) :
    totalAdditiveSheaf P ⟶ totalAdditiveSheaf P := by
  letI := P.totalChartedSpace
  exact HolomorphicFunctionSheaf.scalarSheafEnd IT P.TotalSpace c

/-- The actual native right-derived pushforward sheaf in degree zero. -/
abbrev derivedZeroSheaf (P : HolomorphicPeriodMap V B) :=
  SheafHigherDirectImage.sheaf (projectionMap P) (totalAdditiveSheaf P) 0

/-- Mathlib's canonical comparison of actual degree-zero derived pushforward
with the original additive sheaf pushforward. -/
def derivedZeroToPushforwardIso (P : HolomorphicPeriodMap V B) :
    derivedZeroSheaf P ≅ additiveDirectImage P :=
  (SheafHigherDirectImage.zeroIso (projectionMap P)).app (totalAdditiveSheaf P)

/-- Apply the genuine right-derived functor to original complex multiplication. -/
def derivedScalarEnd (P : HolomorphicPeriodMap V B) (c : ℂ) :
    derivedZeroSheaf P ⟶ derivedZeroSheaf P :=
  (SheafHigherDirectImage.functor (projectionMap P) 0).map (totalScalarEnd P c)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The additive comparison retains exactly the proved all-open holomorphic pullback. -/
def additiveDirectImageIso (P : HolomorphicPeriodMap V B) :
    baseAdditiveSheaf P ≅ additiveDirectImage P :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).mapIso
    (holomorphicDirectImageIso P)

@[simp] theorem additiveDirectImageIso_hom_app (P : HolomorphicPeriodMap V B)
    (U : Opens B) (f : BaseSection P U) :
    (additiveDirectImageIso P).hom.hom.app (op U) f = pullbackSection P U f := rfl

@[simp] theorem additiveDirectImageIso_inv_app (P : HolomorphicPeriodMap V B)
    (U : Opens B) (s : PreimageSection P U) :
    (additiveDirectImageIso P).inv.hom.app (op U) s = descendedSection P U s := rfl

/-- Actual pullback commutes with the original pointwise complex scalar maps. -/
@[reassoc] theorem additiveDirectImageIso_scalar (P : HolomorphicPeriodMap V B) (c : ℂ) :
    baseScalarEnd P c ≫ (additiveDirectImageIso P).hom =
      (additiveDirectImageIso P).hom ≫
        (SheafHigherDirectImage.pushforward (projectionMap P)).map (totalScalarEnd P c) := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The actual `O_B ≅ R⁰f_*O_Total` comparison, using the original
all-open holomorphic pullback and the canonical derived-functor isomorphism. -/
def derivedZeroIso (P : HolomorphicPeriodMap V B) :
    baseAdditiveSheaf P ≅ derivedZeroSheaf P :=
  additiveDirectImageIso P ≪≫ (derivedZeroToPushforwardIso P).symm

/-- Reading the degree-zero derived comparison in ordinary pushforward
recovers exactly the original holomorphic pullback morphism. -/
@[reassoc] theorem derivedZeroIso_hom_toPushforward (P : HolomorphicPeriodMap V B) :
    (derivedZeroIso P).hom ≫ (derivedZeroToPushforwardIso P).hom =
      (additiveDirectImageIso P).hom := by
  let e := derivedZeroToPushforwardIso P
  change ((additiveDirectImageIso P).hom ≫ e.inv) ≫ e.hom = (additiveDirectImageIso P).hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => (additiveDirectImageIso P).hom ≫ g) e.inv_hom_id).trans
      (Category.comp_id _))

/-- The native derived comparison intertwines the original sheaf scalar
maps with the actual right-derived scalar endomorphism. -/
@[reassoc] theorem derivedZeroIso_scalar (P : HolomorphicPeriodMap V B) (c : ℂ) :
    baseScalarEnd P c ≫ (derivedZeroIso P).hom =
      (derivedZeroIso P).hom ≫ derivedScalarEnd P c := by
  let a := baseScalarEnd P c
  let b := (SheafHigherDirectImage.pushforward (projectionMap P)).map (totalScalarEnd P c)
  let e := additiveDirectImageIso P
  let z := derivedZeroToPushforwardIso P
  have hb : b ≫ z.inv = z.inv ≫ derivedScalarEnd P c :=
    (SheafHigherDirectImage.zeroIso (projectionMap P)).inv.naturality (totalScalarEnd P c)
  change a ≫ (e.hom ≫ z.inv) = (e.hom ≫ z.inv) ≫ derivedScalarEnd P c
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ z.inv) (additiveDirectImageIso_scalar P c)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => e.hom ≫ g) hb).trans (Category.assoc _ _ _).symm)))

/-- On each actual base open, the derived comparison represents literal pullback. -/
theorem derivedZeroIso_hom_app_toPushforward (P : HolomorphicPeriodMap V B)
    (U : Opens B) (f : BaseSection P U) :
    (derivedZeroToPushforwardIso P).hom.hom.app (op U)
        ((derivedZeroIso P).hom.hom.app (op U) f) = pullbackSection P U f :=
  congrArg (fun a : baseAdditiveSheaf P ⟶ additiveDirectImage P => a.hom.app (op U) f)
    (derivedZeroIso_hom_toPushforward P)

/-- Its inverse reads an actual derived degree-zero section in ordinary
pushforward and then evaluates at the original zero section. -/
@[simp] theorem derivedZeroIso_inv_app (P : HolomorphicPeriodMap V B)
    (U : Opens B) (s : (derivedZeroSheaf P).presheaf.obj (op U)) :
    (derivedZeroIso P).inv.hom.app (op U) s =
      descendedSection P U ((derivedZeroToPushforwardIso P).hom.hom.app (op U) s) := rfl

/-- Actual complex multiplication is preserved on every open-set component. -/
theorem derivedZeroIso_hom_app_scalar (P : HolomorphicPeriodMap V B) (U : Opens B)
    (c : ℂ) (f : BaseSection P U) :
    (derivedScalarEnd P c).hom.app (op U) ((derivedZeroIso P).hom.hom.app (op U) f) =
      (derivedZeroIso P).hom.hom.app (op U) (c • f) :=
  (congrArg (fun a : baseAdditiveSheaf P ⟶ derivedZeroSheaf P => a.hom.app (op U) f)
    (derivedZeroIso_scalar P c)).symm

/-- The native degree-zero comparison commutes with the literal sheaf restriction. -/
theorem derivedZeroIso_hom_restrict (P : HolomorphicPeriodMap V B) {U W : Opens B}
    (h : U ≤ W) (f : BaseSection P W) :
    (derivedZeroSheaf P).presheaf.map (homOfLE h).op
        ((derivedZeroIso P).hom.hom.app (op W) f) =
      (derivedZeroIso P).hom.hom.app (op U) (baseRestriction P h f) :=
  (ConcreteCategory.congr_hom ((derivedZeroIso P).hom.hom.naturality (homOfLE h).op) f).symm

/-- Its inverse commutes with the original restrictions as well. -/
theorem derivedZeroIso_inv_restrict (P : HolomorphicPeriodMap V B) {U W : Opens B}
    (h : U ≤ W) (s : (derivedZeroSheaf P).presheaf.obj (op W)) :
    (derivedZeroIso P).inv.hom.app (op U)
        ((derivedZeroSheaf P).presheaf.map (homOfLE h).op s) =
      baseRestriction P h ((derivedZeroIso P).inv.hom.app (op W) s) :=
  ConcreteCategory.congr_hom ((derivedZeroIso P).inv.hom.naturality (homOfLE h).op) s

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.Zero
