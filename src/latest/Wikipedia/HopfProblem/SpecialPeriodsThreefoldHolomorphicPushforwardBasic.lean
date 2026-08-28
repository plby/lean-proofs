import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDirectImage
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZero
import Wikipedia.HopfProblem.SheafHigherDirectImageBasic

/-!
# The native additive degree-zero direct image of the holomorphic sheaf

The all-open holomorphic pullback isomorphism is already proved for
the original ring sheaves.  Forgetting ring structure gives the actual
additive pushforward comparison.  The native degree-zero derived-
functor comparison then identifies the actual `R⁰f_* O_X` with `O_P¹`.
The maps retain the original holomorphic pullback and commute with the
endomorphisms given by multiplication by complex scalars.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicPushforward

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

abbrev baseAdditiveSheaf := HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ) RiemannSphere

abbrev totalAdditiveSheaf := HolomorphicFunctionSheaf.additiveSheaf IF Space

/-- The actual additive sheaf pushforward of the actual holomorphic sheaf. -/
abbrev additiveDirectImage :=
  (SheafHigherDirectImage.pushforward sphereProjectionMap).obj totalAdditiveSheaf

/-- Forgetting the proved ring-sheaf isomorphism gives the native
additive-sheaf isomorphism, with the same section maps. -/
def additiveDirectImageIso : baseAdditiveSheaf ≅ additiveDirectImage :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).mapIso
    holomorphicDirectImageIso

@[simp] theorem additiveDirectImageIso_hom_app (U : Opens RiemannSphere)
    (s : BaseSection U) :
    additiveDirectImageIso.hom.hom.app (op U) s = pullbackSection U s := rfl

/-- The actual additive pullback commutes with pointwise complex scalars. -/
@[reassoc] theorem additiveDirectImageIso_scalar (c : ℂ) :
    HolomorphicFunctionSheaf.scalarSheafEnd 𝓘(ℂ) RiemannSphere c ≫ additiveDirectImageIso.hom =
      additiveDirectImageIso.hom ≫
        (SheafHigherDirectImage.pushforward sphereProjectionMap).map
          (HolomorphicFunctionSheaf.scalarSheafEnd IF Space c) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The actual native right-derived pushforward in degree zero. -/
abbrev derivedZeroSheaf :=
  SheafHigherDirectImage.sheaf sphereProjectionMap totalAdditiveSheaf 0

/-- The native derived-functor degree-zero comparison to actual pushforward. -/
def derivedZeroToPushforwardIso : derivedZeroSheaf ≅ additiveDirectImage :=
  (SheafHigherDirectImage.zeroIso sphereProjectionMap).app totalAdditiveSheaf

/-- The original holomorphic pullback followed by the canonical
degree-zero derived-functor comparison. -/
def derivedZeroIso : baseAdditiveSheaf ≅ derivedZeroSheaf :=
  additiveDirectImageIso ≪≫ derivedZeroToPushforwardIso.symm

/-- Reading the comparison in ordinary pushforward recovers the
original, literal holomorphic pullback. -/
@[reassoc] theorem derivedZeroIso_hom_toPushforward :
    derivedZeroIso.hom ≫ derivedZeroToPushforwardIso.hom = additiveDirectImageIso.hom := by
  let e := derivedZeroToPushforwardIso
  change (additiveDirectImageIso.hom ≫ e.inv) ≫ e.hom = additiveDirectImageIso.hom
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => additiveDirectImageIso.hom ≫ g) e.inv_hom_id).trans
      (Category.comp_id _))

/-- The scalar endomorphism is obtained by applying the genuine
right-derived functor to the original scalar sheaf map. -/
def derivedScalarEnd (c : ℂ) : derivedZeroSheaf ⟶ derivedZeroSheaf :=
  (SheafHigherDirectImage.functor sphereProjectionMap 0).map
    (HolomorphicFunctionSheaf.scalarSheafEnd IF Space c)

/-- The native derived comparison is compatible with the original
complex scalar action, not only with an abstract additive equivalence. -/
@[reassoc] theorem derivedZeroIso_scalar (c : ℂ) :
    HolomorphicFunctionSheaf.scalarSheafEnd 𝓘(ℂ) RiemannSphere c ≫ derivedZeroIso.hom =
      derivedZeroIso.hom ≫ derivedScalarEnd c := by
  let a := HolomorphicFunctionSheaf.scalarSheafEnd 𝓘(ℂ) RiemannSphere c
  let p := (SheafHigherDirectImage.pushforward sphereProjectionMap).map
    (HolomorphicFunctionSheaf.scalarSheafEnd IF Space c)
  let e := additiveDirectImageIso
  let z := derivedZeroToPushforwardIso
  have hp : p ≫ z.inv = z.inv ≫ derivedScalarEnd c :=
    (SheafHigherDirectImage.zeroIso sphereProjectionMap).inv.naturality
      (HolomorphicFunctionSheaf.scalarSheafEnd IF Space c)
  change a ≫ (e.hom ≫ z.inv) = (e.hom ≫ z.inv) ≫ derivedScalarEnd c
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ z.inv) (additiveDirectImageIso_scalar c)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => e.hom ≫ g) hp).trans (Category.assoc _ _ _).symm)))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicPushforward
