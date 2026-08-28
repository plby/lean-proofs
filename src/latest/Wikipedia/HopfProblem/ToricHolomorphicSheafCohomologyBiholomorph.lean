import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBiholomorphBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforward

/-!
# Genuine holomorphic cohomology under an actual biholomorphism

The section equivalences give the actual holomorphic sheaf pushforward
isomorphism, with literal composition as its forward map. The underlying
map is a closed homeomorphism with singleton fibres, so the proved
finite closed pushforward comparison identifies genuine Mathlib sheaf
cohomology in every degree.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Biholomorph

variable {E E' H H' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ E' H'}
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]
  (e : Diffeomorph I J M N ω)

/-- The actual underlying continuous map. -/
def underlyingMap : TopCat.of M ⟶ TopCat.of N :=
  TopCat.ofHom ⟨e, e.continuous⟩

/-- The literal section pullbacks commute with actual restriction. -/
def ringPresheafIso :
    (HolomorphicFunctionSheaf.sheaf J N).presheaf ≅
      ((TopCat.Sheaf.pushforward CommRingCat (underlyingMap e)).obj
        (HolomorphicFunctionSheaf.sheaf I M)).presheaf :=
  NatIso.ofComponents
    (fun U => (sectionPullback e U.unop).toRingEquiv.toCommRingCatIso)
    (by intro U V h; ext f; rfl)

/-- The actual holomorphic ring-sheaf pushforward identification. -/
def ringSheafIso : HolomorphicFunctionSheaf.sheaf J N ≅
    (TopCat.Sheaf.pushforward CommRingCat (underlyingMap e)).obj
      (HolomorphicFunctionSheaf.sheaf I M) :=
  ObjectProperty.isoMk _ (ringPresheafIso e)

/-- The same actual sheaf identification after forgetting to additive groups. -/
def additiveSheafIso : HolomorphicFunctionSheaf.additiveSheaf J N ≅
    (TopCat.Sheaf.pushforward AddCommGrpCat (underlyingMap e)).obj
      (HolomorphicFunctionSheaf.additiveSheaf I M) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).mapIso
    (ringSheafIso e)

/-- The actual pushforward isomorphism is literal pullback of functions. -/
@[simp] theorem additiveSheafIso_hom_app (U : Opens N)
    (f : HolomorphicFunctionSheaf.Section J N U) :
    (additiveSheafIso e).hom.hom.app (op U) f = sectionPullback e U f := rfl

/-- Every actual fibre of the underlying biholomorphism is finite. -/
theorem underlyingMap_fibre_finite (y : N) :
    ((underlyingMap e) ⁻¹' {y}).Finite :=
  (Set.finite_singleton y).preimage e.injective.injOn

/-- Genuine sheaf cohomology of actual holomorphic functions is
preserved by the actual biholomorphism in every degree. -/
def cohomologyEquiv [T2Space M] (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf J N) n ≃+
      CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) n := by
  let ei := (CategoryTheory.Sheaf.functorH _ n).mapIso (additiveSheafIso e)
  exact ei.addCommGroupIsoToAddEquiv.trans
    (CuspNormalization.SheafCohomologyFinitePushforward.cohomologyEquiv
      (underlyingMap e) e.toHomeomorph.isClosedMap (underlyingMap_fibre_finite e)
      (HolomorphicFunctionSheaf.additiveSheaf I M) n)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Biholomorph
