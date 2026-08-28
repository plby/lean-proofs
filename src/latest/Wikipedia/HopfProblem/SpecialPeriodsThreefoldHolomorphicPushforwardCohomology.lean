import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicPushforwardBasic

/-!
# Scalar-compatible degree-zero cohomology of the actual derived pushforward

All cohomology groups below are the existing Ext-defined `Sheaf.H`.
The scalar module transported along the canonical derived comparison
agrees with the maps induced by the genuinely derived scalar sheaf
endomorphisms.  Actual pullback on global holomorphic sections gives
the comparison with the original threefold's degree-zero cohomology.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicPushforward

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Genuine degree-zero cohomology of the genuine degree-zero derived image. -/
abbrev derivedH0 : Type := CategoryTheory.Sheaf.H.{0} derivedZeroSheaf 0

instance derivedH0AddCommGroup : AddCommGroup derivedH0 :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The comparison is induced by the actual sheaf isomorphism. -/
def derivedH0BaseAddEquiv :
    derivedH0 ≃+ HolomorphicFunctionSheaf.H0 𝓘(ℂ) RiemannSphere :=
  ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology RiemannSphere) 0).mapIso
    derivedZeroIso.symm).addCommGroupIsoToAddEquiv

@[simp] theorem derivedH0BaseAddEquiv_apply (x : derivedH0) :
    derivedH0BaseAddEquiv x = CategoryTheory.Sheaf.H.map derivedZeroIso.inv 0 x := rfl

@[simp] theorem derivedH0BaseAddEquiv_symm_apply
    (x : HolomorphicFunctionSheaf.H0 𝓘(ℂ) RiemannSphere) :
    derivedH0BaseAddEquiv.symm x = CategoryTheory.Sheaf.H.map derivedZeroIso.hom 0 x := rfl

/-- Transport through the canonical comparison, checked against the
actual derived scalar maps below. -/
instance derivedH0Module : Module ℂ derivedH0 := derivedH0BaseAddEquiv.module ℂ

/-- The actual sheaf-induced comparison is complex linear. -/
def derivedH0BaseLinearEquiv :
    derivedH0 ≃ₗ[ℂ] HolomorphicFunctionSheaf.H0 𝓘(ℂ) RiemannSphere :=
  derivedH0BaseAddEquiv.linearEquiv ℂ

/-- The scalar action is exactly the cohomology map induced by applying
the genuine derived functor to the original scalar sheaf endomorphism. -/
theorem h0_map_derivedScalarEnd (c : ℂ) (x : derivedH0) :
    CategoryTheory.Sheaf.H.map (derivedScalarEnd c) 0 x = c • x := by
  obtain ⟨b, rfl⟩ := derivedH0BaseAddEquiv.symm.surjective x
  let a := HolomorphicFunctionSheaf.scalarSheafEnd 𝓘(ℂ) RiemannSphere c
  have h := congrArg
    (fun g : baseAdditiveSheaf ⟶ derivedZeroSheaf => CategoryTheory.Sheaf.H.map g 0 b)
    (derivedZeroIso_scalar c)
  have hn : CategoryTheory.Sheaf.H.map derivedZeroIso.hom 0
      (CategoryTheory.Sheaf.H.map a 0 b) =
      CategoryTheory.Sheaf.H.map (derivedScalarEnd c) 0
        (CategoryTheory.Sheaf.H.map derivedZeroIso.hom 0 b) :=
    (CategoryTheory.Sheaf.H.map_comp_apply a derivedZeroIso.hom b).symm.trans
      (h.trans (CategoryTheory.Sheaf.H.map_comp_apply derivedZeroIso.hom (derivedScalarEnd c) b))
  exact hn.symm.trans
    ((congrArg (CategoryTheory.Sheaf.H.map derivedZeroIso.hom 0)
      (HolomorphicFunctionSheaf.h0_map_scalarSheafEnd 𝓘(ℂ) RiemannSphere c b)).trans
        (derivedH0BaseLinearEquiv.symm.map_smul c b))

/-- The original all-open pullback at the top open set identifies the
actual degree-zero cohomology of the base and the original threefold. -/
def baseH0SourceLinearEquiv :
    HolomorphicFunctionSheaf.H0 𝓘(ℂ) RiemannSphere ≃ₗ[ℂ]
      HolomorphicFunctionSheaf.H0 IF Space :=
  (HolomorphicFunctionSheaf.h0GlobalLinearEquiv 𝓘(ℂ) RiemannSphere).trans
    ((pullbackSectionEquiv ⊤).toLinearEquiv.trans
      (HolomorphicFunctionSheaf.h0GlobalLinearEquiv IF Space).symm)

/-- The comparison retains literal holomorphic pullback on global sections. -/
theorem baseH0SourceLinearEquiv_sections
    (x : HolomorphicFunctionSheaf.H0 𝓘(ℂ) RiemannSphere) :
    HolomorphicFunctionSheaf.h0GlobalAddEquiv IF Space (baseH0SourceLinearEquiv x) =
      pullbackSection ⊤ (HolomorphicFunctionSheaf.h0GlobalAddEquiv 𝓘(ℂ) RiemannSphere x) :=
  (HolomorphicFunctionSheaf.h0GlobalLinearEquiv IF Space).apply_symm_apply _

/-- Genuine degree-zero cohomology of `R⁰f_*O_X` is complex-linearly
identified with genuine degree-zero cohomology on the source. -/
def derivedH0SourceLinearEquiv : derivedH0 ≃ₗ[ℂ] HolomorphicFunctionSheaf.H0 IF Space :=
  derivedH0BaseLinearEquiv.trans baseH0SourceLinearEquiv

/-- The source comparison is the actual sheaf-induced base comparison
followed by literal holomorphic pullback of its global section. -/
theorem derivedH0SourceLinearEquiv_sections (x : derivedH0) :
    HolomorphicFunctionSheaf.h0GlobalAddEquiv IF Space (derivedH0SourceLinearEquiv x) =
      pullbackSection ⊤ (HolomorphicFunctionSheaf.h0GlobalAddEquiv 𝓘(ℂ) RiemannSphere
        (CategoryTheory.Sheaf.H.map derivedZeroIso.inv 0 x)) :=
  baseH0SourceLinearEquiv_sections (derivedH0BaseLinearEquiv x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicPushforward
