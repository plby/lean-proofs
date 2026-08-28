import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicPushforwardBasic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphere
import Wikipedia.HopfProblem.SheafLerayLowDegrees

/-!
# The actual Leray edge for the constructed threefold

The proved all-open isomorphism `O_P¹ ≅ f_* O_X` transfers the genuine
positive-degree cohomology vanishing of the sphere to the actual ordinary
pushforward. In particular the two outer groups in the native low-degree
Leray sequence vanish. Its original edge map is consequently a complex-
linear equivalence for the original sheaf-induced scalar structures.

The target is the genuine right-derived pushforward. No splitting or
dimension calculation for that sheaf is used or asserted.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge

open HolomorphicPushforward CuspNormalization.SheafCohomology

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual cohomology comparison induced by the already proved
ordinary direct-image sheaf isomorphism. -/
def directImageCohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} additiveDirectImage n ≃+
      CategoryTheory.Sheaf.H.{0} baseAdditiveSheaf n :=
  ((CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology RiemannSphere) n).mapIso
    additiveDirectImageIso.symm).addCommGroupIsoToAddEquiv

@[simp] theorem directImageCohomologyEquiv_apply (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} additiveDirectImage n) :
    directImageCohomologyEquiv n x =
      CategoryTheory.Sheaf.H.map additiveDirectImageIso.inv n x := rfl

@[simp] theorem directImageCohomologyEquiv_symm_apply (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} baseAdditiveSheaf n) :
    (directImageCohomologyEquiv n).symm x =
      CategoryTheory.Sheaf.H.map additiveDirectImageIso.hom n x := rfl

/-- Every positive cohomology group of the original ordinary pushforward
vanishes, as a consequence of the actual sheaf isomorphism. -/
theorem directImage_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} additiveDirectImage (n + 1)) := by
  refine ⟨fun x y => (directImageCohomologyEquiv (n + 1)).injective ?_⟩
  exact (HolomorphicSheafCohomology.SphereDolbeault.holomorphic_higher_subsingleton n).elim _ _

theorem directImage_higher_eq_zero (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} additiveDirectImage (n + 1)) : x = 0 :=
  (directImage_higher_subsingleton n).elim x 0

instance directImageH1Subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} additiveDirectImage 1) :=
  directImage_higher_subsingleton 0

instance directImageH2Subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} additiveDirectImage 2) :=
  directImage_higher_subsingleton 1

/-- The original holomorphic degree-one Ext group on the actual threefold. -/
abbrev HolomorphicH1 := CategoryTheory.Sheaf.H.{0} totalAdditiveSheaf 1

/-- The genuine first right-derived sheaf pushforward of the original
holomorphic sheaf along the original sphere projection. -/
abbrev firstHigherDirectImage :=
  SheafHigherDirectImage.sheaf sphereProjectionMap totalAdditiveSheaf 1

/-- Genuine degree-zero Ext cohomology of the actual first direct image. -/
abbrev HigherH0 := CategoryTheory.Sheaf.H.{0} firstHigherDirectImage 0

/-- Original pointwise complex multiplication on holomorphic functions. -/
abbrev sourceScalarEnd : ℂ →+* End totalAdditiveSheaf := holomorphicScalarEnd IF Space

/-- Scalars obtained by applying the genuine right-derived pushforward
to the original multiplication endomorphisms. -/
abbrev firstHigherScalarEnd : ℂ →+* End firstHigherDirectImage :=
  SheafLerayLowDegrees.Scalars.higherScalarEnd
    sphereProjectionMap totalAdditiveSheaf sourceScalarEnd 1

@[simp] theorem firstHigherScalarEnd_apply (c : ℂ) :
    firstHigherScalarEnd c = (SheafHigherDirectImage.functor sphereProjectionMap 1).map
      (HolomorphicFunctionSheaf.scalarSheafEnd IF Space c) := rfl

instance holomorphicH1Module : Module ℂ HolomorphicH1 :=
  cohomologyModule totalAdditiveSheaf sourceScalarEnd 1

instance higherH0Module : Module ℂ HigherH0 :=
  SheafLerayLowDegrees.Scalars.higherCohomologyModule
    sphereProjectionMap totalAdditiveSheaf sourceScalarEnd 1 0

/-- The source scalar action is induced by the actual holomorphic sheaf map. -/
theorem holomorphicH1_smul (c : ℂ) (x : HolomorphicH1) :
    c • x = CategoryTheory.Sheaf.H.map
      (HolomorphicFunctionSheaf.scalarSheafEnd IF Space c) 1 x := rfl

/-- The target scalar action is the actual derived sheaf scalar map
followed by the original degree-zero cohomology functor. -/
theorem higherH0_smul (c : ℂ) (x : HigherH0) :
    c • x = CategoryTheory.Sheaf.H.map
      ((SheafHigherDirectImage.functor sphereProjectionMap 1).map
        (HolomorphicFunctionSheaf.scalarSheafEnd IF Space c)) 0 x := rfl

/-- The original native Leray edge is bijective on the constructed threefold,
with no vanishing or geometric comparison hypotheses left to supply. -/
theorem nativeEdge_bijective :
    Function.Bijective (SheafLerayLowDegrees.edge sphereProjectionMap totalAdditiveSheaf) :=
  SheafLerayLowDegrees.edge_bijective_of_vanishing sphereProjectionMap totalAdditiveSheaf

/-- The actual native Leray edge is unconditionally a complex-linear
equivalence for the original scalar actions. -/
def nativeEdgeLinearEquiv : HolomorphicH1 ≃ₗ[ℂ] HigherH0 :=
  SheafLerayLowDegrees.Scalars.edgeLinearEquivOfVanishing
    sphereProjectionMap totalAdditiveSheaf sourceScalarEnd

/-- The forward map is exactly the original Leray edge, not a map chosen
from a dimension comparison. -/
@[simp] theorem nativeEdgeLinearEquiv_apply (x : HolomorphicH1) :
    nativeEdgeLinearEquiv x =
      SheafLerayLowDegrees.edge sphereProjectionMap totalAdditiveSheaf x := rfl

@[simp] theorem nativeEdgeLinearEquiv_toAddEquiv :
    nativeEdgeLinearEquiv.toAddEquiv =
      SheafLerayLowDegrees.edgeEquivOfVanishing sphereProjectionMap totalAdditiveSheaf := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge
