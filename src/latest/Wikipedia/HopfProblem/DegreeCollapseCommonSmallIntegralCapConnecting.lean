import Wikipedia.HopfProblem.DegreeCollapseCommonSmallIntegralCapConnectingLift

/-!
# The original integral connecting map on actual cap representatives

The genuine biproduct lift maps to the original ambient cap and has
boundary equal to the intersection map of the signed overlap cap.
Consequently the original integral Mayer--Vietoris connecting map sends
the ambient cap class to -(-1)^p times the actual overlap cap class.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap

open FirstHurewicz SingularMayerVietoris NoExoticSixSphere
open IntegralCap (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)
open SmallRelativeIntegralCochains (Cochain)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- The actual cap lift projects to the original ambient cap of the cochain difference. -/
theorem capLift_inclusion (p q : ℕ) (α : SingularCohomologyCup.Cochain X p)
    (β : RelativeIntegralCap.Cochain A p) (γ : RelativeIntegralCap.Cochain B p)
    (hα : α = RelativeIntegralCap.toAbsolute A p β - RelativeIntegralCap.toAbsolute B p γ)
    (c : (complex U A V B).X (p + q + 1))
    (cU : SmallChains Coefficient U A (p + q + 1))
    (hcU : smallInclusionMap Coefficient U A (p + q + 1) cU =
      ((inclusion U A V B).f (p + q + 1)).hom c)
    (cV : SmallChains Coefficient V B (p + q + 1))
    (hcV : smallInclusionMap Coefficient V B (p + q + 1) cV =
      ((inclusion U A V B).f (p + q + 1)).hom c) :
    ((IntegralMayerVietoris.smallInclusion U V).f (q + 1)).hom
        (((IntegralMayerVietoris.smallSequence U V).g.f (q + 1)).hom
          (capLift U A V B p q β γ cU cV)) =
      IntegralCap.capInDegree (p := p) (q := q + 1) (by omega) α
        (((inclusion U A V B).f (p + q + 1)).hom c) := by
  have he := congrArg (fun m => (m.f (q + 1)).hom (capLift U A V B p q β γ cU cV))
    (IntegralMayerVietoris.second_inclusion U V)
  apply he.trans
  apply (ChainBiproduct.desc_pair (RelativeCoefficients.inclusion Coefficient U)
    (RelativeCoefficients.inclusion Coefficient V) (q + 1) _ _).trans
  apply (congrArg (fun t : Chains X (q + 1) =>
    inducedChain (subtypeInclusion U) (q + 1)
      (SmallIntegralCap.capInDegree U A (p := p) (q := q + 1) (by omega) β cU) + t)
    ((inducedChain (subtypeInclusion V) (q + 1)).map_neg
      (SmallIntegralCap.capInDegree V B (p := p) (q := q + 1) (by omega) γ cV))).trans
  exact (sub_eq_add_neg _ _).symm.trans
    (SmallIntegralCap.capInDegree_difference U V A B (p := p) (q := q + 1)
      (by omega) α β γ hα _ cU hcU cV hcV).symm

/-- The original connecting map retains both the actual cap classes and the integer sign. -/
theorem connecting_cap_representatives (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (p q : ℕ)
    (α : SingularCohomologyCup.Cochain X p)
    (β : RelativeIntegralCap.Cochain A p) (γ : RelativeIntegralCap.Cochain B p)
    (hα : α = RelativeIntegralCap.toAbsolute A p β - RelativeIntegralCap.toAbsolute B p γ)
    (η : Cochain A B (p + 1))
    (hβ : ((IntegralRelativeCohomologyMayerVietoris.smallRestrictionLeft A B).f (p + 1)).hom η =
      RelativeIntegralCap.coboundary A β)
    (hγ : ((IntegralRelativeCohomologyMayerVietoris.smallRestrictionRight A B).f (p + 1)).hom η =
      RelativeIntegralCap.coboundary B γ)
    (c : (complex U A V B).X (p + q + 1))
    (hc : ((inclusion U A V B).f (p + q)).hom
        (((complex U A V B).d (p + q + 1) (p + q)).hom c) ∈
      LinearMap.range (inducedChain (subtypeInclusion (A ∩ B)) (p + q)))
    (cU : SmallChains Coefficient U A (p + q + 1))
    (hcU : smallInclusionMap Coefficient U A (p + q + 1) cU =
      ((inclusion U A V B).f (p + q + 1)).hom c)
    (cV : SmallChains Coefficient V B (p + q + 1))
    (hcV : smallInclusionMap Coefficient V B (p + q + 1) cV =
      ((inclusion U A V B).f (p + q + 1)).hom c)
    (a : ModuleHomology.Cycle (singularComplex X) (q + 1))
    (ha : a.val = IntegralCap.capInDegree (p := p) (q := q + 1) (by omega) α
      (((inclusion U A V B).f (p + q + 1)).hom c))
    (w : ModuleHomology.Cycle (singularComplex (U ∩ V : Set X)) q)
    (hw : w.val = capInDegree U A V B (p := p + 1) (q := q) (by omega) η c) :
    connectingHomomorphism U V hU hV hcover q
        (ModuleHomology.cycleClass (singularComplex X) (q + 1) a) =
      -((-1 : ℤ) ^ p) • ModuleHomology.cycleClass (singularComplex (U ∩ V : Set X)) q w := by
  let S := IntegralMayerVietoris.smallSequence U V
  let b := capLift U A V B p q β γ cU cV
  let w' : ModuleHomology.Cycle (singularComplex (U ∩ V : Set X)) q := -((-1 : ℤ) ^ p) • w
  have hf : (S.f.f q).hom w'.val = (S.X₂.d (q + 1) q).hom b :=
    (congrArg (S.f.f q).hom (congrArg (fun t => -((-1 : ℤ) ^ p) • t) hw)).trans
      (intersection_cap_eq_boundary_lift U A V B p q β γ η hβ hγ c hc cU hcU cV hcV)
  have hz : (S.X₃.d (q + 1) q).hom ((S.g.f (q + 1)).hom b) = 0 :=
    (congrArg (fun m => m.hom b) (S.g.comm (q + 1) q)).trans
      ((congrArg (S.g.f q).hom hf.symm).trans
        (congrArg (fun m => (m.f q).hom w'.val) S.zero))
  let z : ModuleHomology.Cycle S.X₃ (q + 1) :=
    ModuleHomology.mkCycle S.X₃ (q + 1) ((S.g.f (q + 1)).hom b)
      ((congrArg (fun j => (S.X₃.d (q + 1) j).hom ((S.g.f (q + 1)).hom b) = 0)
        (Nat.add_sub_cancel q 1)).mpr hz)
  have hza : ModuleHomology.mapCycles (IntegralMayerVietoris.smallInclusion U V) (q + 1) z = a :=
    Subtype.ext ((ModuleHomology.mapCycles_val _ _ z).trans
      ((capLift_inclusion U A V B p q α β γ hα c cU hcU cV hcV).trans ha.symm))
  exact (congrArg (fun t => connectingHomomorphism U V hU hV hcover q
    (ModuleHomology.cycleClass (singularComplex X) (q + 1) t)) hza.symm).trans
      ((IntegralMayerVietoris.connecting_cycleClass U V hU hV hcover q z b rfl w' hf).trans
        (map_zsmul (ModuleHomology.cycleClass (singularComplex (U ∩ V : Set X)) q)
          (-((-1 : ℤ) ^ p)) w))

end Wikipedia.HopfProblem.DegreeCollapse.CommonSmallIntegralCap
