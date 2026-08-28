import Wikipedia.NoExoticSixSphere.CommonSmallCapConnectingLift

/-!
# The connecting formula for actual cap representatives

The native small-chain lift has the original ambient cap as its image
and the overlap cap as its lifted boundary. Applying the genuine
Mayer--Vietoris connecting map proves equality in overlap homology.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoMayerVietoris

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The original small-chain sum followed by inclusion is the original ambient sum. -/
theorem second_inclusion : (smallSequence U V).g ≫ smallInclusion U V =
    biprod.desc (RelativeCoefficients.inclusion Coefficient U)
      (RelativeCoefficients.inclusion Coefficient V) := by
  change biprod.desc
    ((SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.toSmallLeft U V))
    ((SimplicialCoefficients.chains Coefficient).map (SingularSubcomplex.toSmallRight U V)) ≫ _ = _
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, SingularSubcomplex.chainToSmallLeft_inclusion]
    exact (biprod.inl_desc (RelativeCoefficients.inclusion Coefficient U)
      (RelativeCoefficients.inclusion Coefficient V)).symm
  · simp only [biprod.inr_desc_assoc, SingularSubcomplex.chainToSmallRight_inclusion]
    exact (biprod.inr_desc (RelativeCoefficients.inclusion Coefficient U)
      (RelativeCoefficients.inclusion Coefficient V)).symm

end NoExoticSixSphere.ModTwoMayerVietoris

namespace NoExoticSixSphere.CommonSmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)
open SmallRelativeModTwoCochains (Cochain)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

/-- The actual cap lift projects to the original ambient cap of the cochain difference. -/
theorem capLift_inclusion (p q : ℕ) (α : ModTwoCapProduct.Cochain X p)
    (β : RelativeModTwoCochains.Cochain A p) (γ : RelativeModTwoCochains.Cochain B p)
    (hα : α = RelativeModTwoCochains.toAbsolute A p β - RelativeModTwoCochains.toAbsolute B p γ)
    (c : (complex U A V B).X (p + q + 1))
    (cU : SmallChains Coefficient U A (p + q + 1))
    (hcU : smallInclusionMap Coefficient U A (p + q + 1) cU =
      ((inclusion U A V B).f (p + q + 1)).hom c)
    (cV : SmallChains Coefficient V B (p + q + 1))
    (hcV : smallInclusionMap Coefficient V B (p + q + 1) cV =
      ((inclusion U A V B).f (p + q + 1)).hom c) :
    ((ModTwoMayerVietoris.smallInclusion U V).f (q + 1)).hom
        (((ModTwoMayerVietoris.smallSequence U V).g.f (q + 1)).hom
          (capLift U A V B p q β γ cU cV)) =
      ModTwoCapProduct.capInDegree (p := p) (q := q + 1) (by omega) α
        (((inclusion U A V B).f (p + q + 1)).hom c) := by
  have he := congrArg (fun m => (m.f (q + 1)).hom (capLift U A V B p q β γ cU cV))
    (ModTwoMayerVietoris.second_inclusion U V)
  apply he.trans
  apply (ChainBiproduct.desc_pair (RelativeCoefficients.inclusion Coefficient U)
    (RelativeCoefficients.inclusion Coefficient V) (q + 1) _ _).trans
  rw [map_neg]
  exact (sub_eq_add_neg _ _).symm.trans
    (SmallModTwoCap.capInDegree_difference U V A B (p := p) (q := q + 1)
      (by omega) α β γ hα _ cU hcU cV hcV).symm

/-- Genuine connecting sends an actual ambient cap cycle to its actual overlap cap cycle. -/
theorem connecting_cap_representatives (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (p q : ℕ)
    (α : ModTwoCapProduct.Cochain X p)
    (β : RelativeModTwoCochains.Cochain A p) (γ : RelativeModTwoCochains.Cochain B p)
    (hα : α = RelativeModTwoCochains.toAbsolute A p β - RelativeModTwoCochains.toAbsolute B p γ)
    (η : Cochain A B (p + 1))
    (hβ : ((RelativeModTwoMayerVietoris.smallRestrictionLeft A B).f (p + 1)).hom η =
      RelativeModTwoCochains.coboundary A β)
    (hγ : ((RelativeModTwoMayerVietoris.smallRestrictionRight A B).f (p + 1)).hom η =
      RelativeModTwoCochains.coboundary B γ)
    (c : (complex U A V B).X (p + q + 1))
    (hc : ((inclusion U A V B).f (p + q)).hom
        (((complex U A V B).d (p + q + 1) (p + q)).hom c) ∈
      LinearMap.range ((RelativeCoefficients.inclusion Coefficient (A ∩ B)).f (p + q)).hom)
    (cU : SmallChains Coefficient U A (p + q + 1))
    (hcU : smallInclusionMap Coefficient U A (p + q + 1) cU =
      ((inclusion U A V B).f (p + q + 1)).hom c)
    (cV : SmallChains Coefficient V B (p + q + 1))
    (hcV : smallInclusionMap Coefficient V B (p + q + 1) cV =
      ((inclusion U A V B).f (p + q + 1)).hom c)
    (a : ModuleHomology.Cycle (modComplex 2 X) (q + 1))
    (ha : a.val = ModTwoCapProduct.capInDegree (p := p) (q := q + 1) (by omega) α
      (((inclusion U A V B).f (p + q + 1)).hom c))
    (w : ModuleHomology.Cycle (modComplex 2 (U ∩ V : Set X)) q)
    (hw : w.val = capInDegree U A V B (p := p + 1) (q := q) (by omega) η c) :
    ModTwoMayerVietoris.connecting U V hU hV hcover q
        (ModuleHomology.cycleClass (modComplex 2 X) (q + 1) a) =
      ModuleHomology.cycleClass (modComplex 2 (U ∩ V : Set X)) q w := by
  let S := ModTwoMayerVietoris.smallSequence U V
  let b := capLift U A V B p q β γ cU cV
  have hf : (S.f.f q).hom w.val = (S.X₂.d (q + 1) q).hom b :=
    (congrArg (S.f.f q).hom hw).trans
      (intersection_cap_eq_boundary_lift U A V B p q β γ η hβ hγ c hc cU hcU cV hcV)
  have hz : (S.X₃.d (q + 1) q).hom ((S.g.f (q + 1)).hom b) = 0 :=
    (congrArg (fun m => m.hom b) (S.g.comm (q + 1) q)).trans
      ((congrArg (S.g.f q).hom hf.symm).trans
        (congrArg (fun m => (m.f q).hom w.val) S.zero))
  let z : ModuleHomology.Cycle S.X₃ (q + 1) :=
    ModuleHomology.mkCycle S.X₃ (q + 1) ((S.g.f (q + 1)).hom b)
      ((congrArg (fun j => (S.X₃.d (q + 1) j).hom ((S.g.f (q + 1)).hom b) = 0)
        (Nat.add_sub_cancel q 1)).mpr hz)
  have hza : ModuleHomology.mapCycles (ModTwoMayerVietoris.smallInclusion U V) (q + 1) z = a :=
    Subtype.ext ((ModuleHomology.mapCycles_val _ _ z).trans
      ((capLift_inclusion U A V B p q α β γ hα c cU hcU cV hcV).trans ha.symm))
  exact (congrArg (fun t => ModTwoMayerVietoris.connecting U V hU hV hcover q
    (ModuleHomology.cycleClass (modComplex 2 X) (q + 1) t)) hza.symm).trans
      (ModTwoMayerVietoris.connecting_cycleClass U V hU hV hcover q z b rfl w hf)

end NoExoticSixSphere.CommonSmallModTwoCap
