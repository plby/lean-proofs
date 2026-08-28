import Wikipedia.NoExoticSixSphere.CommonSmallCapConnectingCohomology
import Wikipedia.NoExoticSixSphere.CommonSmallUnionCap
import Wikipedia.NoExoticSixSphere.CommonSmallRelativeChains
import Wikipedia.NoExoticSixSphere.SmallCapRelativeRepresentative
import Wikipedia.NoExoticSixSphere.RelativeModExcision

/-!
# The actual relative cap connecting square

Compatible relative classes on the ambient pair and the overlap pair
give a cap square for the two original connecting maps. Subdivision
constructs the required common-small representative. The original
relative excision map identifies its constructed overlap class with
the specified compatible class; no absolute homology map is cancelled.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCapMayerVietoris

open ModTwoCapProduct (Coefficient)
open RelativeSingularHomology (overlapIn)
open SingularSubcomplex (smallInclusionMap)

variable {X : Type} [TopologicalSpace X] (U A V B : Set X)

omit [TopologicalSpace X] in
/-- The two neighborhood covers imply the overlap/union cover used by relative excision. -/
theorem overlap_union_cover (hUA : U ∪ A = Set.univ) (hVB : V ∪ B = Set.univ) :
    (U ∩ V) ∪ (A ∪ B) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro x
  by_cases h : x ∈ A ∪ B
  · exact Or.inr h
  · have h₁ : x ∈ U ∪ A := hUA ▸ Set.mem_univ x
    have h₂ : x ∈ V ∪ B := hVB ▸ Set.mem_univ x
    exact Or.inl ⟨h₁.resolve_right (fun hx => h (Or.inl hx)),
      h₂.resolve_right (fun hx => h (Or.inr hx))⟩

/-- The original identity-ambient pair map from the intersection quotient to the union quotient. -/
abbrev interToUnion := RelativeCoefficients.subsetMap Coefficient
  (show A ∩ B ⊆ A ∪ B from fun _ hx => Or.inl hx.1)

/-- The genuine cap square for compatible original relative classes. -/
theorem connecting_cap
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hA : IsOpen A) (hB : IsOpen B) (hUA : U ∪ A = Set.univ) (hVB : V ∪ B = Set.univ)
    (p q : ℕ) (a : RelativeModTwoCochains.Cohomology (A ∩ B) p)
    (F : (RelativeCoefficients.complex Coefficient (A ∩ B)).homology (p + q + 1))
    (G : (RelativeCoefficients.complex Coefficient (overlapIn (U ∩ V) (A ∪ B))).homology
      (p + q + 1))
    (hFG : homologyLinearMap
        (RelativeCoefficients.subtypePairMap Coefficient (U ∩ V) (A ∪ B)) (p + q + 1) G =
      homologyLinearMap (interToUnion A B) (p + q + 1) F) :
    ModTwoMayerVietoris.connecting U V hU hV hcover q
        (RelativeModTwoCap.capProduct (A ∩ B) p (q + 1) a F) =
      RelativeModTwoCap.capProductInDegree (overlapIn (U ∩ V) (A ∪ B))
        (p := p + 1) (q := q) (n := p + q + 1) (by omega)
        (RelativeModTwoCochains.cohomologyPullback (subtypeInclusion (U ∩ V))
          (show Set.MapsTo (subtypeInclusion (U ∩ V)) (overlapIn (U ∩ V) (A ∪ B)) (A ∪ B)
            from fun _ hx => hx) (p + 1)
          (RelativeModTwoMayerVietoris.connecting A B hA hB p a)) G := by
  obtain ⟨α, hα⟩ := SingularCohomologyFree.cocycleClass_surjective
    (RelativeModTwoCochains.complex (A ∩ B)) p a
  obtain ⟨θ, hθ⟩ := RelativeModTwoMayerVietoris.exists_connecting_union_cocycle A B hA hB p a
  obtain ⟨c, hc, hclass⟩ := CommonSmallRelative.exists_representative U A V B (A ∩ B)
    Set.inter_subset_left Set.inter_subset_right 2 (by decide)
    hU hA hUA hV hB hVB (p + q + 1) F
  let z := ModuleHomology.mkCycle (RelativeCoefficients.complex Coefficient (A ∩ B))
    (p + q + 1) (RelativeCoefficients.quotientMap Coefficient (A ∩ B) (p + q + 1)
      (((CommonSmallModTwoCap.inclusion U A V B).f (p + q + 1)).hom c)) hc
  have hθ' : SingularCohomologyFree.cocycleClass _ (p + 1) θ =
      RelativeModTwoMayerVietoris.connecting A B hA hB p
        (SingularCohomologyFree.cocycleClass _ p α) :=
    hθ.trans (congrArg (RelativeModTwoMayerVietoris.connecting A B hA hB p) hα.symm)
  obtain ⟨w, hw, hconnect⟩ :=
    CommonSmallModTwoCap.connecting_relative_cap_representative U A V B
      hU hV hcover hA hB p q α θ hθ' c z rfl
  let c' := (((SimplicialCoefficients.chains Coefficient).map
    (SingularSubcomplex.commonToOverlapSmall U A V B)).f (p + q + 1)).hom c
  have hc' : smallInclusionMap Coefficient (U ∩ V) (A ∪ B) (p + q + 1) c' =
      ((CommonSmallModTwoCap.inclusion U A V B).f (p + q + 1)).hom c :=
    congrArg (fun m => (m.f (p + q + 1)).hom c)
      (SingularSubcomplex.commonToOverlapSmall_chain_inclusion U A V B Coefficient)
  let zD := ModuleHomology.mapCycles (interToUnion A B) (p + q + 1) z
  have hzD : zD.val = RelativeCoefficients.quotientMap Coefficient (A ∪ B) (p + q + 1)
      (smallInclusionMap Coefficient (U ∩ V) (A ∪ B) (p + q + 1) c') :=
    (ModuleHomology.mapCycles_val (interToUnion A B) (p + q + 1) z).trans
      ((congrArg (fun m => (m.f (p + q + 1)).hom
        (((CommonSmallModTwoCap.inclusion U A V B).f (p + q + 1)).hom c))
        (RelativeCoefficients.projection_subsetMap Coefficient
          (show A ∩ B ⊆ A ∪ B from fun _ hx => Or.inl hx.1))).trans
            (congrArg (RelativeCoefficients.quotientMap Coefficient (A ∪ B) (p + q + 1)) hc'.symm))
  have hw' : w.val = SmallModTwoCap.capInDegree (U ∩ V) (A ∪ B)
      (p := p + 1) (q := q) (n := p + q + 1) (by omega) θ.val c' :=
    hw.trans ((congrArg (fun η => CommonSmallModTwoCap.capInDegree U A V B
      (p := p + 1) (q := q) (n := p + q + 1) (by omega) η c)
      (SmallRelativeModTwoCochains.unionCocycle_val A B (p + 1) θ)).trans
        (CommonSmallModTwoCap.capInDegree_union U A V B
          (p := p + 1) (q := q) (n := p + q + 1) (by omega) θ.val c))
  obtain ⟨b, hb, hcap⟩ := SmallModTwoCap.exists_relative_cap_class_inDegree (U ∩ V) (A ∪ B)
    (p := p + 1) (q := q) (n := p + q + 1) (by omega) θ c' zD hzD w hw'
  have hbG : b = G := by
    apply (RelativeCoefficients.modExcisionEquiv 2 (by decide) (U ∩ V) (A ∪ B)
      (hU.inter hV) (hA.union hB) (overlap_union_cover U A V B hUA hVB) (p + q + 1)).injective
    exact hb.trans ((ModuleHomology.homologyMap_cycleClass
      (interToUnion A B) (p + q + 1) z).symm.trans
      ((congrArg (homologyLinearMap (interToUnion A B) (p + q + 1)) hclass).trans hFG.symm))
  have hsource : RelativeModTwoCap.capProduct (A ∩ B) p (q + 1) a F =
      RelativeModTwoCap.homologyCap (A ∩ B) p (q + 1) α.val
        (RelativeModTwoCochains.cocycle_coboundary_zero (A ∩ B) p α)
        (ModuleHomology.cycleClass _ (p + (q + 1)) z) :=
    (congrArg (fun t => RelativeModTwoCap.capProduct (A ∩ B) p (q + 1) t F) hα.symm).trans
      ((congrArg (fun f => f F)
        (RelativeModTwoCap.capProduct_cocycleClass (A ∩ B) p (q + 1) α)).trans
        (congrArg (RelativeModTwoCap.homologyCap (A ∩ B) p (q + 1) α.val
          (RelativeModTwoCochains.cocycle_coboundary_zero (A ∩ B) p α)) hclass.symm))
  apply (congrArg (ModTwoMayerVietoris.connecting U V hU hV hcover q) hsource).trans
  apply hconnect.trans
  apply hcap.trans
  exact congrArg₂ (fun t d => RelativeModTwoCap.capProductInDegree (overlapIn (U ∩ V) (A ∪ B))
    (p := p + 1) (q := q) (n := p + q + 1) (by omega) t d)
    (congrArg (RelativeModTwoCochains.cohomologyPullback (subtypeInclusion (U ∩ V))
      (show Set.MapsTo (subtypeInclusion (U ∩ V)) (overlapIn (U ∩ V) (A ∪ B)) (A ∪ B)
        from fun _ hx => hx) (p + 1)) hθ) hbG

end NoExoticSixSphere.RelativeCapMayerVietoris
