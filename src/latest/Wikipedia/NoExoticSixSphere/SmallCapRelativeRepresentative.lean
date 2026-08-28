import Wikipedia.NoExoticSixSphere.SmallRelativeCycleLift
import Wikipedia.NoExoticSixSphere.SmallModTwoCap
import Wikipedia.NoExoticSixSphere.RelativeModTwoCapNaturality
import Wikipedia.NoExoticSixSphere.RelativeModTwoExcision
import Wikipedia.NoExoticSixSphere.RelativeModTwoCapDegree

/-!
# Localized cap as actual relative cap inside the subspace

The second summand in a small-chain decomposition is annihilated by
the relative cochain. The first summand gives a relative cycle in the
actual subspace, whose original relative cap is exactly the localized
cap chain. The resulting equality holds in the subspace homology.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.SmallModTwoCap

open ModTwoCapProduct (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)
open RelativeSingularHomology (overlapIn)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The first summand's original relative cap equals the actual localized cap chain. -/
theorem capInDegree_eq_relative_of_decomposition {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cochain V p) (c : SmallChains Coefficient U V n)
    (u : ModTwoChains.Chains U n) (v : ModTwoChains.Chains V n)
    (he : smallInclusionMap Coefficient U V n c =
      ((RelativeCoefficients.inclusion Coefficient U).f n).hom u +
        ((RelativeCoefficients.inclusion Coefficient V).f n).hom v) :
    capInDegree U V h α c = RelativeModTwoCap.capInDegree (overlapIn U V) h
      (RelativeModTwoCochains.pullback (subtypeInclusion U)
        (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) p α)
      (RelativeCoefficients.quotientMap Coefficient (overlapIn U V) n u) := by
  apply inclusion_injective U q
  let f := ModTwoCapProduct.capInDegree h (RelativeModTwoCochains.toAbsolute V p α)
  have hv : f (((RelativeCoefficients.inclusion Coefficient V).f n).hom v) = 0 :=
    RelativeModTwoCap.capInDegree_inclusion_zero V h α v
  have hleft : f (smallInclusionMap Coefficient U V n c) =
      f (((RelativeCoefficients.inclusion Coefficient U).f n).hom u) :=
    (congrArg f he).trans ((f.map_add _ _).trans
      ((congrArg (fun t => f (((RelativeCoefficients.inclusion Coefficient U).f n).hom u) + t)
        hv).trans (add_zero _)))
  have hmap := congrArg (fun m => (m.f n).hom u)
    (RelativeCoefficients.projection_mapChain Coefficient (subtypeInclusion U)
      (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx))
  have hright := (RelativeModTwoCap.spaceMap_capInDegree (subtypeInclusion U)
    (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) h α
    (RelativeCoefficients.quotientMap Coefficient (overlapIn U V) n u)).trans
      ((congrArg (RelativeModTwoCap.capInDegree V h α) hmap).trans
        (RelativeModTwoCap.capInDegree_quotientMap V h α _))
  exact (inclusion_capInDegree U V h α c).trans (hleft.trans hright.symm)

/-- The localized cap is the cap of a constructed relative cycle in the original subspace. -/
theorem exists_relative_cap_cycle (p q : ℕ) (α : RelativeModTwoCochains.Cocycle V p)
    (c : SmallChains Coefficient U V (p + q))
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient V) (p + q))
    (hz : z.val = RelativeCoefficients.quotientMap Coefficient V (p + q)
      (smallInclusionMap Coefficient U V (p + q) c)) :
    ∃ y : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient (overlapIn U V)) (p + q),
      ModuleHomology.mapCycles (RelativeCoefficients.subtypePairMap Coefficient U V) (p + q) y = z ∧
      capInDegree U V (q := q) rfl α.val c =
        (RelativeModTwoCap.capCycles (overlapIn U V) p q
          (SingularCohomologyFree.mapCocycles (RelativeModTwoCochains.excisionPullbackMap U V)
            p α).val
          (RelativeModTwoCochains.cocycle_coboundary_zero (overlapIn U V) p _) y).val := by
  obtain ⟨u, v, y, he, hy, hmap⟩ :=
    RelativeCoefficients.exists_small_relative_cycle Coefficient U V (p + q) c z hz
  let β := SingularCohomologyFree.mapCocycles (RelativeModTwoCochains.excisionPullbackMap U V) p α
  have hβ := SingularCohomologyFree.mapCocycles_val
    (RelativeModTwoCochains.excisionPullbackMap U V) p α
  have hr := (RelativeModTwoCap.capCycles_val (overlapIn U V) p q β.val
    (RelativeModTwoCochains.cocycle_coboundary_zero (overlapIn U V) p β) y).trans
      (congrArg₂ (fun δ t => RelativeModTwoCap.capInDegree (overlapIn U V) (q := q) rfl δ t) hβ hy)
  exact ⟨y, hmap, (capInDegree_eq_relative_of_decomposition U V rfl α.val c u v he).trans hr.symm⟩

/-- The localized cap class is an actual relative cap class whose pair-map image is prescribed. -/
theorem exists_relative_cap_class (p q : ℕ) (α : RelativeModTwoCochains.Cocycle V p)
    (c : SmallChains Coefficient U V (p + q))
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient V) (p + q))
    (hz : z.val = RelativeCoefficients.quotientMap Coefficient V (p + q)
      (smallInclusionMap Coefficient U V (p + q) c))
    (w : ModuleHomology.Cycle (modComplex 2 U) q)
    (hw : w.val = capInDegree U V (q := q) rfl α.val c) :
    ∃ b : (RelativeCoefficients.complex Coefficient (overlapIn U V)).homology (p + q),
      homologyLinearMap (RelativeCoefficients.subtypePairMap Coefficient U V) (p + q) b =
        ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient V) (p + q) z ∧
      ModuleHomology.cycleClass (modComplex 2 U) q w =
        RelativeModTwoCap.capProduct (overlapIn U V) p q
          (RelativeModTwoCochains.cohomologyPullback (subtypeInclusion U)
            (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) p
            (SingularCohomologyFree.cocycleClass (RelativeModTwoCochains.complex V) p α)) b := by
  obtain ⟨y, hmap, hcap⟩ := exists_relative_cap_cycle U V p q α c z hz
  let β := SingularCohomologyFree.mapCocycles (RelativeModTwoCochains.excisionPullbackMap U V) p α
  let b := ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient (overlapIn U V))
    (p + q) y
  refine ⟨b, ?_, ?_⟩
  · exact (ModuleHomology.homologyMap_cycleClass
      (RelativeCoefficients.subtypePairMap Coefficient U V) (p + q) y).trans
        (congrArg (ModuleHomology.cycleClass _ (p + q)) hmap)
  · have he := RelativeModTwoCochains.cohomologyPullback_cocycleClass (subtypeInclusion U)
      (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) p α
    have hr := (congrArg (fun a => RelativeModTwoCap.capProduct (overlapIn U V) p q a b) he).trans
      (RelativeModTwoCap.capProduct_cocycle_cycle (overlapIn U V) p q β y)
    exact (congrArg (ModuleHomology.cycleClass (modComplex 2 U) q)
      (Subtype.ext (hw.trans hcap))).trans hr.symm

/-- The same original relative cap-class comparison with only its total degree reindexed. -/
theorem exists_relative_cap_class_inDegree {p q n : ℕ} (h : p + q = n)
    (α : RelativeModTwoCochains.Cocycle V p) (c : SmallChains Coefficient U V n)
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient V) n)
    (hz : z.val = RelativeCoefficients.quotientMap Coefficient V n
      (smallInclusionMap Coefficient U V n c))
    (w : ModuleHomology.Cycle (modComplex 2 U) q) (hw : w.val = capInDegree U V h α.val c) :
    ∃ b : (RelativeCoefficients.complex Coefficient (overlapIn U V)).homology n,
      homologyLinearMap (RelativeCoefficients.subtypePairMap Coefficient U V) n b =
        ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient V) n z ∧
      ModuleHomology.cycleClass (modComplex 2 U) q w =
        RelativeModTwoCap.capProductInDegree (overlapIn U V) h
          (RelativeModTwoCochains.cohomologyPullback (subtypeInclusion U)
            (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) p
            (SingularCohomologyFree.cocycleClass (RelativeModTwoCochains.complex V) p α)) b := by
  subst n
  exact exists_relative_cap_class U V p q α c z hz w hw

end NoExoticSixSphere.SmallModTwoCap
