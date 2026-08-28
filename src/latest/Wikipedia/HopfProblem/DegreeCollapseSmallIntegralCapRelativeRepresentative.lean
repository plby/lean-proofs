import Wikipedia.NoExoticSixSphere.SmallRelativeCycleLift
import Wikipedia.HopfProblem.DegreeCollapseSmallIntegralCap
import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapNaturality

/-!
# Localized integral cap as actual relative cap inside the subspace

The second summand in a small-chain decomposition is annihilated by
the relative cochain. The first summand gives a relative cycle in the
actual subspace, whose original relative cap is exactly the localized
cap chain. The resulting equality holds in the subspace homology.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris NoExoticSixSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.SmallIntegralCap

open IntegralCap (Coefficient)
open SingularSubcomplex (SmallChains smallInclusionMap)
open RelativeSingularHomology (overlapIn)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The original relative cochain pullback for the subtype inclusion. -/
abbrev subtypePullbackMap := RelativeIntegralCap.pullbackMap (subtypeInclusion U)
  (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx)

/-- The first summand's original relative cap equals the actual localized cap chain. -/
theorem capInDegree_eq_relative_of_decomposition {p q n : ℕ} (h : p + q = n)
    (α : RelativeIntegralCap.Cochain V p) (c : SmallChains Coefficient U V n)
    (u : Chains U n) (v : Chains V n)
    (he : smallInclusionMap Coefficient U V n c =
      ((RelativeCoefficients.inclusion Coefficient U).f n).hom u +
        ((RelativeCoefficients.inclusion Coefficient V).f n).hom v) :
    capInDegree U V h α c = RelativeIntegralCap.capInDegree (overlapIn U V) h
      (RelativeIntegralCap.pullback (subtypeInclusion U)
        (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) p α)
      (RelativeCoefficients.quotientMap Coefficient (overlapIn U V) n u) := by
  apply inclusion_injective U q
  let f := IntegralCap.capInDegree h (RelativeIntegralCap.toAbsolute V p α)
  have hv : f (((RelativeCoefficients.inclusion Coefficient V).f n).hom v) = 0 :=
    RelativeIntegralCap.cap_inclusion_zero V h α v
  have hleft : f (smallInclusionMap Coefficient U V n c) =
      f (((RelativeCoefficients.inclusion Coefficient U).f n).hom u) :=
    (congrArg f he).trans ((f.map_add _ _).trans
      ((congrArg (fun t => f (((RelativeCoefficients.inclusion Coefficient U).f n).hom u) + t)
        hv).trans (add_zero _)))
  have hmap := congrArg (fun m => (m.f n).hom u)
    (RelativeCoefficients.projection_mapChain Coefficient (subtypeInclusion U)
      (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx))
  have hright := (RelativeIntegralCap.chainMap_capInDegree (subtypeInclusion U)
    (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) h α
    (RelativeCoefficients.quotientMap Coefficient (overlapIn U V) n u)).trans
      ((congrArg (RelativeIntegralCap.capInDegree V h α) hmap).trans
        (RelativeIntegralCap.capInDegree_quotientMap V h α _))
  exact (inclusion_capInDegree U V h α c).trans (hleft.trans hright.symm)

/-- The localized cap is the cap of a constructed relative cycle in the original subspace. -/
theorem exists_relative_cap_cycle (p q : ℕ) (α : RelativeIntegralCap.Cocycle V p)
    (c : SmallChains Coefficient U V (p + q))
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient V) (p + q))
    (hz : z.val = RelativeCoefficients.quotientMap Coefficient V (p + q)
      (smallInclusionMap Coefficient U V (p + q) c)) :
    ∃ y : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient (overlapIn U V)) (p + q),
      ModuleHomology.mapCycles (RelativeCoefficients.subtypePairMap Coefficient U V) (p + q) y = z ∧
      capInDegree U V (q := q) rfl α.val c =
        (RelativeIntegralCap.capCycles (overlapIn U V) p q
          (SingularCohomologyFree.mapCocycles (subtypePullbackMap U V)
            p α).val
          (RelativeIntegralCap.cocycle_coboundary_zero (overlapIn U V) p _) y).val := by
  obtain ⟨u, v, y, he, hy, hmap⟩ :=
    RelativeCoefficients.exists_small_relative_cycle Coefficient U V (p + q) c z hz
  let β := SingularCohomologyFree.mapCocycles (subtypePullbackMap U V) p α
  have hβ := SingularCohomologyFree.mapCocycles_val
    (subtypePullbackMap U V) p α
  have hr := (RelativeIntegralCap.capCycles_val (overlapIn U V) p q β.val
    (RelativeIntegralCap.cocycle_coboundary_zero (overlapIn U V) p β) y).trans
      (congrArg₂
        (fun δ t => RelativeIntegralCap.capInDegree (overlapIn U V) (q := q) rfl δ t) hβ hy)
  exact ⟨y, hmap, (capInDegree_eq_relative_of_decomposition U V rfl α.val c u v he).trans hr.symm⟩

/-- The localized cap class is an actual relative cap class whose pair-map image is prescribed. -/
theorem exists_relative_cap_class (p q : ℕ) (α : RelativeIntegralCap.Cocycle V p)
    (c : SmallChains Coefficient U V (p + q))
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient V) (p + q))
    (hz : z.val = RelativeCoefficients.quotientMap Coefficient V (p + q)
      (smallInclusionMap Coefficient U V (p + q) c))
    (w : ModuleHomology.Cycle (singularComplex U) q)
    (hw : w.val = capInDegree U V (q := q) rfl α.val c) :
    ∃ b : (RelativeCoefficients.complex Coefficient (overlapIn U V)).homology (p + q),
      homologyLinearMap (RelativeCoefficients.subtypePairMap Coefficient U V) (p + q) b =
        ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient V) (p + q) z ∧
      ModuleHomology.cycleClass (singularComplex U) q w =
        RelativeIntegralCap.capProduct (overlapIn U V) p q
          (RelativeIntegralCap.cohomologyPullback (subtypeInclusion U)
            (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) p
            (SingularCohomologyFree.cocycleClass
              (RelativeIntegralCap.cochainComplex V) p α)) b := by
  obtain ⟨y, hmap, hcap⟩ := exists_relative_cap_cycle U V p q α c z hz
  let β := SingularCohomologyFree.mapCocycles (subtypePullbackMap U V) p α
  let b := ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient (overlapIn U V))
    (p + q) y
  refine ⟨b, ?_, ?_⟩
  · exact (ModuleHomology.homologyMap_cycleClass
      (RelativeCoefficients.subtypePairMap Coefficient U V) (p + q) y).trans
        (congrArg (ModuleHomology.cycleClass _ (p + q)) hmap)
  · have he := RelativeIntegralCap.cohomologyPullback_cocycleClass (subtypeInclusion U)
      (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) p α
    have hr := (congrArg (fun a => RelativeIntegralCap.capProduct (overlapIn U V) p q a b) he).trans
      (RelativeIntegralCap.capProduct_cocycle_cycle (overlapIn U V) p q β y)
    exact (congrArg (ModuleHomology.cycleClass (singularComplex U) q)
      (Subtype.ext (hw.trans hcap))).trans hr.symm

/-- The same original relative cap-class comparison with only its total degree reindexed. -/
theorem exists_relative_cap_class_inDegree {p q n : ℕ} (h : p + q = n)
    (α : RelativeIntegralCap.Cocycle V p) (c : SmallChains Coefficient U V n)
    (z : ModuleHomology.Cycle (RelativeCoefficients.complex Coefficient V) n)
    (hz : z.val = RelativeCoefficients.quotientMap Coefficient V n
      (smallInclusionMap Coefficient U V n c))
    (w : ModuleHomology.Cycle (singularComplex U) q) (hw : w.val = capInDegree U V h α.val c) :
    ∃ b : (RelativeCoefficients.complex Coefficient (overlapIn U V)).homology n,
      homologyLinearMap (RelativeCoefficients.subtypePairMap Coefficient U V) n b =
        ModuleHomology.cycleClass (RelativeCoefficients.complex Coefficient V) n z ∧
      ModuleHomology.cycleClass (singularComplex U) q w =
        RelativeIntegralCap.capProductInDegree (overlapIn U V) h
          (RelativeIntegralCap.cohomologyPullback (subtypeInclusion U)
            (show Set.MapsTo (subtypeInclusion U) (overlapIn U V) V from fun _ hx => hx) p
            (SingularCohomologyFree.cocycleClass
              (RelativeIntegralCap.cochainComplex V) p α)) b := by
  subst n
  exact exists_relative_cap_class U V p q α c z hz w hw

end Wikipedia.HopfProblem.DegreeCollapse.SmallIntegralCap
