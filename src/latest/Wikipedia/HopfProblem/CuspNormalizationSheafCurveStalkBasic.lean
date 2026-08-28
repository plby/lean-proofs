import Wikipedia.HopfProblem.CuspNormalizationSheafCuspTerms
import Wikipedia.HopfProblem.CuspNormalizationSheafForgetStalk
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Actual stalks of the pushed-forward double-curve sheaves

The double-curve map is the actual subspace inclusion. Its canonical
pushforward stalk map is an isomorphism at every point of the curve.
After the proved forgetful comparison its target is the actual
ring-valued holomorphic stalk. Away from the closed curve the actual
pushforward stalk is zero, proved using its empty fibre.
-/

noncomputable section

open Set Topology TopologicalSpace Opposite CategoryTheory Limits
open scoped ContDiff Manifold AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk

open CuspQuotient ToricCharts ToricSpace NormalizationCurves SheafResolution

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual double-curve inclusion has the induced subspace topology. -/
theorem sourceCurveMap_isInducing (k : Fin 3) :
    IsInducing (sourceCurveMap C ε hε k) :=
  IsInducing.subtypeVal.codRestrict
    (fun d => doubleCurve_subset_central C ε hε (sourceEdgeIndex k) d.property)

/-- The actual source curve is a closed subspace of the actual central fibre. -/
theorem sourceCurveMap_isClosedMap (k : Fin 3) :
    IsClosedMap (sourceCurveMap C ε hε k) :=
  curveInclusion_isClosedMap C ε hε (sourceEdgeIndex k)

/-- The actual source-curve inclusion is injective. -/
theorem sourceCurveMap_injective (k : Fin 3) :
    Function.Injective (sourceCurveMap C ε hε k) :=
  curveInclusion_injective C ε hε (sourceEdgeIndex k)

variable (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual additive direct-image stalk at a curve point is
canonically its actual ring-valued holomorphic stalk. -/
def curvePointStalkEquiv (k : Fin 3) (d : sourceDoubleCurve C ε hε k)
    (x : CentralSpace C ε) (hd : sourceCurveMap C ε hε k d = x) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    (curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x ≃+
      (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, ℂ)
        (sourceDoubleCurve C ε hε k)).stalk d := by
  letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let F := (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ)
    (sourceDoubleCurve C ε hε k)).presheaf
  letI : IsIso (F.stalkPushforward AddCommGrpCat (sourceCurveMap C ε hε k) d) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat (sourceCurveMap_isInducing C ε hε k) F d
  let φ := SheafFiniteStalk.pushforwardStalkComponent (sourceCurveMap C ε hε k)
    F x ⟨d, hd⟩
  letI : IsIso φ := by
    dsimp [φ, SheafFiniteStalk.pushforwardStalkComponent]
    infer_instance
  exact (asIso φ).addCommGroupIsoToAddEquiv.trans
    (SheafForgetStalk.stalkAddEquiv
      (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)) d)

/-- The point of the actual curve lies in the inverse image of each
neighbourhood of its image in the central fibre. -/
theorem curvePoint_mem_preimage (k : Fin 3) (d : sourceDoubleCurve C ε hε k)
    (x : CentralSpace C ε) (hd : sourceCurveMap C ε hε k d = x)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U) :
    d ∈ (Opens.map (sourceCurveMap C ε hε k)).obj U :=
  SheafFiniteStalk.fiber_mem_preimage (sourceCurveMap C ε hε k) x ⟨d, hd⟩ U hxU

/-- The canonical comparison preserves the actual section germ at the
chosen source-curve point. -/
@[simp] theorem curvePointStalkEquiv_germ (k : Fin 3)
    (d : sourceDoubleCurve C ε hε k) (x : CentralSpace C ε)
    (hd : sourceCurveMap C ε hε k d = x)
    (U : Opens (CentralSpace C ε)) (hxU : x ∈ U) :
    letI := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
    ∀ f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)
      ((Opens.map (sourceCurveMap C ε hε k)).obj U),
    curvePointStalkEquiv C ε hε hε1 hC hR k d x hd
        ((curveSheaf C ε hε hε1 hC hR k).presheaf.germ U x hxU f) =
      (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, ℂ)
        (sourceDoubleCurve C ε hε k)).germ
        ((Opens.map (sourceCurveMap C ε hε k)).obj U) d
        (curvePoint_mem_preimage C ε hε k d x hd U hxU) f := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  intro f
  exact (congrArg (SheafForgetStalk.stalkAddEquiv
      (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)) d)
    (SheafFiniteStalk.pushforwardStalkComponent_germ (sourceCurveMap C ε hε k)
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ)
        (sourceDoubleCurve C ε hε k)).presheaf x ⟨d, hd⟩ U hxU f)).trans
    (SheafForgetStalk.stalkAddEquiv_germ
      (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k))
      ((Opens.map (sourceCurveMap C ε hε k)).obj U) d
      (curvePoint_mem_preimage C ε hε k d x hd U hxU) f)

/-- Away from the actual closed double curve its actual direct-image
stalk is zero. The proof uses the empty fibre and the proved closed-map
injectivity, rather than an assumed stalk formula. -/
theorem curveStalk_isZero_of_not_mem (k : Fin 3) (x : CentralSpace C ε)
    (hx : x.val ∉ sourceDoubleCurve C ε hε k) :
    IsZero ((curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x) := by
  let := curveChartedSpace C ε hε hε1 hC hR (sourceEdgeIndex k)
  let : IsEmpty (sourceCurveMap C ε hε k ⁻¹' {x}) := ⟨fun d => by
    apply hx
    have hdx : d.val.val = x.val := congrArg Subtype.val d.property
    exact hdx ▸ d.val.property⟩
  have hinj := SheafFiniteStalk.pushforwardStalkHom_injective
    (sourceCurveMap C ε hε k) (sourceCurveMap_isClosedMap C ε hε k)
    (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ) (sourceDoubleCurve C ε hε k)) x
  let : Subsingleton ((curveSheaf C ε hε hε1 hC hR k).presheaf.stalk x) :=
    hinj.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

end Wikipedia.HopfProblem.CuspNormalization.SheafCurveStalk
