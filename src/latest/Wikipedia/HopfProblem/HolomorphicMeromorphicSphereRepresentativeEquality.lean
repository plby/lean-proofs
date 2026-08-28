import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereRepresentativeLocal
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereRepresentativeEqualityAnalytic

/-!
# Ordinary sphere representatives determine the native meromorphic section

Agreement on one punctured coordinate neighborhood gives equality of
the actual fraction germs: take common local numerator/denominator
presentations, use isolated zeros of the nonzero denominator germs,
and apply the analytic identity principle to their cross product.
The native connected-domain identity theorem then gives equality of
the original meromorphic sections on the entire sphere.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereRepresentative

/-- Scalar agreement of two actual local fractions implies equality in
the original meromorphic stalk, including at a common denominator zero. -/
theorem fraction_eq_of_chart_fraction_eventuallyEq (U : Opens RiemannSphere)
    (p q r s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U)
    (b : Bool) (z : ℂ) (hz : RiemannSphere.standardCharts.affineMap b z ∈ U)
    (hq : holomorphicGerm 𝓘(ℂ) RiemannSphere U
      ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ q ≠ 0)
    (hs : holomorphicGerm 𝓘(ℂ) RiemannSphere U
      ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ s ≠ 0)
    (he : (fun w => chartCoefficient U p b w / chartCoefficient U q b w)
      =ᶠ[𝓝[≠] z] (fun w => chartCoefficient U r b w / chartCoefficient U s b w)) :
    fraction 𝓘(ℂ) RiemannSphere U p q
        ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ =
      fraction 𝓘(ℂ) RiemannSphere U r s
        ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ := by
  apply (fraction_eq_iff_cross_germ_zero 𝓘(ℂ) RiemannSphere U p q r s
    ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ hq hs).mpr
  apply (holomorphicGerm_eq_zero_iff_chartCoefficient_eventuallyEq_zero
    U (p * s - r * q) b z hz).mpr
  have hq' : ¬ chartCoefficient U q b =ᶠ[𝓝 z] 0 := fun h =>
    hq ((holomorphicGerm_eq_zero_iff_chartCoefficient_eventuallyEq_zero U q b z hz).mpr h)
  have hs' : ¬ chartCoefficient U s b =ᶠ[𝓝 z] 0 := fun h =>
    hs ((holomorphicGerm_eq_zero_iff_chartCoefficient_eventuallyEq_zero U s b z hz).mpr h)
  have hcross := analytic_cross_eventuallyEq_zero_of_fraction_eventuallyEq
    (chartCoefficient_analyticAt U p b z hz) (chartCoefficient_analyticAt U q b z hz)
    (chartCoefficient_analyticAt U r b z hz) (chartCoefficient_analyticAt U s b z hz)
    hq' hs' he
  have hU : ∀ᶠ w in 𝓝 z, RiemannSphere.standardCharts.affineMap b w ∈ U :=
    (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).continuous.continuousAt.eventually
      (U.isOpen.mem_nhds hz)
  filter_upwards [hU, hcross] with w hw hcw
  rw [chartCoefficient_apply U (p * s - r * q) b w hw]
  change p ⟨_, hw⟩ * s ⟨_, hw⟩ - r ⟨_, hw⟩ * q ⟨_, hw⟩ = 0
  simpa only [chartCoefficient_apply U p b w hw, chartCoefficient_apply U q b w hw,
    chartCoefficient_apply U r b w hw, chartCoefficient_apply U s b w hw,
    Pi.zero_apply] using hcw

/-- One punctured coordinate neighborhood determines the actual native
meromorphic germ of two arbitrary locally represented sections. -/
theorem germ_eq_of_chartValue_eventuallyEq (s t : SphereFunction) (b : Bool) (z : ℂ)
    (he : chartValue s b =ᶠ[𝓝[≠] z] chartValue t b) :
    s ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩ =
      t ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩ := by
  obtain ⟨U, _, hz, p, q, r, a, hq, ha, hs, ht⟩ :=
    common_local_representation 𝓘(ℂ) RiemannSphere s t
      ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩
  have hs' := chartValue_eventuallyEq_local_fraction s U p q b z hz (hq ⟨_, hz⟩) hs
  have ht' := chartValue_eventuallyEq_local_fraction t U r a b z hz (ha ⟨_, hz⟩) ht
  have hfrac := fraction_eq_of_chart_fraction_eventuallyEq U p q r a b z hz
    (hq ⟨_, hz⟩) (ha ⟨_, hz⟩) (hs'.symm.trans (he.trans ht'))
  exact (hs ⟨_, hz⟩).trans (hfrac.trans (ht ⟨_, hz⟩).symm)

/-- The original meromorphic function on the sphere is determined by
its ordinary representative on any one punctured affine neighborhood. -/
theorem eq_of_chartValue_eventuallyEq (s t : SphereFunction) (b : Bool) (z : ℂ)
    (he : chartValue s b =ᶠ[𝓝[≠] z] chartValue t b) : s = t := by
  let : PreconnectedSpace (⊤ : Opens RiemannSphere) :=
    Subtype.preconnectedSpace isPreconnected_univ
  exact section_eq_of_germ_eq 𝓘(ℂ) RiemannSphere s t
    ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩
    (germ_eq_of_chartValue_eventuallyEq s t b z he)

/-- Equality of finite-coordinate representatives near one finite point
forces equality of the genuine native meromorphic functions. -/
theorem eq_of_finiteValue_eventuallyEq (s t : SphereFunction) (z : ℂ)
    (he : finiteValue s =ᶠ[𝓝[≠] z] finiteValue t) : s = t :=
  eq_of_chartValue_eventuallyEq s t false z he

/-- The ordinary finite-coordinate representative forgets no native
meromorphic function, despite its harmless convention for pole values. -/
theorem finiteValue_injective : _root_.Function.Injective finiteValue := by
  intro s t h
  apply eq_of_finiteValue_eventuallyEq s t 0
  exact Filter.Eventually.of_forall fun z => congrFun h z

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereRepresentative
