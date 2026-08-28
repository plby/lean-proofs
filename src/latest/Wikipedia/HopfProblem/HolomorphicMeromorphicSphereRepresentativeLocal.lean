import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereRepresentativeBasic
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Genuine local fraction representatives of native sphere values

At every point of either actual affine chart, a native meromorphic
section has a holomorphic local numerator and a genuinely nonzero
denominator germ.  The ordinary value is their quotient wherever the
denominator value is nonzero.  Isolated zeros then give equality on a
punctured coordinate neighborhood, which is the germ notion used by
Mathlib's scalar `MeromorphicAt`.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereRepresentative

/-- On the cozero set of a literal denominator, native ordinary values
are exactly the scalar quotient of the actual chart coefficients. -/
theorem chartValue_eq_local_fraction (s : SphereFunction) (U : Opens RiemannSphere)
    (p q : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (b : Bool) (z : ℂ)
    (hz : RiemannSphere.standardCharts.affineMap b z ∈ U)
    (hs : s ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩ =
      fraction 𝓘(ℂ) RiemannSphere U p q
        ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩)
    (hq : chartCoefficient U q b z ≠ 0) :
    chartValue s b z = chartCoefficient U p b z / chartCoefficient U q b z := by
  rw [chartCoefficient_apply U q b z hz] at hq
  rw [chartCoefficient_apply U p b z hz, chartCoefficient_apply U q b z hz]
  exact value_eq_local_fraction 𝓘(ℂ) RiemannSphere s p q
    (RiemannSphere.standardCharts.affineMap b z) (by trivial) hz hs hq

/-- Every literal local fraction agrees with native values on a punctured
chart neighborhood, including when the denominator vanishes at its center. -/
theorem chartValue_eventuallyEq_local_fraction (s : SphereFunction)
    (U : Opens RiemannSphere)
    (p q : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (b : Bool) (z : ℂ)
    (hz : RiemannSphere.standardCharts.affineMap b z ∈ U)
    (hq : holomorphicGerm 𝓘(ℂ) RiemannSphere U
      ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ q ≠ 0)
    (hs : ∀ y : U, s ⟨y.val, by trivial⟩ = fraction 𝓘(ℂ) RiemannSphere U p q y) :
    chartValue s b =ᶠ[𝓝[≠] z]
      (fun w => chartCoefficient U p b w / chartCoefficient U q b w) := by
  have hU : ∀ᶠ w in 𝓝 z, RiemannSphere.standardCharts.affineMap b w ∈ U :=
    (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).continuous.continuousAt.eventually
      (U.isOpen.mem_nhds hz)
  filter_upwards [hU.filter_mono nhdsWithin_le_nhds,
    chartCoefficient_eventually_ne_zero U q b z hz hq] with w hw hqw
  exact chartValue_eq_local_fraction s U p q b w hw (hs ⟨_, hw⟩) hqw

/-- A native section supplies actual scalar analytic numerator and
denominator germs in each chart; they are derived from its local fractions. -/
theorem exists_chartValue_local_fraction (s : SphereFunction) (b : Bool) (z : ℂ) :
    ∃ p q : ℂ → ℂ, AnalyticAt ℂ p z ∧ AnalyticAt ℂ q z ∧
      ¬ q =ᶠ[𝓝 z] 0 ∧
        chartValue s b =ᶠ[𝓝[≠] z] (fun w => p w / q w) := by
  obtain ⟨U, _, hz, p, q, hq, hs⟩ := local_representation 𝓘(ℂ) RiemannSphere s
    ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩
  refine ⟨chartCoefficient U p b, chartCoefficient U q b,
    chartCoefficient_analyticAt U p b z hz, chartCoefficient_analyticAt U q b z hz, ?_, ?_⟩
  · intro hzero
    exact hq ⟨_, hz⟩
      ((holomorphicGerm_eq_zero_iff_chartCoefficient_eventuallyEq_zero U q b z hz).mpr hzero)
  · exact chartValue_eventuallyEq_local_fraction s U p q b z hz (hq ⟨_, hz⟩) hs

/-- The scalar ordinary representative is genuinely meromorphic in every actual sphere chart. -/
theorem chartValue_meromorphicAt (s : SphereFunction) (b : Bool) (z : ℂ) :
    MeromorphicAt (chartValue s b) z := by
  obtain ⟨p, q, hp, hq, _, he⟩ := exists_chartValue_local_fraction s b z
  exact (hp.meromorphicAt.div hq.meromorphicAt).congr he.symm

/-- The finite-plane ordinary representative of every native section is meromorphic everywhere. -/
theorem finiteValue_meromorphicOn (s : SphereFunction) :
    MeromorphicOn (finiteValue s) univ :=
  fun z _ => chartValue_meromorphicAt s false z

/-- The reciprocal-plane representative is meromorphic everywhere, including at infinity. -/
theorem infinityValue_meromorphicOn (s : SphereFunction) :
    MeromorphicOn (infinityValue s) univ :=
  fun z _ => chartValue_meromorphicAt s true z

/-- The scalar expression obtained from the finite representative by inversion
is meromorphic at zero, by exact agreement with the actual infinity chart off zero. -/
theorem finiteValue_comp_inv_meromorphicAt_zero (s : SphereFunction) :
    MeromorphicAt (fun z : ℂ => finiteValue s z⁻¹) 0 := by
  apply (chartValue_meromorphicAt s true 0).congr
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact infinityValue_eq_finiteValue_inv s z hz

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereRepresentative
