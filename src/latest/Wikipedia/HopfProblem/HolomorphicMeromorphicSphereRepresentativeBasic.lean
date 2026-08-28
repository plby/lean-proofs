import Wikipedia.HopfProblem.HolomorphicMeromorphicField
import Wikipedia.HopfProblem.HolomorphicMeromorphicValue
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1ChartsPullback
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Ordinary representatives in the two actual sphere coordinates

The functions here are ordinary values of the already constructed native
meromorphic section.  They do not define meromorphy and do not discard
the fraction germs retained by that section.  Holomorphic local
coefficients are compared to their original categorical stalk germs
using the actual open-embedding sphere parametrizations.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereRepresentative

/-- All locally meromorphic sections on the original sphere. -/
abbrev SphereFunction := Function 𝓘(ℂ) RiemannSphere

/-- The canonical ordinary value in an actual affine sphere coordinate. -/
def chartValue (s : SphereFunction) (b : Bool) (z : ℂ) : ℂ :=
  value 𝓘(ℂ) RiemannSphere s ⟨RiemannSphere.standardCharts.affineMap b z, by trivial⟩

/-- The ordinary representative in the finite complex-plane chart. -/
def finiteValue (s : SphereFunction) (z : ℂ) : ℂ :=
  value 𝓘(ℂ) RiemannSphere s ⟨(z : RiemannSphere), by trivial⟩

/-- The ordinary representative in the reciprocal chart, including its origin at infinity. -/
def infinityValue (s : SphereFunction) (u : ℂ) : ℂ :=
  value 𝓘(ℂ) RiemannSphere s ⟨RiemannSphere.infinityParametrization u, by trivial⟩

@[simp] theorem chartValue_false (s : SphereFunction) : chartValue s false = finiteValue s := rfl

@[simp] theorem chartValue_true (s : SphereFunction) : chartValue s true = infinityValue s := rfl

/-- The native ordinary representatives obey the actual reciprocal transition exactly. -/
theorem infinityValue_eq_finiteValue_inv (s : SphereFunction) (u : ℂ) (hu : u ≠ 0) :
    infinityValue s u = finiteValue s u⁻¹ := by
  unfold infinityValue
  rw [RiemannSphere.infinityParametrization_of_ne hu]
  rfl

/-- A local holomorphic section in either of the two actual sphere coordinates. -/
def chartCoefficient (U : Opens RiemannSphere)
    (p : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (b : Bool) (z : ℂ) : ℂ :=
  HolomorphicFunctionSheaf.SphereH1.sectionExtend U p
    (RiemannSphere.standardCharts.affineMap b z)

@[simp] theorem chartCoefficient_false (U : Opens RiemannSphere)
    (p : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    chartCoefficient U p false = HolomorphicFunctionSheaf.SphereH1.finiteCoefficient U p := rfl

@[simp] theorem chartCoefficient_true (U : Opens RiemannSphere)
    (p : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    chartCoefficient U p true = HolomorphicFunctionSheaf.SphereH1.infinityCoefficient U p := rfl

@[simp] theorem chartCoefficient_apply (U : Opens RiemannSphere)
    (p : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (b : Bool) (z : ℂ)
    (hz : RiemannSphere.standardCharts.affineMap b z ∈ U) :
    chartCoefficient U p b z = p ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ :=
  HolomorphicFunctionSheaf.SphereH1.sectionExtend_apply U p _ hz

/-- Every local coefficient is analytic on the genuine coordinate preimage of its domain. -/
theorem chartCoefficient_analyticAt (U : Opens RiemannSphere)
    (p : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (b : Bool) (z : ℂ)
    (hz : RiemannSphere.standardCharts.affineMap b z ∈ U) :
    AnalyticAt ℂ (chartCoefficient U p b) z := by
  cases b
  · exact HolomorphicFunctionSheaf.SphereH1.finiteCoefficient_analyticAt U p z hz
  · exact HolomorphicFunctionSheaf.SphereH1.infinityCoefficient_analyticAt U p z hz

/-- The actual holomorphic stalk germ is zero precisely when its actual affine
coefficient vanishes on a neighborhood. -/
theorem holomorphicGerm_eq_zero_iff_chartCoefficient_eventuallyEq_zero
    (U : Opens RiemannSphere)
    (p : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (b : Bool) (z : ℂ)
    (hz : RiemannSphere.standardCharts.affineMap b z ∈ U) :
    holomorphicGerm 𝓘(ℂ) RiemannSphere U
        ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ p = 0 ↔
      chartCoefficient U p b =ᶠ[𝓝 z] 0 := by
  change (HolomorphicFunctionSheaf.presheaf 𝓘(ℂ) RiemannSphere).germ U
    (RiemannSphere.standardCharts.affineMap b z) hz p = 0 ↔ _
  rw [HolomorphicFunctionSheaf.germ_eq_zero_iff_extend_eventuallyEq_zero]
  rw [← (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).map_nhds_eq z]
  rfl

/-- A genuinely nonzero denominator germ has no zeros in a small punctured
coordinate neighborhood.  This uses the one-variable isolated-zero theorem. -/
theorem chartCoefficient_eventually_ne_zero (U : Opens RiemannSphere)
    (q : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) (b : Bool) (z : ℂ)
    (hz : RiemannSphere.standardCharts.affineMap b z ∈ U)
    (hq : holomorphicGerm 𝓘(ℂ) RiemannSphere U
      ⟨RiemannSphere.standardCharts.affineMap b z, hz⟩ q ≠ 0) :
    ∀ᶠ w in 𝓝[≠] z, chartCoefficient U q b w ≠ 0 := by
  have h := (chartCoefficient_analyticAt U q b z hz).eventually_eq_zero_or_eventually_ne_zero
  apply h.resolve_left
  intro hzero
  exact hq ((holomorphicGerm_eq_zero_iff_chartCoefficient_eventuallyEq_zero U q b z hz).mpr hzero)

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereRepresentative
