import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Charts

/-!
# Actual affine open sets and reciprocal-coordinate sections

These are the open sets of the constructed two-chart sphere atlas.
An analytic coefficient on the reciprocal-coordinate preimage of any
subopen set gives an actual holomorphic section on that same subopen
set.  This local construction is used for the sheaf frame at infinity.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

open RiemannSphere

/-- The actual finite affine chart, the complement of infinity. -/
def finiteChart : Opens RiemannSphere :=
  ⟨range ((↑) : ℂ → RiemannSphere),
    (standardCharts.affineMap_isOpenEmbedding false).isOpen_range⟩

/-- The actual reciprocal affine chart, the complement of the finite origin. -/
def infinityChart : Opens RiemannSphere :=
  ⟨range infinityParametrization, (standardCharts.affineMap_isOpenEmbedding true).isOpen_range⟩

@[simp] theorem mem_finiteChart (p : RiemannSphere) :
    p ∈ finiteChart ↔ p ≠ (∞ : RiemannSphere) := by
  change p ∈ range standardCharts.left ↔ _
  rw [standardCharts.range_left]
  change p ≠ infinityParametrization 0 ↔ _
  rw [infinityParametrization_zero]

@[simp] theorem mem_infinityChart (p : RiemannSphere) :
    p ∈ infinityChart ↔ p ≠ ((0 : ℂ) : RiemannSphere) := by
  change p ∈ range standardCharts.right ↔ _
  rw [standardCharts.range_right]
  rfl

@[simp] theorem coe_mem_finiteChart (z : ℂ) : (z : RiemannSphere) ∈ finiteChart :=
  (mem_finiteChart _).mpr (OnePoint.coe_ne_infty z)

@[simp] theorem infty_not_mem_finiteChart : (∞ : RiemannSphere) ∉ finiteChart := by
  exact fun h => (mem_finiteChart _).mp h rfl

@[simp] theorem coe_mem_infinityChart_iff (z : ℂ) :
    (z : RiemannSphere) ∈ infinityChart ↔ z ≠ 0 := by
  rw [mem_infinityChart]
  exact not_congr OnePoint.coe_injective.eq_iff

@[simp] theorem infty_mem_infinityChart : (∞ : RiemannSphere) ∈ infinityChart :=
  (mem_infinityChart _).mpr (OnePoint.coe_ne_infty 0).symm

theorem infinityParametrization_mem (u : ℂ) : infinityParametrization u ∈ infinityChart :=
  mem_range_self u

theorem infinityParametrization_mem_finiteChart_iff (u : ℂ) :
    infinityParametrization u ∈ finiteChart ↔ u ≠ 0 := by
  rw [mem_finiteChart, ← infinityParametrization_zero]
  exact not_congr infinityParametrization_injective.eq_iff

/-- The two actual affine open sets cover the whole sphere. -/
theorem chart_cover (p : RiemannSphere) : p ∈ finiteChart ∨ p ∈ infinityChart := by
  by_cases hp : p = (∞ : RiemannSphere)
  · subst p
    exact Or.inr infty_mem_infinityChart
  · exact Or.inl ((mem_finiteChart p).mpr hp)

theorem exists_infinityCoordinate (p : RiemannSphere) (hp : p ∈ infinityChart) :
    ∃ u : ℂ, infinityParametrization u = p := hp

theorem inverse_mem_infinityOpen (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (z : ℂ) (hz : (z : RiemannSphere) ∈ U) : z⁻¹ ∈ infinityOpen U := by
  have hz0 : z ≠ 0 := (coe_mem_infinityChart_iff z).mp (hU hz)
  change infinityParametrization z⁻¹ ∈ U
  rw [infinityParametrization_of_ne (inv_ne_zero hz0), inv_inv]
  exact hz

theorem reciprocalCoefficient_analytic (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (infinityOpen U)) :
    AnalyticOnNhd ℂ (fun z => F z⁻¹) (finiteOpen U) := by
  intro z hz
  have hz0 : z ≠ 0 := (coe_mem_infinityChart_iff z).mp (hU hz)
  exact (hF z⁻¹ (inverse_mem_infinityOpen U hU z hz)).comp
    (contDiffAt_inv ℂ hz0 (n := ω)).analyticAt

theorem reciprocalCoefficient_infinityExtension (U : Opens RiemannSphere)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (infinityOpen U))
    (hInf : (∞ : RiemannSphere) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G (Metric.ball (0 : ℂ) r) ∧ G 0 = F 0 ∧
        ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 →
          infinityParametrization u ∈ U → F (u⁻¹)⁻¹ = G u := by
  obtain ⟨r, hr, hrU⟩ := exists_positive_infinity_radius U hInf
  exact ⟨r, hr, F, hF.mono hrU, rfl, fun u _ _ _ => congrArg F (inv_inv u)⟩

/-- Analytic reciprocal coefficients give actual holomorphic sections on
every original subopen set of the reciprocal chart. -/
def ofInfinityCoefficient (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (infinityOpen U)) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U :=
  fromFiniteSection U (fun z => F z⁻¹) (F 0)
    (reciprocalCoefficient_analytic U hU F hF)
    (reciprocalCoefficient_infinityExtension U F hF)

@[simp] theorem ofInfinityCoefficient_coe (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (infinityOpen U))
    (z : ℂ) (hz : (z : RiemannSphere) ∈ U) :
    ofInfinityCoefficient U hU F hF ⟨(z : RiemannSphere), hz⟩ = F z⁻¹ := rfl

@[simp] theorem ofInfinityCoefficient_infty (U : Opens RiemannSphere) (hU : U ≤ infinityChart)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (infinityOpen U))
    (hInf : (∞ : RiemannSphere) ∈ U) :
    ofInfinityCoefficient U hU F hF ⟨(∞ : RiemannSphere), hInf⟩ = F 0 := rfl

@[simp] theorem ofInfinityCoefficient_parametrization (U : Opens RiemannSphere)
    (hU : U ≤ infinityChart) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (infinityOpen U))
    (u : ℂ) (hu : infinityParametrization u ∈ U) :
    ofInfinityCoefficient U hU F hF ⟨infinityParametrization u, hu⟩ = F u := by
  change fromFinite (fun z => F z⁻¹) (F 0) (infinityParametrization u) = F u
  by_cases hu0 : u = 0
  · subst u
    rw [infinityParametrization_zero, fromFinite_infty]
  · rw [fromFinite_infinityParametrization _ _ hu0, inv_inv]

@[simp] theorem infinityCoefficient_ofInfinityCoefficient (U : Opens RiemannSphere)
    (hU : U ≤ infinityChart) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F (infinityOpen U))
    (u : ℂ) (hu : u ∈ infinityOpen U) :
    infinityCoefficient U (ofInfinityCoefficient U hU F hF) u = F u := by
  exact (infinityCoefficient_apply U _ u hu).trans
    (ofInfinityCoefficient_parametrization U hU F hF u hu)

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames
