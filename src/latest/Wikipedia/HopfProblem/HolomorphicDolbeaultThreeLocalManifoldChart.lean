import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedCoordinates
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeDifferentialCoordinates

/-!
# Literal smooth scalar descent through an original manifold chart

An open subset of the original chart target pulls back to an actual open
subset of the manifold.  A real-smooth scalar function pulls back to a
native smooth section there, and its actual scalar chart representative
has precisely the original function germ on the actual coordinate domain.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.LocalManifold

variable (E M : Type) [NormedAddCommGroup E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The literal chart-source part of the inverse image of a model open. -/
def chartPreimageOpen (x₀ : M) (W : Opens E) : Opens M :=
  ⟨(chartAt E x₀).source ∩ (chartAt E x₀) ⁻¹' (W : Set E),
    (chartAt E x₀).isOpen_inter_preimage W.isOpen⟩

@[simp] theorem mem_chartPreimageOpen (x₀ : M) (W : Opens E) (y : M) :
    y ∈ chartPreimageOpen E M x₀ W ↔
      y ∈ (chartAt E x₀).source ∧ chartAt E x₀ y ∈ W := Iff.rfl

/-- A model neighbourhood of the original chart centre pulls back to a
neighbourhood containing the same original point. -/
theorem mem_chartPreimageOpen_self (x₀ : M) (W : Opens E)
    (hx₀ : chartAt E x₀ x₀ ∈ W) : x₀ ∈ chartPreimageOpen E M x₀ W :=
  ⟨mem_chart_source E x₀, hx₀⟩

theorem chartPreimageOpen_subset_source (x₀ : M) (W : Opens E) :
    (chartPreimageOpen E M x₀ W : Set M) ⊆ (chartAt E x₀).source :=
  fun _ hy => hy.1

/-- Pulling back a smaller actual coordinate open stays inside the
original manifold open on which the coordinate problem was posed. -/
theorem chartPreimageOpen_le (U : Opens M) (x₀ : M) (W : Opens E)
    (hW : W ≤ ClosedForms.coordinateDomain E M U x₀) :
    chartPreimageOpen E M x₀ W ≤ U := by
  intro y hy
  have hU : (chartAt E x₀).symm (chartAt E x₀ y) ∈ U := (hW hy.2).2
  rwa [(chartAt E x₀).left_inv hy.1] at hU

/-- The coordinate domain of the literal pullback is exactly the part of
the model open lying in the original chart target. -/
@[simp] theorem mem_coordinateDomain_chartPreimageOpen (x₀ : M) (W : Opens E) (z : E) :
    z ∈ ClosedForms.coordinateDomain E M (chartPreimageOpen E M x₀ W) x₀ ↔
      z ∈ (chartAt E x₀).target ∧ z ∈ W := by
  constructor
  · intro hz
    refine ⟨hz.1, ?_⟩
    have hW : chartAt E x₀ ((chartAt E x₀).symm z) ∈ W := hz.2.2
    rwa [(chartAt E x₀).right_inv hz.1] at hW
  · intro hz
    refine ⟨hz.1, (chartAt E x₀).map_target hz.1, ?_⟩
    change chartAt E x₀ ((chartAt E x₀).symm z) ∈ W
    rw [(chartAt E x₀).right_inv hz.1]
    exact hz.2

variable [NormedSpace ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Pull back a real-smooth scalar function through the genuine original
chart on an actual open contained in its source. -/
def chartSmoothSection (V : Opens M) (x₀ : M)
    (hV : ∀ y ∈ V, y ∈ (chartAt E x₀).source) (u : E → ℂ) (hu : ContDiff ℝ ∞ u) :
    Functions.SmoothSection E M V :=
  Functions.sectionOfSmooth E M V (u ∘ chartAt E x₀) fun y hy =>
    hu.comp_contMDiffAt
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) (hV y hy))

/-- The native section has the literal pulled-back scalar value. -/
@[simp] theorem chartSmoothSection_apply (V : Opens M) (x₀ : M)
    (hV : ∀ y ∈ V, y ∈ (chartAt E x₀).source) (u : E → ℂ) (hu : ContDiff ℝ ∞ u)
    (y : V) : chartSmoothSection E M V x₀ hV u hu y = u (chartAt E x₀ (y : M)) := rfl

/-- The actual extended chart representative of the pulled-back native
smooth section equals the original scalar function throughout its genuine
coordinate domain. -/
theorem chartFunction_chartSmoothSection_apply (V : Opens M) (x₀ : M)
    (hV : ∀ y ∈ V, y ∈ (chartAt E x₀).source) (u : E → ℂ) (hu : ContDiff ℝ ∞ u)
    (z : E) (hz : z ∈ ClosedForms.coordinateDomain E M V x₀) :
    NativeDifferential.chartFunction E M V (chartSmoothSection E M V x₀ hV u hu) x₀ z =
      u z := by
  change Functions.extend E M V (chartSmoothSection E M V x₀ hV u hu)
      ((chartAt E x₀).symm z) = u z
  rw [Functions.extend_apply E M V _ _ hz.2, chartSmoothSection_apply,
    (chartAt E x₀).right_inv hz.1]

/-- The original scalar chart-function germ is preserved exactly, so all
actual derivatives computed from that germ are the original derivatives. -/
theorem chartFunction_chartSmoothSection_germ (V : Opens M) (x₀ : M)
    (hV : ∀ y ∈ V, y ∈ (chartAt E x₀).source) (u : E → ℂ) (hu : ContDiff ℝ ∞ u)
    (z : E) (hz : z ∈ ClosedForms.coordinateDomain E M V x₀) :
    NativeDifferential.chartFunction E M V (chartSmoothSection E M V x₀ hV u hu) x₀ =ᶠ[𝓝 z]
      u := by
  filter_upwards [(ClosedForms.coordinateDomain E M V x₀).isOpen.mem_nhds hz] with y hy
  exact chartFunction_chartSmoothSection_apply E M V x₀ hV u hu y hy

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.LocalManifold
