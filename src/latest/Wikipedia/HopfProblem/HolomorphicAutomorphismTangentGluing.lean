import Wikipedia.HopfProblem.HolomorphicAutomorphismTangentGluingCharts
import Wikipedia.HopfProblem.HolomorphicAutomorphismTangentGluingLocal

/-!
# Gluing holomorphic chart coefficients to a native vector field

An arbitrary open cover by restrictions of the original preferred charts
is sufficient. Holomorphic coordinate vectors satisfying the actual
derivative transition law glue to a section of the original tangent
bundle. The construction has exact coordinate values, is unique, and
does not lose a nonzero coordinate vector.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismTangentGluing

variable {ι E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- Compatibility is the genuine derivative of the chart transition
applied to the given coordinate vector, on the actual overlap. -/
def ChartCompatible (a : ι → M) (V : ι → Opens E) (h : ι → E → E) : Prop :=
  ∀ i j x, x ∈ chartDomain (a i) (V i : Set E) →
    x ∈ chartDomain (a j) (V j : Set E) →
    fderiv ℂ ((chartAt E (a j)) ∘ (chartAt E (a i)).symm) ((chartAt E (a i)) x)
      (h i ((chartAt E (a i)) x)) = h j ((chartAt E (a j)) x)

variable (a : ι → M) (V : ι → Opens E)
  (hcover : ∀ x, ∃ i, x ∈ chartDomain (a i) (V i : Set E))
  (h : ι → E → E) (hh : ∀ i, ContDiffOn ℂ ω (h i) (V i))
  (hcompat : ChartCompatible a V h)

/-- The native global holomorphic vector field with the supplied chart
coefficients. No auxiliary tangent bundle or coordinate surrogate is used. -/
def glueChartFields : HolomorphicVectorFields.Field E M :=
  glueLocalSections (fun i => chartDomain_isOpen (a i) (V i).isOpen) hcover
    (fun i => chartSection (a i) (h i))
    (fun i => chartSection_holomorphicOn (a i) (V i).isOpen (hh i))
    (fun i j x hi hj => chartSection_eq_of_transition (a i) (a j) hi.1 hj.1
      (hcompat i j x hi hj))

/-- The field restricts to the local native pushforward on each member
of the original chart cover. -/
theorem glueChartFields_apply (i : ι) {x : M} (hx : x ∈ chartDomain (a i) (V i : Set E)) :
    glueChartFields a V hcover h hh hcompat x = chartSection (a i) (h i) x :=
  glueLocalSections_apply _ _ _ _ _ i hx

/-- The actual tangent-trivialization coefficient is the given function. -/
theorem glueChartFields_coordinate (i : ι) {x : M}
    (hx : x ∈ chartDomain (a i) (V i : Set E)) :
    chartCoordinate (a i) x (glueChartFields a V hcover h hh hcompat x) =
      h i ((chartAt E (a i)) x) := by
  rw [glueChartFields_apply a V hcover h hh hcompat i hx]
  exact chartSection_coordinate (a i) (h i) hx.1

/-- In terms of the original chart differential, the field has exactly
the prescribed coordinate vector. -/
theorem glueChartFields_mfderiv_chart (i : ι) {x : M}
    (hx : x ∈ chartDomain (a i) (V i : Set E)) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (chartAt E (a i)) x
      (glueChartFields a V hcover h hh hcompat x) = h i ((chartAt E (a i)) x) := by
  rw [← chartCoordinate_eq_mfderiv (a i) hx.1]
  exact glueChartFields_coordinate a V hcover h hh hcompat i hx

/-- At a coordinate point, the field is the genuine inverse-chart
differential applied to the coefficient. -/
theorem glueChartFields_at_inverse_chart (i : ι) {q : E}
    (hq : q ∈ V i) (hqt : q ∈ (chartAt E (a i)).target) :
    glueChartFields a V hcover h hh hcompat ((chartAt E (a i)).symm q) =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (chartAt E (a i)).symm q (h i q) := by
  have hx : (chartAt E (a i)).symm q ∈ chartDomain (a i) (V i : Set E) :=
    ⟨(chartAt E (a i)).map_target hqt, by
      change (chartAt E (a i)) ((chartAt E (a i)).symm q) ∈ V i
      rwa [(chartAt E (a i)).right_inv hqt]⟩
  rw [glueChartFields_apply a V hcover h hh hcompat i hx]
  unfold chartSection
  rw [chartVector_eq_mfderiv_symm (a i) hx.1, (chartAt E (a i)).right_inv hqt]

/-- Exact chart coefficients at the inverse-chart point. -/
theorem glueChartFields_coordinate_at_inverse_chart (i : ι) {q : E}
    (hq : q ∈ V i) (hqt : q ∈ (chartAt E (a i)).target) :
    chartCoordinate (a i) ((chartAt E (a i)).symm q)
      (glueChartFields a V hcover h hh hcompat ((chartAt E (a i)).symm q)) = h i q := by
  have hx : (chartAt E (a i)).symm q ∈ chartDomain (a i) (V i : Set E) :=
    ⟨(chartAt E (a i)).map_target hqt, by
      change (chartAt E (a i)) ((chartAt E (a i)).symm q) ∈ V i
      rwa [(chartAt E (a i)).right_inv hqt]⟩
  rw [glueChartFields_coordinate a V hcover h hh hcompat i hx,
    (chartAt E (a i)).right_inv hqt]

/-- A native global field is uniquely determined by these chart coordinates. -/
theorem glueChartFields_unique (v : HolomorphicVectorFields.Field E M)
    (hv : ∀ i x, x ∈ chartDomain (a i) (V i : Set E) →
      chartCoordinate (a i) x (v x) = h i ((chartAt E (a i)) x)) :
    v = glueChartFields a V hcover h hh hcompat := by
  apply glueLocalSections_unique
  intro i x hx
  apply chartCoordinate_injective (a i) hx.1
  rw [chartSection_coordinate (a i) (h i) hx.1]
  exact hv i x hx

/-- Zero and nonzero statements concern the actual coordinate domains;
the target containment prevents irrelevant values outside the charts. -/
theorem glueChartFields_eq_zero_iff
    (hV : ∀ i, (V i : Set E) ⊆ (chartAt E (a i)).target) :
    glueChartFields a V hcover h hh hcompat = 0 ↔ ∀ i q, q ∈ V i → h i q = 0 := by
  constructor
  · intro hz i q hq
    have hcoord := glueChartFields_coordinate_at_inverse_chart a V hcover h hh hcompat
      i hq (hV i hq)
    rw [hz] at hcoord
    exact hcoord.symm.trans (chartCoordinate_zero (a i) _)
  · intro hz
    apply (HolomorphicVectorFields.eq_zero_iff E M _).mpr
    intro x
    obtain ⟨i, hi⟩ := hcover x
    rw [glueChartFields_apply a V hcover h hh hcompat i hi]
    change chartVector (a i) x (h i ((chartAt E (a i)) x)) = 0
    rw [hz i _ hi.2, chartVector_zero]

/-- A nonzero chart coefficient is equivalent to a nonzero native global field. -/
theorem glueChartFields_ne_zero_iff
    (hV : ∀ i, (V i : Set E) ⊆ (chartAt E (a i)).target) :
    glueChartFields a V hcover h hh hcompat ≠ 0 ↔ ∃ i q, q ∈ V i ∧ h i q ≠ 0 := by
  classical
  rw [ne_eq, glueChartFields_eq_zero_iff a V hcover h hh hcompat hV]
  simp only [not_forall, exists_prop]

theorem glueChartFields_ne_zero
    (hV : ∀ i, (V i : Set E) ⊆ (chartAt E (a i)).target)
    (i : ι) {q : E} (hq : q ∈ V i) (hhq : h i q ≠ 0) :
    glueChartFields a V hcover h hh hcompat ≠ 0 :=
  (glueChartFields_ne_zero_iff a V hcover h hh hcompat hV).mpr ⟨i, q, hq, hhq⟩

end Wikipedia.HopfProblem.HolomorphicAutomorphismTangentGluing
