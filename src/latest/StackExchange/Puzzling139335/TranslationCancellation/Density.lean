import StackExchange.Puzzling139335.WeightedMass.Isometry
import StackExchange.Puzzling139335.JordanRegion
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrable real density of a closed region

The real density assigns weight one to the interior and one half to the
frontier.  Compact regions have integrable density, including when their
frontiers have positive area.  This is the real-valued version of
`weightedDensity`, suitable for cancellation in `L¹`.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Puzzling139335

noncomputable section

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Weight one on the interior and one half on the frontier, valued in `ℝ`. -/
def weightedDensityReal (P : Set X) : X → ℝ :=
  (interior P).indicator (fun _ => 1) +
    (frontier P).indicator (fun _ => 1 / 2)

theorem weightedDensityReal_of_mem_interior {P : Set X} {x : X}
    (hx : x ∈ interior P) : weightedDensityReal P x = 1 := by
  have hfront : x ∉ frontier P := fun h => h.2 hx
  simp [weightedDensityReal, hx, hfront]

theorem weightedDensityReal_of_mem_frontier {P : Set X} {x : X}
    (hx : x ∈ frontier P) : weightedDensityReal P x = 1 / 2 := by
  simp [weightedDensityReal, hx, hx.2]

theorem weightedDensityReal_of_not_mem {P : Set X} (hP : IsClosed P) {x : X}
    (hx : x ∉ P) : weightedDensityReal P x = 0 := by
  have hint : x ∉ interior P := fun h => hx (interior_subset h)
  have hfront : x ∉ frontier P := fun h => hx (hP.frontier_subset h)
  simp [weightedDensityReal, hint, hfront]

theorem weightedDensityReal_nonneg (P : Set X) (x : X) :
    0 ≤ weightedDensityReal P x := by
  exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    (Set.indicator_nonneg (fun _ _ => by norm_num) x)

theorem weightedDensityReal_le_one (P : Set X) (x : X) :
    weightedDensityReal P x ≤ 1 := by
  by_cases hi : x ∈ interior P
  · rw [weightedDensityReal_of_mem_interior hi]
  by_cases hf : x ∈ frontier P
  · rw [weightedDensityReal_of_mem_frontier hf]
    norm_num
  · simp [weightedDensityReal, hi, hf]

/-- The real and nonnegative extended-real versions agree pointwise. -/
theorem weightedDensityReal_eq_toReal (P : Set X) (x : X) :
    weightedDensityReal P x = (weightedDensity P x).toReal := by
  by_cases hi : x ∈ interior P
  · rw [weightedDensityReal_of_mem_interior hi, weightedDensity_of_mem_interior hi]
    simp
  by_cases hf : x ∈ frontier P
  · rw [weightedDensityReal_of_mem_frontier hf, weightedDensity_of_mem_frontier hf]
    norm_num
  · simp [weightedDensityReal, weightedDensity, hi, hf]

/-- Homeomorphisms preserve the interior/frontier weights pointwise. -/
@[simp] theorem weightedDensityReal_image_homeomorph
    (e : X ≃ₜ Y) (P : Set X) (x : X) :
    weightedDensityReal (e '' P) (e x) = weightedDensityReal P x := by
  simp only [weightedDensityReal, ← e.image_interior, ← e.image_frontier,
    Pi.add_apply, Set.indicator_image e.injective, Function.comp_def]

theorem weightedDensityReal_preimage_homeomorph
    (e : X ≃ₜ Y) (P : Set Y) (x : X) :
    weightedDensityReal (e ⁻¹' P) x = weightedDensityReal P (e x) := by
  have h := weightedDensityReal_image_homeomorph e (e ⁻¹' P) x
  rw [e.image_preimage] at h
  exact h.symm

end Topology

section Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem measurable_weightedDensityReal (P : Set X) : Measurable (weightedDensityReal P) :=
  (measurable_const.indicator isOpen_interior.measurableSet).add
    (measurable_const.indicator isClosed_frontier.measurableSet)

/-- Closed finite-measure regions have integrable real density. -/
theorem integrable_weightedDensityReal_of_isClosed {P : Set X}
    (hP : IsClosed P) {μ : Measure X} (hμ : μ P ≠ ∞) :
    Integrable (weightedDensityReal P) μ := by
  have hi : μ (interior P) ≠ ∞ :=
    ne_top_of_le_ne_top hμ (measure_mono interior_subset)
  have hf : μ (frontier P) ≠ ∞ :=
    ne_top_of_le_ne_top hμ (measure_mono hP.frontier_subset)
  unfold weightedDensityReal
  exact ((integrableOn_const hi).integrable_indicator isOpen_interior.measurableSet).add
    ((integrableOn_const hf).integrable_indicator isClosed_frontier.measurableSet)

/-- Compact regions have integrable density for measures finite on compact sets. -/
theorem integrable_weightedDensityReal_of_isCompact [T2Space X]
    {P : Set X} (hP : IsCompact P) {μ : Measure X} [IsFiniteMeasureOnCompacts μ] :
    Integrable (weightedDensityReal P) μ :=
  integrable_weightedDensityReal_of_isClosed hP.isClosed hP.measure_ne_top

omit [BorelSpace X] in
/-- An interior point cannot lie outside a closed region with the same density
almost everywhere: the open difference would have both zero and positive measure. -/
theorem interior_subset_of_weightedDensityReal_ae {P Q : Set X}
    {μ : Measure X} [μ.IsOpenPosMeasure] (hQ : IsClosed Q)
    (hρ : weightedDensityReal P =ᵐ[μ] weightedDensityReal Q) : interior P ⊆ Q := by
  have hnull : μ (interior P \ Q) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hρ)
    intro x hx
    change weightedDensityReal P x ≠ weightedDensityReal Q x
    rw [weightedDensityReal_of_mem_interior hx.1,
      weightedDensityReal_of_not_mem hQ hx.2]
    exact one_ne_zero
  exact sdiff_eq_empty.mp ((isOpen_interior.sdiff hQ).eq_empty_of_measure_zero hnull)

omit [BorelSpace X] in
/-- The density determines a closed regular region from its almost-everywhere
values, for every measure positive on nonempty open sets. -/
theorem eq_of_weightedDensityReal_ae {P Q : Set X}
    {μ : Measure X} [μ.IsOpenPosMeasure] (hP : IsClosed P) (hQ : IsClosed Q)
    (hPreg : closure (interior P) = P) (hQreg : closure (interior Q) = Q)
    (hρ : weightedDensityReal P =ᵐ[μ] weightedDensityReal Q) : P = Q := by
  apply Subset.antisymm
  · rw [← hPreg]
    exact closure_minimal (interior_subset_of_weightedDensityReal_ae hQ hρ) hQ
  · rw [← hQreg]
    exact closure_minimal (interior_subset_of_weightedDensityReal_ae hP hρ.symm) hP

end Measure

/-- Pointwise invariance under an affine Euclidean congruence. -/
@[simp] theorem weightedDensityReal_image_affineIsometry
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (P : Set Plane) (x : Plane) :
    weightedDensityReal (e '' P) (e x) = weightedDensityReal P x :=
  weightedDensityReal_image_homeomorph e.toHomeomorph P x

/-- Every Jordan region has an integrable real density; no boundary-area
assumption is required. -/
theorem IsJordanRegion.integrable_weightedDensityReal {P : Set Plane}
    (hP : IsJordanRegion P) : Integrable (weightedDensityReal P) volume :=
  integrable_weightedDensityReal_of_isCompact hP.isCompact

/-- Almost-everywhere equality of the weighted densities identifies the actual
Jordan regions, not just their equivalence classes modulo null sets. -/
theorem IsJordanRegion.eq_of_weightedDensityReal_ae {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hρ : weightedDensityReal P =ᵐ[volume] weightedDensityReal Q) : P = Q :=
  Puzzling139335.eq_of_weightedDensityReal_ae hP.isClosed hQ.isClosed hP.closure_interior
    hQ.closure_interior hρ

end

end Puzzling139335
