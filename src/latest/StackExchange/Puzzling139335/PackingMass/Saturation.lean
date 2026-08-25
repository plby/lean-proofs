import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Saturation of a finite measure bound

A measurable subset with at least the measure of its finite-measure container
leaves a null complement.  For a measure positive on nonempty open sets, no
nonempty open subset of the container can avoid it.  If the subset is closed
and the container is regular closed, the two sets are equal.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Puzzling139335.PackingMass

section Measure

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {K S : Set X}

/-- A measurable subset saturating the finite measure of its container leaves
a null complement.  Measurability of the container is not required. -/
theorem measure_sdiff_eq_zero_of_saturation (hK : MeasurableSet K) (hKS : K ⊆ S)
    (hS : μ S ≠ ∞) (hmass : μ S ≤ μ K) : μ (S \ K) = 0 := by
  rw [measure_sdiff hKS hK.nullMeasurableSet
    (ne_top_of_le_ne_top hS (measure_mono hKS))]
  exact tsub_eq_zero_of_le hmass

end Measure

section Topology

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  {μ : Measure X} [μ.IsOpenPosMeasure] {K S U : Set X}

/-- Every open subset of a container avoiding a subset with null complement
is empty. -/
theorem eq_empty_of_isOpen_disjoint_of_null_sdiff (hnull : μ (S \ K) = 0)
    (hU : IsOpen U) (hUS : U ⊆ S) (hUK : Disjoint U K) : U = ∅ := by
  apply hU.eq_empty_of_measure_zero (μ := μ)
  refine measure_mono_null ?_ hnull
  intro x hx
  exact ⟨hUS hx, fun hk => Set.disjoint_left.mp hUK hx hk⟩

/-- A saturated measurable subset cannot leave a nonempty open gap. -/
theorem false_of_nonempty_open_disjoint_of_saturation
    (hK : MeasurableSet K) (hKS : K ⊆ S) (hS : μ S ≠ ∞) (hmass : μ S ≤ μ K)
    (hU : IsOpen U) (hne : U.Nonempty) (hUS : U ⊆ S) (hUK : Disjoint U K) : False := by
  exact hne.ne_empty (eq_empty_of_isOpen_disjoint_of_null_sdiff
    (measure_sdiff_eq_zero_of_saturation hK hKS hS hmass) hU hUS hUK)

/-- A closed subset whose complement in a regular closed set is null contains
that entire set, including its boundary. -/
theorem subset_of_isClosed_of_null_sdiff (hK : IsClosed K)
    (hSregular : closure (interior S) = S) (hnull : μ (S \ K) = 0) : S ⊆ K := by
  have hn : μ (interior S \ K) = 0 := by
    refine measure_mono_null ?_ hnull
    intro x hx
    exact ⟨interior_subset hx.1, hx.2⟩
  have hi : interior S ⊆ K :=
    sdiff_eq_empty.mp ((isOpen_interior.sdiff hK).eq_empty_of_measure_zero hn)
  rw [← hSregular]
  exact closure_minimal hi hK

/-- A closed subset saturating the finite measure of a regular closed container
equals the container as an actual set. -/
theorem eq_of_isClosed_of_saturation [OpensMeasurableSpace X]
    (hK : IsClosed K) (hKS : K ⊆ S) (hSregular : closure (interior S) = S)
    (hS : μ S ≠ ∞) (hmass : μ S ≤ μ K) : K = S := by
  exact Subset.antisymm hKS (subset_of_isClosed_of_null_sdiff hK hSregular
    (measure_sdiff_eq_zero_of_saturation hK.measurableSet hKS hS hmass))

end Topology

end Puzzling139335.PackingMass
