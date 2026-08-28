import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# A sufficiently small sublevel lies in any neighborhood of a unique minimum

Compactness bounds the function away from its minimum outside the
neighborhood. This lets the local Morse chart describe the entire small
sublevel rather than only its intersection with a chart.
-/

open Set

namespace Wikipedia.SmoothSixDPoincare

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Small closed sublevels of a continuous function near its unique minimum lie in any chosen
open neighborhood of that minimum. -/
theorem exists_small_sublevel_subset {f : X → ℝ} (hf : Continuous f) {p : X}
    (hunique : ∀ x, f x ≤ f p → x = p) {U : Set X} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ ε > (0 : ℝ), {x | f x ≤ f p + ε} ⊆ U := by
  by_cases hne : Uᶜ.Nonempty
  · obtain ⟨q, hq, hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn hne hf.continuousOn
    have hgap : f p < f q := by
      by_contra! h
      exact hq (hunique q h ▸ hpU)
    refine ⟨(f q - f p) / 2, half_pos (sub_pos.mpr hgap), ?_⟩
    intro x hx
    by_contra hxU
    have hqx : f q ≤ f x := hmin hxU
    change f x ≤ f p + (f q - f p) / 2 at hx
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x _
    by_contra hx
    exact hne ⟨x, hx⟩

end Wikipedia.SmoothSixDPoincare
