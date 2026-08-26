import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Restoring a boundary after a fixed-parameter limit

This is the abstract `eta ↓ 0` argument used by both retained annular
branches.  The contraction parameter is chosen first, and only then is the
main asymptotic variable sent to infinity.  No diagonal sequence is used.
-/

open Filter
open scoped Topology

namespace Erdos1002

/-- If every fixed contraction tends to zero, and the distance from the
uncontracted quantity is uniformly small after first choosing a sufficiently
thin boundary, then the uncontracted quantity tends to zero. -/
theorem tendsto_zero_of_iterated_contracted_boundary
    (full : ℕ → ℂ)
    (contracted : ℕ → ℕ → ℂ)
    (boundary : ℕ → ℕ → ℝ)
    (hdifference : ∀ m : ℕ, ∀ᶠ N : ℕ in atTop,
      ‖full N - contracted m N‖ ≤ boundary m N)
    (hcontracted : ∀ m : ℕ,
      Tendsto (contracted m) atTop (nhds 0))
    (hboundary : ∀ {δ : ℝ}, 0 < δ →
      ∀ᶠ m : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        boundary m N < δ) :
    Tendsto full atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hmEventually :
      ∀ᶠ m : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        boundary m N < δ / 2 :=
    hboundary (half_pos hδ)
  obtain ⟨m, hm⟩ := hmEventually.exists
  have hc :
      ∀ᶠ N : ℕ in atTop, dist (contracted m N) 0 < δ / 2 :=
    (Metric.tendsto_nhds.mp (hcontracted m))
      (δ / 2) (half_pos hδ)
  filter_upwards [hm, hdifference m, hc] with
      N hboundaryN hdifferenceN hcontractedN
  rw [dist_zero_right] at hcontractedN ⊢
  calc
    ‖full N‖ =
        ‖(full N - contracted m N) + contracted m N‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖full N - contracted m N‖ + ‖contracted m N‖ :=
      norm_add_le _ _
    _ ≤ boundary m N + ‖contracted m N‖ :=
      add_le_add hdifferenceN le_rfl
    _ < δ / 2 + δ / 2 :=
      add_lt_add hboundaryN hcontractedN
    _ = δ := by ring

end Erdos1002
