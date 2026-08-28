import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalStep

/-!
# Actual smooth primitives on smaller three-dimensional polydiscs

The proof performs finitely many genuine one-coordinate Cauchy–Green
corrections.  All coefficients are globally smooth, but their closedness
is required only on the larger open polydisc.
-/

noncomputable section

open Complex Set Metric Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

theorem exists_smooth_primitive_on_polydisc
    {f : Fin 3 → Coordinates → ℂ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (x : Coordinates) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hclosed : IsClosedOn f (polydisc ∅ x r R)) :
    ∃ u : Coordinates → ℂ, ContDiff ℝ ∞ u ∧
      ∀ q ∈ polydisc Finset.univ x r R, ∀ i, coordinateDbar i u q = f i q := by
  classical
  have hpartial : ∀ S : Finset (Fin 3),
      ∃ u : Coordinates → ℂ, ContDiff ℝ ∞ u ∧
        ∀ q ∈ polydisc S x r R, ∀ i ∈ S, coordinateDbar i u q = f i q := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        refine ⟨fun _ => 0, contDiff_const, ?_⟩
        intro q hq i hi
        exact False.elim (Finset.notMem_empty i hi)
    | @insert j S hj ih =>
        obtain ⟨u, hu, heq⟩ := ih
        exact extend_partial_primitive hj hf x hr hrR hclosed hu heq
  obtain ⟨u, hu, heq⟩ := hpartial Finset.univ
  exact ⟨u, hu, fun q hq i => heq q hq i (Finset.mem_univ i)⟩

/-- Globally smooth coefficients closed only near a point admit an actual
smooth primitive as a germ at that point. -/
theorem exists_smooth_primitive_of_eventually_closed
    {f : Fin 3 → Coordinates → ℂ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {x : Coordinates}
    (hclosed : ∀ᶠ q in 𝓝 x, ∀ i j,
      coordinateDbar i (f j) q = coordinateDbar j (f i) q) :
    ∃ u : Coordinates → ℂ, ContDiff ℝ ∞ u ∧
      ∀ᶠ q in 𝓝 x, ∀ i, coordinateDbar i u q = f i q := by
  obtain ⟨R, hR, hclosedR⟩ := Metric.eventually_nhds_iff_ball.mp hclosed
  have hclosed' : IsClosedOn f (polydisc ∅ x (R / 2) R) := by
    intro q hq
    exact hclosedR q (polydisc_empty_subset_ball x hR hq)
  obtain ⟨u, hu, heq⟩ := exists_smooth_primitive_on_polydisc hf x
    (half_pos hR) (half_lt_self hR) hclosed'
  refine ⟨u, hu, ?_⟩
  filter_upwards [(isOpen_polydisc Finset.univ x (R / 2) R).mem_nhds
    (mem_polydisc_center Finset.univ x (half_pos hR) hR)] with q hq
  exact heq q hq

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
