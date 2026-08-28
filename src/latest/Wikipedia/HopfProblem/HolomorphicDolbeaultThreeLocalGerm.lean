import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalPolydisc

/-!
# The genuine local smooth Dolbeault lemma in three coordinates

An arbitrary smooth closed coefficient family on an open set is first
extended coefficient by coefficient.  Equality of germs preserves the
actual mixed-derivative equations near the chosen point, where the
successive Cauchy–Green construction applies.
-/

noncomputable section

open Complex Set Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

/-- The degree-one local smooth `∂̄` Poincaré lemma in three complex
coordinates, with the literal all-pairs differential equations. -/
theorem exists_smooth_primitive_germ {U : Set Coordinates} (hU : IsOpen U)
    {f : Fin 3 → Coordinates → ℂ} (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hclosed : IsClosedOn f U) {x : Coordinates} (hx : x ∈ U) :
    ∃ u : Coordinates → ℂ, ContDiff ℝ ∞ u ∧
      ∀ᶠ q in 𝓝 x, ∀ i, coordinateDbar i u q = f i q := by
  classical
  choose g hg hgc hge using fun i => exists_compact_smooth_representative hU (hf i) hx
  have hderiv : ∀ᶠ q in 𝓝 x, ∀ i j,
      coordinateDbar i (g j) q = coordinateDbar i (f j) q := by
    exact eventually_all.mpr fun i => eventually_all.mpr fun j =>
      coordinateDbar_eventuallyEq i (hge j)
  have hgclosed : ∀ᶠ q in 𝓝 x, ∀ i j,
      coordinateDbar i (g j) q = coordinateDbar j (g i) q := by
    filter_upwards [hU.mem_nhds hx, hderiv] with q hq hd
    intro i j
    rw [hd i j, hd j i]
    exact hclosed q hq i j
  obtain ⟨u, hu, heq⟩ := exists_smooth_primitive_of_eventually_closed hg hgclosed
  refine ⟨u, hu, ?_⟩
  have hgeall : ∀ᶠ q in 𝓝 x, ∀ i, g i q = f i q := eventually_all.mpr hge
  filter_upwards [heq, hgeall] with q hq hgq
  intro i
  exact (hq i).trans (hgq i)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
