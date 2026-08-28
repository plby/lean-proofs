import Wikipedia.HopfProblem.DegreeCollapsePairBandBasinComplement

/-!
# Smooth extension of the stationary weight across the whole pair band

The weight is smooth on the native level basin. Its full constant germs at
the two critical points propagate along every orbit outside that basin in
the closed pair band. This proves native smoothness at all band points,
including the stable and unstable sheets excluded from the cylinder.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]

theorem contMDiffOn_extendedBasinWeight_pair_band (F : Flow ℝ M) {f : M → ℝ}
    (hf : Continuous f) {S : Set M} (hinj : InjOn f S)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x)))
    {p q : M} {l a u : ℝ} (hla : l < a) (hau : a < u)
    (hp : f p < a) (hq : a < f q)
    (hpair : ∀ z ∈ S, f z ∈ Icc l u → z = p ∨ z = q)
    (hB : IsOpen (levelBasin F f a)) {w : M → ℝ}
    (hw : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ w (levelBasin F f a))
    (hstationary : ∀ x ∈ levelBasin F f a, ∀ t : ℝ, w (F t x) = w x)
    (hpw : ∀ᶠ x in 𝓝 p, x ∈ levelBasin F f a → w x = 1)
    (hqw : ∀ᶠ x in 𝓝 q, x ∈ levelBasin F f a → w x = 0) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (extendedBasinWeight F f a w) (f ⁻¹' Icc l u) := by
  have hpgerm := extendedBasinWeight_lower_germ F hf.continuousAt hp hpw
  have hqgerm := extendedBasinWeight_upper_germ F hf.continuousAt hq hqw
  have hinvariant (x : M) (t : ℝ) := extendedBasinWeight_flow F hf a w hstationary x t
  intro x hx
  by_cases hxB : x ∈ levelBasin F f a
  · have heq : extendedBasinWeight F f a w =ᶠ[𝓝 x] w := by
      filter_upwards [hB.mem_nhds hxB] with y hy
      exact extendedBasinWeight_eq F f a w hy
    exact (((hw x hxB).contMDiffAt (hB.mem_nhds hxB)).congr_of_eventuallyEq heq).contMDiffWithinAt
  · rcases pair_band_basin_complement F hf hinj hmono hstrict hla hau hp hq hpair hx hxB with
      ⟨-, hlim⟩ | ⟨-, hlim⟩
    · have heq := constant_germ_of_endpoint_limit F hinvariant hlim hpgerm
      exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt
    · have heq := constant_germ_of_endpoint_limit F hinvariant hlim hqgerm
      exact (contMDiffAt_const.congr_of_eventuallyEq heq).contMDiffWithinAt

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
