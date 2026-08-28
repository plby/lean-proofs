import Wikipedia.HopfProblem.HolomorphicCousinSmoothCocycle
import Wikipedia.HopfProblem.HolomorphicCousinSmoothCocycleRelative

/-!
# Smooth additive cochains normalized near a distinguished patch

For an actual local cocycle, a relative partition of unity produces the
smooth cochain and makes its distinguished member identically zero near any
closed subset of the distinguished patch.  All other members then coincide
there with the original overlap functions.  In a holomorphic application
their antiholomorphic derivatives therefore vanish near that region; no
holomorphic splitting is asserted here.
-/

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCousin

variable {ι E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- An additive smooth local cocycle has a smooth cochain which is zero on
a whole neighborhood of a prescribed closed subset of a distinguished patch.
This is a relative construction from the cocycle itself. -/
theorem exists_normalized_smooth_cocycle_cochain {U : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    {h : ι → ι → M → F}
    (hh : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) ∞ (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k →
      h i j x + h j k x = h i k x)
    (i₀ : ι) {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ (V : Set M) (s : ι → M → F),
      IsOpen V ∧ K ⊆ V ∧ V ⊆ U i₀ ∧
      (∀ i, ContMDiffOn I 𝓘(ℝ, F) ∞ (s i) (U i)) ∧
      (∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x) ∧
      EqOn (s i₀) (fun _ => 0) V ∧
      ∀ i, EqOn (s i) (h i i₀) (U i ∩ V) := by
  obtain ⟨V, hVo, hKV, hVU, ρ, hρ, _, hρ0, _⟩ :=
    exists_smoothPartitionOfUnity_eq_one_near_closed I U hU
      (fun x _ => mem_iUnion.mpr (hcover x)) i₀ hK hKU
  refine ⟨V, partitionCochain ρ h, hVo, hKV, hVU,
    partitionCochain_contMDiffOn hU hρ hh,
    fun i j _ hi hj => partitionCochain_sub_eq hρ hc i j hi hj, ?_, ?_⟩
  · intro x hx
    exact partitionCochain_eq_zero_of_weights_single hc i₀ (hVU hx)
      (fun k hk => hρ0 k hk x hx)
  · intro i x hx
    exact partitionCochain_eq_overlap_of_weights_single hρ hc i i₀ hx.1 (hVU hx.2)
      (fun k hk => hρ0 k hk x hx.2)

end Wikipedia.HopfProblem.HolomorphicCousin
