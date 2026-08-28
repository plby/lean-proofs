import Wikipedia.HopfProblem.HolomorphicAutomorphismDisplacementNonzeroCompact
import Wikipedia.HopfProblem.HolomorphicAutomorphismDisplacementNonzeroComparison

/-!
# Nonzero limits of actual normalized automorphisms

The maximum defining the normalization can occur at the boundary of a closed
coordinate ball. We therefore extract a convergent maximum sequence, move its
manifold limit into an inner chart from the genuine finite cover, and transport
the limiting displacement by the actual derivative of the original chart
transition. Its norm is one, so the inner-chart limit cannot vanish.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [LocallyCompactSpace M] [IsManifold 𝓘(ℂ, E) ω M] (A : CompactAtlas E M)

/-- Locally uniform limits of the actual sup-normalized displacements of
nonidentity automorphisms approaching the identity cannot all vanish. No
normalization, comparison, or nonvanishing premise is supplied separately. -/
theorem exists_ne_zero_of_locallyUniformLimits
    {f : ℕ → HolomorphicAutomorphism 𝓘(ℂ, E) M} {h : A.Index → E → E}
    (hf : Tendsto f atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)))
    (hgood : ∀ n, f n ∈ good A) (hne : ∀ n, f n ≠ 1)
    (hlim : ∀ i : A.Index,
      TendstoLocallyUniformlyOn (fun n => normalized A (f n) i) (h i)
        atTop (A.outerCoordinates i : Set E)) :
    ∃ i : A.Index, ∃ z ∈ A.outerCoordinates i, h i z ≠ 0 := by
  choose idx z hz hnorm using fun n =>
    exists_normalized_norm_eq_one A (hgood n) (hne n)
  obtain ⟨i, z₀, hz₀, φ, hφ, hidx, hzconv⟩ :=
    exists_fixed_index_tendsto_subseq (coordinateBall A) (coordinateBall_isCompact A)
      idx z hz
  let F : ℕ → HolomorphicAutomorphism 𝓘(ℂ, E) M := fun n => f (φ n)
  let p : ℕ → M := fun n => (A.chart i).symm (z (φ n))
  let p₀ : M := (A.chart i).symm z₀
  have hF : Tendsto F atTop (𝓝 (1 : HolomorphicAutomorphism 𝓘(ℂ, E) M)) :=
    hf.comp hφ.tendsto_atTop
  have hFgood : ∀ n, F n ∈ good A := fun n => hgood (φ n)
  have hz' (n : ℕ) : z (φ n) ∈ coordinateBall A i := by
    simpa only [hidx n] using hz (φ n)
  have hnorm' (n : ℕ) : ‖normalized A (F n) i (z (φ n))‖ = 1 := by
    simpa only [F, hidx n] using hnorm (φ n)
  have hp₀ : p₀ ∈ (A.chart i).source :=
    (A.chart i).map_target (coordinateBall_subset_target A i hz₀)
  have hp : Tendsto p atTop (𝓝 p₀) := by
    have hc := ((A.chart i).symm.continuousAt
      (coordinateBall_subset_target A i hz₀)).tendsto.comp hzconv
    simpa only [p, p₀, Function.comp_def] using hc
  obtain ⟨j, hj⟩ := A.covered p₀
  have hjouter : p₀ ∈ A.outerOpen j := A.innerOpen_subset_outerOpen j hj
  have hlimF : TendstoLocallyUniformlyOn (fun n => normalized A (F n) j)
      (h j) atTop (A.outerCoordinates j : Set E) :=
    HolomorphicAutomorphismNormalFamily.locallyUniform_reindex (hlim j) hφ.tendsto_atTop
  have htrans := normalized_moving_change_chart_tendsto A hF hFgood i j
    hlimF hp₀ hjouter hp
  have hsource_norm (n : ℕ) :
      ‖(delta A (F n) : ℂ)⁻¹ • (A.chart i (F n (p n)) - A.chart i (p n))‖ = 1 := by
    simpa only [normalized, Coordinates.expression, p,
      (A.chart i).right_inv (coordinateBall_subset_target A i (hz' n))] using hnorm' n
  have hlimit_norm :
      ‖fderiv ℂ ((A.chart i) ∘ (A.chart j).symm) (A.chart j p₀)
        (h j (A.chart j p₀))‖ = 1 :=
    tendsto_nhds_unique htrans.norm
      (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hsource_norm n).symm))
  refine ⟨j, A.chart j p₀, hjouter.2, ?_⟩
  intro hzero
  simp [hzero] at hlimit_norm

end Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement
