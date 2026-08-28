import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicUniformDescent
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Quantitative control of noncritical descent

Descent on a compact noncritical set can remain in any open neighborhood of
that set. On a fixed positive time interval with a uniform energy decrease,
small energy loss forces small movement, uniformly over the initial point.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization VertexSpace

variable {n m : ℕ}

theorem continuousOn_descent (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ) :
    ContinuousOn (descent a b τ) (admissible a b m ×ˢ (univ : Set ℝ)) :=
  fun p hp ↦ (continuousAt_descent a b τ (p := p) hp.1).continuousWithinAt

theorem exists_uniform_descent_in_neighborhood (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (K : Set (Space n m)) (hK : IsCompact K)
    (ha : K ⊆ admissible a b m)
    (hn : ∀ v ∈ K, mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0)
    (N : Set (Space n m)) (hN : IsOpen N) (hKN : K ⊆ N) :
    ∃ c > 0, ∃ T > 0, ∀ v ∈ K, ∀ s ∈ Icc (0 : ℝ) T,
      descent a b τ (v, s) ∈ admissible a b m ∧ descent a b τ (v, s) ∈ N ∧
        energy a b τ (descent a b τ (v, s)) ≤ energy a b τ v - c * s := by
  obtain ⟨c, hc, T₀, hT₀, hstep⟩ := exists_uniform_descent a b τ K hK ha hn
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hmap : Continuous (fun p : ℝ × K ↦ descent a b τ (p.2.1, p.1)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (continuousAt_descent a b τ (ha p.2.2)).comp
      ((continuous_subtype_val.continuousAt.comp continuousAt_snd).prodMk continuousAt_fst)
  have ho : IsOpen {s : ℝ | ∀ v : K, descent a b τ (v.1, s) ∈ N} :=
    isOpen_forall_compact (hN.preimage hmap)
  have hz : (0 : ℝ) ∈ {s : ℝ | ∀ v : K, descent a b τ (v.1, s) ∈ N} := by
    intro v
    rw [descent_zero]
    exact hKN v.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hz)
  refine ⟨c, hc, min T₀ (ε / 2), lt_min hT₀ (by positivity), ?_⟩
  intro v hv s hs
  have hs₀ : s ∈ Icc (0 : ℝ) T₀ := ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
  have hsball : s ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    have hh := hs.2.trans (min_le_right T₀ (ε / 2))
    linarith
  exact ⟨(hstep v hv s hs₀).1, hball hsball ⟨v, hv⟩, (hstep v hv s hs₀).2⟩

theorem exists_descent_energy_window (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (K : Set (Space n m)) (hK : IsCompact K)
    (ha : K ⊆ admissible a b m) (c T : ℝ) (hc : 0 < c) (hT : 0 ≤ T)
    (hstep : ∀ v ∈ K, ∀ s ∈ Icc (0 : ℝ) T,
      energy a b τ (descent a b τ (v, s)) ≤ energy a b τ v - c * s)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ζ > 0, ∀ v ∈ K, ∀ s ∈ Icc (0 : ℝ) T,
      energy a b τ v - energy a b τ (descent a b τ (v, s)) ≤ 2 * ζ →
        dist (descent a b τ (v, s)) v < ρ := by
  have hcont : ContinuousOn (descent a b τ) (K ×ˢ Icc (0 : ℝ) T) :=
    fun p hp ↦ (continuousAt_descent a b τ (ha hp.1)).continuousWithinAt
  have huc := (hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont
  obtain ⟨σ, hσ, hmetric⟩ := Metric.uniformContinuousOn_iff.mp huc ρ hρ
  let ζ := c * σ / 4
  refine ⟨ζ, by dsimp [ζ]; positivity, ?_⟩
  intro v hv s hs hsmall
  have htime : s < σ := by
    have hh := hstep v hv s hs
    dsimp [ζ] at hsmall
    nlinarith only [hh, hsmall, hc, hσ, mul_pos hc hσ]
  have hdist : dist (v, s) (v, (0 : ℝ)) < σ := by
    simpa only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero, abs_of_nonneg hs.1,
      max_eq_right hs.1] using htime
  have hh := hmetric (v, s) ⟨hv, hs⟩ (v, 0) ⟨hv, le_rfl, hT⟩ hdist
  simpa only [descent_zero] using hh

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
