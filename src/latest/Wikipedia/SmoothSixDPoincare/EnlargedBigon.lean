import Wikipedia.SmoothSixDPoincare.WhitneyBigon
import Mathlib.Topology.Compactness.Compact

/-!
# Slightly enlarge the bigon inside its actual open neighborhood

An anisotropic scaling multiplies the horizontal coordinate by `r` and the
vertical coordinate by `r²`. Compactness allows `r > 1` while staying in any
given open neighborhood of the original embedded bigon. The enlarged cap
has the exact inequality `h*s² + y ≤ h*r²`.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.WhitneyPairModel

def scaledBigonEmbedding (r : ℝ) (p : ℝ × ℝ) : Space :=
  bigonEmbedding (r * p.1, r ^ 2 * p.2)

theorem scaledBigonEmbedding_one (p : ℝ × ℝ) : scaledBigonEmbedding 1 p = bigonEmbedding p := by
  simp only [scaledBigonEmbedding, one_mul, one_pow, Prod.eta]

theorem continuous_scaledBigonEmbedding :
    Continuous (fun z : ℝ × (ℝ × ℝ) => scaledBigonEmbedding z.1 z.2) := by
  unfold scaledBigonEmbedding bigonEmbedding
  fun_prop

/-- An actual enlargement of the whole compact disk remains in its prescribed open neighborhood. -/
theorem exists_scaled_bigon_in_open {h : ℝ} (hh : 0 < h) {U : Set Space} (hU : IsOpen U)
    (hKU : MapsTo bigonEmbedding (bigon h) U) :
    ∃ r : ℝ, 1 < r ∧ MapsTo (scaledBigonEmbedding r) (bigon h) U := by
  have hnear : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ bigon h, scaledBigonEmbedding r p ∈ U := by
    apply (isCompact_bigon hh).eventually_forall_of_forall_eventually
    intro p hp
    apply (continuous_scaledBigonEmbedding.continuousAt (x := (1, p))).preimage_mem_nhds
    apply hU.mem_nhds
    simpa only [scaledBigonEmbedding_one] using hKU hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hrball : (1 + ε / 2 : ℝ) ∈ Metric.ball 1 ε := by
    change dist (1 + ε / 2) 1 < ε
    rw [Real.dist_eq]
    have heq : 1 + ε / 2 - 1 = ε / 2 := by ring
    rw [heq, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact ⟨1 + ε / 2, by linarith, fun p hp => hball hrball p hp⟩

/-- Every point in the enlarged cap is an actual scaled point of the original bigon. -/
theorem enlarged_cap_parametrization {h r : ℝ} (hr : 0 < r) {p : ℝ × ℝ}
    (hp : 0 ≤ p.2 ∧ h * p.1 ^ 2 + p.2 ≤ h * r ^ 2) :
    ∃ q ∈ bigon h, scaledBigonEmbedding r q = bigonEmbedding p := by
  let q : ℝ × ℝ := (p.1 / r, p.2 / r ^ 2)
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hcalc : h * (p.1 / r) ^ 2 + p.2 / r ^ 2 = (h * p.1 ^ 2 + p.2) / r ^ 2 := by
    field_simp
  have hq : q ∈ bigon h := by
    refine ⟨div_nonneg hp.1 hr2.le, ?_⟩
    change h * (p.1 / r) ^ 2 + p.2 / r ^ 2 ≤ h
    rw [hcalc]
    exact (div_le_iff₀ hr2).mpr hp.2
  refine ⟨q, hq, ?_⟩
  apply congrArg bigonEmbedding
  apply Prod.ext
  · change r * (p.1 / r) = p.1
    field_simp
  · change r ^ 2 * (p.2 / r ^ 2) = p.2
    field_simp

end Wikipedia.SmoothSixDPoincare.WhitneyPairModel
