import ErdosProblems.Erdos4.FGKMTInitialConditionedLaw

/-! Retained pinned incidence gives a lower bound for the actual conditioned edge degree. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical

variable {I Ω V : Type*} [Fintype I] [Fintype Ω] [Fintype V] [DecidableEq V]

theorem initial_retained_degree_lower (μ : I → FiniteLaw Ω) (E : I → Ω → Prop)
    (edge : I → Ω → Finset V) {σ : ℝ} (hσ : 0 < σ) {k : ℕ} (hk : 1 ≤ k)
    (o₀ : I → Ω) (v : V) :
    (2 / (3 * σ)) *
      ((∑ i, initialPinnedIncidence (μ i) (E i) (edge i) σ k v) -
        ∑ i, if (1 / 2 : ℝ) < |initialCenterNormalizer (μ i) (E i) σ k - 1| then
          initialPinnedIncidence (μ i) (E i) (edge i) σ k v else 0) ≤
      ∑ i, (initialEdgeLaw (μ i) (E i) (edge i) σ k (o₀ i)).prob (fun e => v ∈ e) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := initialEdgeLaw_vertex_lower (μ i) (E i) (edge i) hσ hk (o₀ i) v
  by_cases hgood : |initialCenterNormalizer (μ i) (E i) σ k - 1| ≤ 1 / 2
  · simpa only [if_pos hgood, if_neg (not_lt_of_ge hgood), sub_zero] using hh
  · simpa only [if_neg hgood, if_pos (lt_of_not_ge hgood), sub_self, mul_zero] using hh

theorem initial_degree_lower_of_retained (μ : I → FiniteLaw Ω) (E : I → Ω → Prop)
    (edge : I → Ω → Finset V) {σ : ℝ} (hσ : 0 < σ) {k : ℕ} (hk : 1 ≤ k)
    (o₀ : I → Ω) (v : V) {β : ℝ}
    (hretained : β / 4 ≤
      (∑ i, initialPinnedIncidence (μ i) (E i) (edge i) σ k v) -
        ∑ i, if (1 / 2 : ℝ) < |initialCenterNormalizer (μ i) (E i) σ k - 1| then
          initialPinnedIncidence (μ i) (E i) (edge i) σ k v else 0) :
    β / (6 * σ) ≤
      ∑ i, (initialEdgeLaw (μ i) (E i) (edge i) σ k (o₀ i)).prob (fun e => v ∈ e) := by
  calc
    _ = (2 / (3 * σ)) * (β / 4) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hretained (by positivity)
    _ ≤ _ := initial_retained_degree_lower μ E edge hσ hk o₀ v

end Erdos4.FGKMT
