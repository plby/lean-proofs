import Arxiv.Arxiv2411_18291.StarGreedyFailure

/-! # A counterexample to the intended Lemma 5.5, beyond its definition error

The fixed pattern has 257 vertices. The prescribed roots meet the printed
linear smallness condition at arbitrarily large ambient sizes. Nevertheless,
the success event is empty, for every output degree constant. This refutes
the intended ordinary process as well as any claimed high-probability rate.
The proved quadratic smallness repair is used in the paper applications.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem greedy_linear_smallness_counterexample {L : ℕ} (hL : 4096 ≤ L) :
    ∃ Φ : ℕ → greedyStarRoots (ZMod 256) ↪ Fin (65600 * L),
      IsAdmissible (greedyDoubleStar (ZMod 256)) (greedyStarRoots (ZMod 256)) ∧
      (newEdges (greedyStarRoots (ZMod 256)) (greedyDoubleStar (ZMod 256))).Nonempty ∧
      ((65600 * L : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) < 1 / 16385 ∧
      (1 / 16385 : ℝ) <
        (8 * ((2 : ℕ).factorial : ℝ) ^ 2 * (greedyDoubleStar (ZMod 256)).card)⁻¹ ∧
      IsGraphBounded (∅ : Hypergraph (Fin (65600 * L)) 2) (1 / 16385) ∧
      (∀ e ∈ greedyDoubleStar (ZMod 256), ∀ he : e.val ⊆ greedyStarRoots (ZMod 256),
        IsEdgeFamilyBounded
          (fun i : Fin (65792 * L) => rootImage (Φ i) e he) (1 / 16385)) ∧
      (∀ δ : ℝ,
        greedyFamilyEvent Φ (greedyDoubleStar (ZMod 256)) ∅ δ (65792 * L) = ∅ ∧
        (unstoppedGreedyProbability Φ (greedyDoubleStar (ZMod 256)) ∅).real
          (allEdgesGreedyFamilyEvent Φ (greedyDoubleStar (ZMod 256)) ∅ δ (65792 * L)) = 0) := by
  classical
  obtain ⟨Φ, hbound, hempty⟩ := greedyDoubleStar256_empty_success hL
  have hB : IsGraphBounded (∅ : Hypergraph (Fin (65600 * L)) 2) (1 / 16385) := by
    intro S
    simp only [filter_empty, card_empty, Nat.cast_zero, Fintype.card_fin]
    exact (by positivity : (0 : ℝ) ≤ 4 * L).trans_lt
      (greedyDoubleStar256_degree (by omega))
  refine ⟨Φ, greedyDoubleStar_admissible (ZMod 256) 1 (by decide),
    ⟨greedyStarSpoke 0, greedyStarSpoke_new _ 0
      (greedyDoubleStar_spoke_mem (ZMod 256) 0)⟩,
    greedyDoubleStar256_lower_density hL, greedyDoubleStar256_smallness, hB,
    fun e _ he => hbound e he, ?_⟩
  intro δ
  refine ⟨hempty δ, ?_⟩
  have hall : allEdgesGreedyFamilyEvent Φ (greedyDoubleStar (ZMod 256)) ∅ δ
      (65792 * L) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ω ⟨Ψ, hΨ, _, hmatch⟩
    have hm : ω ∈ greedyFamilyEvent Φ (greedyDoubleStar (ZMod 256)) ∅ δ (65792 * L) :=
      ⟨Ψ, hΨ, hmatch⟩
    rw [hempty δ] at hm
    exact hm
  rw [hall, measureReal_empty]

theorem arbitrarily_large_greedy_linear_counterexamples (N : ℕ) :
    ∃ n ≥ N, ∃ t : ℕ, ∃ Φ : ℕ → greedyStarRoots (ZMod 256) ↪ Fin n,
      IsAdmissible (greedyDoubleStar (ZMod 256)) (greedyStarRoots (ZMod 256)) ∧
      (newEdges (greedyStarRoots (ZMod 256)) (greedyDoubleStar (ZMod 256))).Nonempty ∧
      (n : ℝ) ^ (-(1 / 2 : ℝ)) < 1 / 16385 ∧
      (1 / 16385 : ℝ) <
        (8 * ((2 : ℕ).factorial : ℝ) ^ 2 * (greedyDoubleStar (ZMod 256)).card)⁻¹ ∧
      IsGraphBounded (∅ : Hypergraph (Fin n) 2) (1 / 16385) ∧
      (∀ e ∈ greedyDoubleStar (ZMod 256), ∀ he : e.val ⊆ greedyStarRoots (ZMod 256),
        IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) e he) (1 / 16385)) ∧
      (∀ δ : ℝ,
        greedyFamilyEvent Φ (greedyDoubleStar (ZMod 256)) ∅ δ t = ∅ ∧
        (unstoppedGreedyProbability Φ (greedyDoubleStar (ZMod 256)) ∅).real
          (allEdgesGreedyFamilyEvent Φ (greedyDoubleStar (ZMod 256)) ∅ δ t) = 0) := by
  let L := max 4096 (N + 1)
  have hL : 4096 ≤ L := le_max_left _ _
  have hN : N + 1 ≤ L := le_max_right _ _
  obtain ⟨Φ, hΦ⟩ := greedy_linear_smallness_counterexample hL
  exact ⟨65600 * L, by omega, 65792 * L, Φ, hΦ⟩

end Arxiv2411_18291
