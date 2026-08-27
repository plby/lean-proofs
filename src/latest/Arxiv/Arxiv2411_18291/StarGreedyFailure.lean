import Arxiv.Arxiv2411_18291.BalancedStarRoots
import Arxiv.Arxiv2411_18291.DoubleStarNumerics
import Arxiv.Arxiv2411_18291.UnstoppedGreedyProcess

/-! # No completed greedy family for too many intersecting stars -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem intersecting_greedy_stars_event_empty
    {A V : Type*} [Fintype A] [Fintype V] [DecidableEq A] [DecidableEq V] {t : ℕ}
    (H : Hypergraph (Option A) 2) (hH : ∀ a : A, greedyStarSpoke a ∈ H)
    (Φ : ℕ → greedyStarRoots A ↪ V)
    (hmeet : ∀ i j : Fin t, (usedVertices (Φ i) ∩ usedVertices (Φ j)).Nonempty)
    (ht : Fintype.card V < t) (B : Hypergraph V 2) (δ : ℝ) :
    greedyFamilyEvent Φ H B δ t = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ω ⟨Ψ, hΨ, _⟩
  exact (not_le_of_gt ht)
    (intersecting_greedy_stars_length_le H hH (fun i => Φ i) hmeet B Ψ hΨ)

theorem greedyDoubleStar256_roots {L : ℕ} (hL : 4096 ≤ L) :
    ∃ Φ : ℕ → greedyStarRoots (ZMod 256) ↪ Fin (65600 * L),
      (∀ e : Block (Option (ZMod 256)) 2, ∀ he : e.val ⊆ greedyStarRoots (ZMod 256),
        IsEdgeFamilyBounded
          (fun i : Fin (65792 * L) => rootImage (Φ i) e he) (1 / 16385)) ∧
      (∀ i j : Fin (65792 * L), (usedVertices (Φ i) ∩ usedVertices (Φ j)).Nonempty) := by
  classical
  obtain ⟨Φ₀, hmeet, hbound⟩ := exists_intersecting_balanced_roots (ZMod 256)
    L (65600 * L) (65792 * L)
    (by rw [greedyDoubleStar256_carrier]; omega)
    (greedyDoubleStar256_indices L) (greedyDoubleStar256_degree (by omega : 0 < L))
  let φ := Φ₀ ⟨0, by omega⟩
  refine ⟨finiteRootSequence Φ₀ φ, ?_, ?_⟩
  · intro e he
    have heq : (fun i : Fin (65792 * L) =>
        rootImage (finiteRootSequence Φ₀ φ i) e he) =
        (fun i => mapBlock (Φ₀ i) (rootBlock (greedyStarRoots (ZMod 256)) e he)) := by
      funext i
      rw [finiteRootSequence_apply]
      rfl
    rw [heq]
    exact hbound _
  · intro i j
    rw [finiteRootSequence_apply, finiteRootSequence_apply]
    exact hmeet i j

theorem greedyDoubleStar256_empty_success {L : ℕ} (hL : 4096 ≤ L) :
    ∃ Φ : ℕ → greedyStarRoots (ZMod 256) ↪ Fin (65600 * L),
      (∀ e : Block (Option (ZMod 256)) 2, ∀ he : e.val ⊆ greedyStarRoots (ZMod 256),
        IsEdgeFamilyBounded
          (fun i : Fin (65792 * L) => rootImage (Φ i) e he) (1 / 16385)) ∧
      (∀ δ : ℝ, greedyFamilyEvent Φ (greedyDoubleStar (ZMod 256)) ∅ δ (65792 * L) = ∅) := by
  obtain ⟨Φ, hbound, hmeet⟩ := greedyDoubleStar256_roots hL
  refine ⟨Φ, hbound, fun δ => ?_⟩
  exact intersecting_greedy_stars_event_empty (greedyDoubleStar (ZMod 256))
    (greedyDoubleStar_spoke_mem (ZMod 256)) Φ hmeet
    (by rw [Fintype.card_fin]; omega) ∅ δ

end Arxiv2411_18291
