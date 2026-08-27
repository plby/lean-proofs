/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TriangleRegularizationThreshold

/-! # The source triangle-regularization lemma, with a uniform order threshold -/

namespace Erdos207

open Finset

noncomputable section

theorem source_triangle_regularization_with_edge_count :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n →
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
      ∀ (E A : Finset (Finset V)) (C p : ℝ), E.card ≤ n ^ 2 →
      2 ≤ C → (n : ℝ) ^ (-1 / 6 : ℝ) < p → p < 1 →
      (∀ P ∈ E, P.card = 2) → (∀ T ∈ A, T.card = 3) →
      (∀ T ∈ A, T.powersetCard 2 ⊆ E) →
      (∀ P ∈ E, |p ^ 2 * n - (A.filter (P ⊆ ·)).card| ≤ p ^ 2 * n / (12 * C ^ 5)) →
      (∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → S.powersetCard 2 ⊆ E →
        p ^ S.card * n / C ≤ ((triangleSetExtensionVertices A S).card : ℝ) ∧
          ((triangleSetExtensionVertices A S).card : ℝ) ≤ C * p ^ S.card * n) →
      ∃ R ⊆ A, ∀ P ∈ E,
        |((R.filter (P ⊆ ·)).card : ℝ) - p ^ 2 * n / 4| ≤
          (n : ℝ) ^ (-1 / 4 : ℝ) * (p ^ 2 * n / 4) := by
  obtain ⟨N, hN1, hN⟩ := exists_triangleRegularization_failure_threshold
  refine ⟨N, fun n hn V _ _ E A C p hcard hC hp hp1 hE hA hAE hdegree hext ↦ ?_⟩
  have hn1 : 1 ≤ n := hN1.trans hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp0 : 0 < p := (Real.rpow_pos_of_pos hnr _).trans hp
  apply exists_source_triangle_regularized_finite E A C p n ((n : ℝ) ^ (-1 / 4 : ℝ))
    (by linarith) hp0 hnr (Real.rpow_pos_of_pos hnr _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by norm_num))
    hE hA hAE hdegree hext
  apply lt_of_le_of_lt _ (hN n hn p hp.le)
  have hcardR : (E.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcardR (by norm_num))
    (Real.exp_pos _).le

theorem source_triangle_regularization :
    ∃ N : ℕ, ∀ (n : ℕ), N ≤ n →
      ∀ {V : Type*} [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ (E A : Finset (Finset V)) (C p : ℝ),
      2 ≤ C → (n : ℝ) ^ (-1 / 6 : ℝ) < p → p < 1 →
      (∀ P ∈ E, P.card = 2) → (∀ T ∈ A, T.card = 3) →
      (∀ T ∈ A, T.powersetCard 2 ⊆ E) →
      (∀ P ∈ E, |p ^ 2 * n - (A.filter (P ⊆ ·)).card| ≤ p ^ 2 * n / (12 * C ^ 5)) →
      (∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → S.powersetCard 2 ⊆ E →
        p ^ S.card * n / C ≤ ((triangleSetExtensionVertices A S).card : ℝ) ∧
          ((triangleSetExtensionVertices A S).card : ℝ) ≤ C * p ^ S.card * n) →
      ∃ R ⊆ A, ∀ P ∈ E,
        |((R.filter (P ⊆ ·)).card : ℝ) - p ^ 2 * n / 4| ≤
          (n : ℝ) ^ (-1 / 4 : ℝ) * (p ^ 2 * n / 4) := by
  obtain ⟨N, hN⟩ := source_triangle_regularization_with_edge_count
  refine ⟨N, fun n hn V _ _ hV E A C p hC hp hp1 hE hA hAE hdegree hext ↦ ?_⟩
  have hcard : E.card ≤ n ^ 2 := by
    calc
      _ ≤ ((univ : Finset V).powersetCard 2).card := card_le_card
        (fun P hP ↦ mem_powersetCard.mpr ⟨subset_univ _, hE P hP⟩)
      _ = n.choose 2 := by rw [card_powersetCard, card_univ, hV]
      _ ≤ n ^ 2 := Nat.choose_le_pow n 2
  exact hN n hn E A C p hcard hC hp hp1 hE hA hAE hdegree hext

end

end Erdos207
