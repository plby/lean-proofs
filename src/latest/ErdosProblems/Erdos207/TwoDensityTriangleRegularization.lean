/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceTriangleRegularization

/-! # Triangle regularization retaining the separate available-triangle density -/

namespace Erdos207

open Finset

noncomputable section

theorem twoDensityTriangleRegularization_correction_budget
    (C p tau n : ℝ) (hC : 0 < C) (hp : 0 < p) (htau : 0 < tau) (hn : 0 < n) :
    ((C * p ^ 3 * tau ^ 3 * n) * (C * p ^ 4 * tau ^ 6 * n) / 2) *
      ((p ^ 2 * tau * n / (12 * C ^ 5)) /
        ((p ^ 2 * tau * n / C) * (p ^ 3 * tau ^ 3 * n / C) *
          (p ^ 4 * tau ^ 6 * n / C) / 6)) = 1 / 4 := by
  field_simp
  <;> ring

theorem exists_twoDensity_triangle_regularized_finite
    {V : Type*} [Fintype V] [DecidableEq V]
    (E A : Finset (Finset V)) (C p tau n eta : ℝ)
    (hC : 0 < C) (hp : 0 < p) (htau : 0 < tau) (hn : 0 < n)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hE : ∀ P ∈ E, P.card = 2) (hA : ∀ T ∈ A, T.card = 3)
    (hAE : ∀ T ∈ A, T.powersetCard 2 ⊆ E)
    (hdegree : ∀ P ∈ E,
      |p ^ 2 * tau * n - (A.filter (P ⊆ ·)).card| ≤ p ^ 2 * tau * n / (12 * C ^ 5))
    (hext : ∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → S.powersetCard 2 ⊆ E →
      p ^ S.card * tau ^ (S.card.choose 2) * n / C ≤ ((triangleSetExtensionVertices A S).card : ℝ) ∧
        ((triangleSetExtensionVertices A S).card : ℝ) ≤ C * p ^ S.card * tau ^ (S.card.choose 2) * n)
    (hfailure : 2 * E.card * Real.exp (-eta ^ 2 * (p ^ 2 * tau * n) / 16) < 1) :
    ∃ R ⊆ A, ∀ P ∈ E,
      |((R.filter (P ⊆ ·)).card : ℝ) - p ^ 2 * tau * n / 4| ≤ eta * (p ^ 2 * tau * n / 4) := by
  have hc2 : (2 : ℕ).choose 2 = 1 := by decide
  have hc3 : (3 : ℕ).choose 2 = 3 := by decide
  have hc4 : (4 : ℕ).choose 2 = 6 := by decide
  apply exists_triangle_regularized_of_fiveSet_counts A E (eligibleFiveSets E A)
    (p ^ 2 * tau * n) eta (p ^ 2 * tau * n / (12 * C ^ 5))
    ((p ^ 2 * tau * n / C) * (p ^ 3 * tau ^ 3 * n / C) * (p ^ 4 * tau ^ 6 * n / C) / 6)
    ((C * p ^ 3 * tau ^ 3 * n) * (C * p ^ 4 * tau ^ 6 * n) / 2)
    hA hE (fun J hJ ↦ let hm := (mem_eligibleFiveSets_iff E A J).mp hJ
      ⟨hm.1, hm.2.2⟩) heta heta1 (by positivity) (by positivity) hdegree
  · intro P hP
    have h := eligibleFiveSets_pair_count_lower E A P (hE P hP) hP hAE
      (fun k ↦ p ^ k * tau ^ (k.choose 2) * n / C) (by positivity) (by positivity)
      (fun S hS2 hS4 hSE ↦ (hext S hS2 hS4 hSE).1)
    simpa only [hc2, hc3, hc4, pow_one] using h
  · intro T hT
    have h := eligibleFiveSets_triple_count_upper E A T (hA T hT) hT hAE
      (fun k ↦ C * p ^ k * tau ^ (k.choose 2) * n) (by positivity)
      (fun S hS3 hS4 hSE ↦ (hext S (by omega) hS4 hSE).2)
    simpa only [hc3, hc4] using h
  · rw [twoDensityTriangleRegularization_correction_budget C p tau n hC hp htau hn]
    norm_num
  · convert hfailure using 2 <;> congr 1 <;> ring

end

end Erdos207
