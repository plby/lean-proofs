/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EligibleFiveSetCounts
import ErdosProblems.Erdos207.FiveSetTriangleRegularization

/-! # Triangle regularization with the source's explicit geometric hypotheses -/

namespace Erdos207

open Finset

noncomputable section

theorem sourceTriangleRegularization_correction_budget
    (C p n : ℝ) (hC : 0 < C) (hp : 0 < p) (hn : 0 < n) :
    ((C * p ^ 3 * n) * (C * p ^ 4 * n) / 2) *
      ((p ^ 2 * n / (12 * C ^ 5)) /
        ((p ^ 2 * n / C) * (p ^ 3 * n / C) * (p ^ 4 * n / C) / 6)) = 1 / 4 := by
  field_simp
  <;> ring

theorem exists_source_triangle_regularized_finite
    {V : Type*} [Fintype V] [DecidableEq V]
    (E A : Finset (Finset V)) (C p n eta : ℝ)
    (hC : 0 < C) (hp : 0 < p) (hn : 0 < n) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hE : ∀ P ∈ E, P.card = 2) (hA : ∀ T ∈ A, T.card = 3)
    (hAE : ∀ T ∈ A, T.powersetCard 2 ⊆ E)
    (hdegree : ∀ P ∈ E,
      |p ^ 2 * n - (A.filter (P ⊆ ·)).card| ≤ p ^ 2 * n / (12 * C ^ 5))
    (hext : ∀ S : Finset V, 2 ≤ S.card → S.card ≤ 4 → S.powersetCard 2 ⊆ E →
      p ^ S.card * n / C ≤ ((triangleSetExtensionVertices A S).card : ℝ) ∧
        ((triangleSetExtensionVertices A S).card : ℝ) ≤ C * p ^ S.card * n)
    (hfailure : 2 * E.card * Real.exp (-eta ^ 2 * (p ^ 2 * n) / 16) < 1) :
    ∃ R ⊆ A, ∀ P ∈ E,
      |((R.filter (P ⊆ ·)).card : ℝ) - p ^ 2 * n / 4| ≤ eta * (p ^ 2 * n / 4) := by
  apply exists_triangle_regularized_of_fiveSet_counts A E (eligibleFiveSets E A)
    (p ^ 2 * n) eta (p ^ 2 * n / (12 * C ^ 5))
    ((p ^ 2 * n / C) * (p ^ 3 * n / C) * (p ^ 4 * n / C) / 6)
    ((C * p ^ 3 * n) * (C * p ^ 4 * n) / 2)
    hA hE (fun J hJ ↦ let hm := (mem_eligibleFiveSets_iff E A J).mp hJ
      ⟨hm.1, hm.2.2⟩) heta heta1 (by positivity) (by positivity) hdegree
  · intro P hP
    exact eligibleFiveSets_pair_count_lower E A P (hE P hP) hP hAE
      (fun k ↦ p ^ k * n / C) (by positivity) (by positivity)
      (fun S hS2 hS4 hSE ↦ (hext S hS2 hS4 hSE).1)
  · intro T hT
    exact eligibleFiveSets_triple_count_upper E A T (hA T hT) hT hAE
      (fun k ↦ C * p ^ k * n) (by positivity)
      (fun S hS3 hS4 hSE ↦ (hext S (by omega) hS4 hSE).2)
  · rw [sourceTriangleRegularization_correction_budget C p n hC hp hn]
    norm_num
  · convert hfailure using 2 <;> congr 1 <;> ring

end

end Erdos207
