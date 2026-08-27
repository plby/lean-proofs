/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialResidualPairs

/-! # Uniform positive initial densities for a small supported absorber -/

namespace Erdos207

open Finset
open scoped Classical

noncomputable section

theorem initial_globalAvailability_lower_unrestricted
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C L : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj] {bank : TripleSystemOn V}
    (hdegree : ∀ x, H.degree x ≤ C) (hsupport : (verticesOn bank).card ≤ C)
    (hlarge : L + 3 * C + 2 ≤ Fintype.card V) :
    Fintype.card V * (Fintype.card V - (C + 1)) * L ≤
      6 * (absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
        (outsideAvailableTriangles H bank)).available.card := by
  let S := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
    (outsideAvailableTriangles H bank)
  have hper : ∀ u : V, (Fintype.card V - (C + 1)) * L ≤
      ∑ v ∈ (univ.erase u), (availableTrianglesContainingPair S {u, v}).card := by
    intro u
    calc
      _ ≤ (graphGoodPartners H u).card * L :=
        Nat.mul_le_mul_right L (card_sub_add_one_le_graphGoodPartners_of_degree hdegree u)
      _ = ∑ _v ∈ graphGoodPartners H u, L := by simp
      _ ≤ ∑ v ∈ graphGoodPartners H u, (availableTrianglesContainingPair S {u, v}).card := by
        apply sum_le_sum
        intro v hv
        have hvdata := mem_graphGoodPartners_iff.mp hv
        have hlocal := card_sub_two_le_initialPairStar_add_three_mul_unrestricted
          (q := q) hdegree hsupport hvdata.1.symm hvdata.2
        dsimp only [S]
        omega
      _ ≤ _ := sum_le_sum_of_subset (graphGoodPartners_subset_erase H u)
  calc
    _ = ∑ _u : V, (Fintype.card V - (C + 1)) * L := by simp [mul_assoc]
    _ ≤ ∑ u : V, ∑ v ∈ (univ.erase u), (availableTrianglesContainingPair S {u, v}).card :=
      sum_le_sum fun u _ ↦ hper u
    _ = _ := sum_ordered_card_availableTrianglesContainingPair S

theorem initial_globalAvailability_cube_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj] {bank : TripleSystemOn V}
    (hdegree : ∀ x, H.degree x ≤ C) (hsupport : (verticesOn bank).card ≤ C)
    (hlarge : 6 * C + 4 ≤ Fintype.card V) :
    Fintype.card V ^ 3 ≤ 48 * (absorberGreedyInitialState
      (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)).available.card := by
  let N := Fintype.card V
  let L := N - (3 * C + 2)
  have hbound := initial_globalAvailability_lower_unrestricted (q := q) (L := L) hdegree hsupport
    (by dsimp only [L, N]; omega)
  have h1 : N ≤ 2 * N := by omega
  have h2 : N ≤ 2 * (N - (C + 1)) := by dsimp only [N]; omega
  have h3 : N ≤ 2 * L := by dsimp only [N, L]; omega
  calc
    N ^ 3 = N * N * N := by ring
    _ ≤ (2 * N) * (2 * (N - (C + 1))) * (2 * L) := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    _ = 8 * (N * (N - (C + 1)) * L) := by ring
    _ ≤ 8 * (6 * (absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank)
        (outsideAvailableTriangles H bank)).available.card) := Nat.mul_le_mul_left 8 hbound
    _ = _ := by ring

theorem initialResidualPairs_density_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj] {bank : TripleSystemOn V}
    (hdegree : ∀ x, H.degree x ≤ C) (hsupport : (verticesOn bank).card ≤ C)
    (hlarge : 6 * C + 4 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ^ 2 / 16 ≤ ((initialResidualPairs H).card : ℝ) := by
  let S := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
  let Q := initialResidualPairs H
  let N : ℝ := Fintype.card V
  have hNpos : 0 < N := by dsimp only [N]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have hcube : N ^ 3 ≤ 48 * (S.available.card : ℝ) := by
    dsimp only [N, S]
    exact_mod_cast initial_globalAvailability_cube_le (q := q) hdegree hsupport hlarge
  have hsum : (∑ P ∈ Q, ((availableTrianglesContainingPair S P).card : ℝ)) = 3 * (S.available.card : ℝ) := by
    exact_mod_cast sum_pairSet_card_available S Q
      (fun P hP ↦ ((mem_initialResidualPairs H P).mp hP).1)
      (fun _ hP hstar ↦ initialResidualPairs_cover_available q H bank hP hstar)
  have hupper : 3 * (S.available.card : ℝ) ≤ (Q.card : ℝ) * N := by
    rw [← hsum]
    simpa only [sum_const, nsmul_eq_mul] using
      (sum_le_sum fun P hP ↦ (initialResidualPairs_initial_degree_interval (q := q) hdegree hsupport hP).2)
  have hmul : N ^ 2 * N ≤ (16 * (Q.card : ℝ)) * N := by nlinarith only [hcube, hupper]
  have hcancel := (mul_le_mul_iff_left₀ hNpos).mp hmul
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  dsimp only [N, Q] at hcancel
  nlinarith only [hcancel]

theorem initial_pair_relative_degree_interval
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj] {bank : TripleSystemOn V}
    (hdegree : ∀ x, H.degree x ≤ C) (hsupport : (verticesOn bank).card ≤ C)
    (hlarge : 6 * C + 4 ≤ Fintype.card V) :
    let S := absorberGreedyInitialState (absorberErdosForbiddenConfigurationsOn q bank) (outsideAvailableTriangles H bank)
    let Q := initialResidualPairs H
    (Fintype.card V : ℝ) / 6 ≤ (S.available.card : ℝ) / Q.card ∧
      (S.available.card : ℝ) / Q.card ≤ (Fintype.card V : ℝ) / 3 ∧
      ∀ P ∈ Q, |((availableTrianglesContainingPair S P).card : ℝ) - 3 * (S.available.card : ℝ) / Q.card| ≤
        3 * (C : ℝ) + 2 := by
  dsimp only
  have hNpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  have hQlower := initialResidualPairs_density_lower (q := q) hdegree hsupport hlarge
  have hQpos : 0 < (initialResidualPairs H).card := by
    have hpos : (0 : ℝ) < (initialResidualPairs H).card := (by positivity : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 / 16).trans_le hQlower
    exact_mod_cast hpos
  have havg := initial_pair_average_interval _ (initialResidualPairs H) (Fintype.card V) (3 * (C : ℝ) + 2)
    (fun P hP ↦ ((mem_initialResidualPairs H P).mp hP).1)
    (fun _ hP hstar ↦ initialResidualPairs_cover_available q H bank hP hstar) hQpos
    (fun _ hP ↦ initialResidualPairs_initial_degree_interval (q := q) hdegree hsupport hP)
  have hlargeR : 6 * (C : ℝ) + 4 ≤ Fintype.card V := by exact_mod_cast hlarge
  have hratio := initial_pair_average_ratio_bounds _ _ _ _ hNpos (by linarith) havg.1
  exact ⟨hratio.1, hratio.2, havg.2⟩

end

end Erdos207
