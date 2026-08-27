/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiveSetFractionalBounds
import ErdosProblems.Erdos207.FractionalSubfamilySampling

/-! # Triangle regularization from explicit five-clique incidence counts -/

namespace Erdos207

open Finset

noncomputable section

theorem fiveSet_balancing_coefficient_abs_le
    {V : Type*} [DecidableEq V] (A Js : Finset (Finset V)) (P : Finset V)
    (D eps lower : ℝ) (hlower : 0 < lower)
    (hdegree : |D - (A.filter (P ⊆ ·)).card| ≤ eps)
    (hcount : lower ≤ ((Js.filter (P ⊆ ·)).card : ℝ)) :
    |fiveSetBalancingCoefficient A Js D P| ≤ eps / lower := by
  have hcpos : (0 : ℝ) < (Js.filter (P ⊆ ·)).card := hlower.trans_le hcount
  unfold fiveSetBalancingCoefficient
  rw [abs_div, abs_of_pos hcpos]
  exact div_le_div₀ ((abs_nonneg _).trans hdegree) hdegree hlower hcount

theorem exists_triangle_regularized_of_fiveSet_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (A E Js : Finset (Finset V)) (D eta eps lower upper : ℝ)
    (hA : ∀ T ∈ A, T.card = 3) (hE : ∀ P ∈ E, P.card = 2)
    (hJ : ∀ J ∈ Js, J.card = 5 ∧ J.powersetCard 3 ⊆ A)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (heps : 0 ≤ eps) (hlower : 0 < lower)
    (hdegree : ∀ P ∈ E, |D - (A.filter (P ⊆ ·)).card| ≤ eps)
    (hlow : ∀ P ∈ E, lower ≤ ((Js.filter (P ⊆ ·)).card : ℝ))
    (hupp : ∀ T ∈ A, ((Js.filter (T ⊆ ·)).card : ℝ) ≤ upper)
    (hbudget : upper * (eps / lower) ≤ 3 / 10)
    (hfailure : 2 * E.card * Real.exp (-eta ^ 2 * (D / 4) / 4) < 1) :
    ∃ R ⊆ A, ∀ P ∈ E,
      |((R.filter (P ⊆ ·)).card : ℝ) - D / 4| ≤ eta * (D / 4) := by
  classical
  let c := fiveSetBalancingCoefficient A Js D
  let w := fiveSetFractionalWeight E Js c
  have hB : 0 ≤ eps / lower := div_nonneg heps hlower.le
  have hc : ∀ P ∈ E, |c P| ≤ eps / lower := fun P hP ↦
    fiveSet_balancing_coefficient_abs_le A Js P D eps lower hlower (hdegree P hP) (hlow P hP)
  have hw : ∀ T ∈ A, 0 ≤ w T ∧ w T ≤ 1 := by
    intro T hT
    exact fiveSet_fractional_weight_mem_unitInterval E Js T c (eps / lower) hB hE
      (fun J hJs ↦ (hJ J hJs).1) hc
      ((mul_le_mul_of_nonneg_right (hupp T hT) hB).trans hbudget)
  have hmean : ∀ P : E, (∑ T ∈ A.filter (P.1 ⊆ ·), w T) = D / 4 := by
    intro P
    have hpos : (0 : ℝ) < (Js.filter (P.1 ⊆ ·)).card := hlower.trans_le (hlow P.1 P.2)
    exact fiveSet_balanced_edge_sum A E Js D P.1 P.2 hA hE hJ (by exact_mod_cast hpos)
  have hf : 2 * Fintype.card E * Real.exp (-eta ^ 2 * (D / 4) / 4) < 1 := by
    simpa only [Fintype.card_coe] using hfailure
  obtain ⟨R, hRA, hR⟩ := exists_regular_subfamily_of_fractional_weights
    A (fun (P : E) T ↦ P.1 ⊆ T) w (D / 4) eta hw heta heta1 hmean hf
  exact ⟨R, hRA, fun P hP ↦ hR ⟨P, hP⟩⟩

end

end Erdos207
