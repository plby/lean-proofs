/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSSharpScheduleProducts
import ErdosProblems.Erdos207.InitialActiveFromFailure

/-! # The actual initial working-graph law from coupled trajectories and a failure bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def ksssInitialGraphProductConstant (q : ℕ) (coeff : ℕ → ℝ) : ℝ≥0 :=
  max 2 (1048576 * Real.toNNReal (Real.exp (∑ d ∈ ksssOrders q, coeff d)))

theorem large_pattern_paid_by_dyadic_error
    (t m : ℕ) (C error x : ℝ≥0) (hC : 2 ≤ C) (herror : (1 / 2 : ℝ≥0) ^ t ≤ error)
    (hm : t < m) : 1 ≤ C ^ m * (x + error) := by
  have hbase : 1 ≤ C ^ (t + 1) * error := by
    calc
      1 ≤ (2 : ℝ≥0) := by norm_num
      _ = (2 : ℝ≥0) ^ (t + 1) * (1 / 2 : ℝ≥0) ^ t := by
        rw [pow_succ, div_pow, one_pow]
        field_simp
      _ ≤ _ := mul_le_mul (pow_le_pow_left' hC _) herror zero_le zero_le
  exact large_pattern_paid_by_error hm hbase (le_trans (by norm_num : (1 : ℝ≥0) ≤ 2) hC)

theorem KSSSPowerParameters.initial_graph_product_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (H : SimpleGraph V) (S₀ : GreedyStateOn V) (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F (initialResidualPairs H) q b B k t a E A i S)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hambient : ∀ T ∈ S₀.available,
      tripleEdgeFinset T ⊆ graphEdges (graphDifference (SimpleGraph.completeGraph V) H))
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (hEupper : E ≤ (Fintype.card V : ℝ) ^ 2)
    (hEquadratic : (Fintype.card V : ℝ) ^ 2 ≤ 16 * E)
    (error : ℝ≥0) (herror : (1 / 2 : ℝ≥0) ^ t ≤ error) (hsmall : error < 1)
    (hfailure : (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ active z.1.1 z.2) ≤ error) :
    IsInitialGraphProductBound
      (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀)
      (fun z ↦ z.2.chosen) (graphDifference (SimpleGraph.completeGraph V) H)
      (Real.toNNReal (ksssEdgeDensity E n)) (ksssInitialGraphProductConstant q coeff) error := by
  let N : ℝ := Fintype.card V
  let scale := N / (t : ℝ) ^ ksssPowerErrorExponent b B
  let d := fun i : ℕ ↦ ksssRoundedPairFloor q a E A scale B i
  let D := fun i : ℕ ↦ ksssRoundedAvailabilityFloor q a E A scale B i
  let M := fun i : ℕ ↦ ksssRoundedAvailabilityCeil q a E A scale B i
  let Inv := fun S ↦ GreedyInvariant F S ∧ GreedyContainedIn S₀.available S
  have hInvInitial : Inv S₀ := ⟨hInv₀, by rw [hchosen₀]; exact empty_subset _, Subset.rfl⟩
  have hInvStep : ∀ i, i < n → ∀ S, Inv S → active i S → (greedyKernel F S).SupportedOn Inv := by
    intro _ _ S hS _ S' hmass
    rcases greedyKernel_supported_step_or_self F S S' hmass with rfl | ⟨T, hT, rfl⟩
    · exact hS
    · exact ⟨hS.1.step hT, hS.2.step hT⟩
  have hlocal := fun (i : ℕ) (hi : i < n) ↦ P.sharp_schedule_bounds i (Nat.cast_nonneg _)
    (P.density_floor i hi.le) hratio
  have hproducts := P.sharp_schedule_survival_point hratio hEupper hEquadratic
  have hC : (2 : ℝ≥0) ≤ ksssInitialGraphProductConstant q coeff := le_max_left _ _
  apply timedStoppedGreedyProcess_boundedSharpInitialGraphProductBound n F
    (graphDifference (SimpleGraph.completeGraph V) H) active Inv D d M t S₀ hchosen₀ hInvInitial
    (FiniteLaw.timedStopped_initial_active_of_failure_lt_one n (fun _ ↦ greedyKernel F) active S₀
      (hfailure.trans_lt hsmall)) hInvStep
    (fun _ hS ↦ ⟨hS.1, hS.2.2, hS.2.1⟩) hambient
    (fun i hi ↦ (hlocal i hi).floor_pos)
  · intro i S _ _ ha
    exact ((hactive i S ha).2.1.rounded_availability_schedule (hactive i S ha).1).1
  · intro i S _ _ ha e he hu
    exact (hactive i S ha).2.1.working_graph_pair_floor e he hu
  · intro i S _ _ ha
    exact ((hactive i S ha).2.1.rounded_availability_schedule (hactive i S ha).1).2
  · exact fun i hi ↦ (hlocal i hi).pair_le_upper
  · exact fun i hi ↦ (hlocal i hi).effective_lt_upper
  · exact hfailure
  · exact hproducts.1.trans (mul_le_mul_of_nonneg_right hC zero_le)
  · exact hproducts.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) zero_le)
  · exact (show (1 : ℝ≥0) ≤ 2 by norm_num).trans hC
  · intro Q edges hm
    exact large_pattern_paid_by_dyadic_error t _ _ error _ hC herror hm

end

end Erdos207
