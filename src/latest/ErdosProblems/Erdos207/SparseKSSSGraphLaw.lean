/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SparseSharpScheduleProducts
import ErdosProblems.Erdos207.KSSSGraphPairSupply
import ErdosProblems.Erdos207.GraphMixedProductBound
import ErdosProblems.Erdos207.BoundedSharpGraphCompatible
import ErdosProblems.Erdos207.StoppedGreedyStateLaw

/-! # The ordinary sparse KSSS process supplies the required graph-restricted mixed law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def ksssSparseGraphProductConstant (q : ℕ) (coeff : ℕ → ℝ) : ℝ≥0 :=
  max 2 (128 * Real.toNNReal (Real.exp (∑ d ∈ ksssOrders q, coeff d)))

theorem KSSSPowerParameters.sparse_graph_mixed_product_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin c : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (G : SimpleGraph V) (S₀ : GreedyStateOn V) (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F (graphPairFamily G) q b B k t a E A i S)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hambient : ∀ T ∈ S₀.available, tripleEdgeFinset T ⊆ graphEdges G)
    (hcb : 2 * c ≤ b) (hfloor : ∀ i : ℕ, i ≤ n → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity E i)
    (error : ℝ≥0) (herror : (1 / 2 : ℝ≥0) ^ t ≤ error) (hsmall : error < 1)
    (hfailure : (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ active z.1.1 z.2) ≤ error) :
    IsGraphMixedProductBound (stoppedGreedyStateLaw n F active S₀) (fun S ↦ S.chosen) G
      (Real.toNNReal (ksssEdgeDensity E n)) (Real.toNNReal E / Real.toNNReal A)
      (ksssSparseGraphProductConstant q coeff) error := by
  let N : ℝ := Fintype.card V
  let scale := N / (t : ℝ) ^ ksssPowerErrorExponent b B
  let d := fun i : ℕ ↦ ksssRoundedPairFloor q a E A scale B i
  let D := fun i : ℕ ↦ ksssRoundedAvailabilityFloor q a E A scale B i
  let M := fun i : ℕ ↦ ksssRoundedAvailabilityCeil q a E A scale B i
  let Inv := fun S ↦ GreedyInvariant F S ∧ GreedyContainedIn S₀.available S
  let raw := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hInvInitial : Inv S₀ := ⟨hInv₀, by rw [hchosen₀]; exact empty_subset _, Subset.rfl⟩
  have hInvStep : ∀ i, i < n → ∀ S, Inv S → active i S → (greedyKernel F S).SupportedOn Inv := by
    intro _ _ S hS _ S' hmass
    rcases greedyKernel_supported_step_or_self F S S' hmass with rfl | ⟨T, hT, rfl⟩
    · exact hS
    · exact ⟨hS.1.step hT, hS.2.step hT⟩
  have hsupport : raw.SupportedOn (fun z ↦ Inv z.2) :=
    FiniteLaw.timedStoppedProcessLaw_supported_indexed n (fun _ ↦ greedyKernel F) active
      (fun _ ↦ Inv) S₀ hInvInitial hInvStep
  have hlocal := fun (i : ℕ) (hi : i < n) ↦ P.sparse_sharp_schedule_bounds hcb i (Nat.cast_nonneg _) (hfloor i hi.le)
  have hproducts := P.sparse_sharp_schedule_survival_point hcb hfloor
  have hC : (2 : ℝ≥0) ≤ ksssSparseGraphProductConstant q coeff := le_max_left _ _
  apply IsGraphMixedProductBound.map Prod.snd
  apply graphMixedProductBound_of_bounded_compatible raw (fun z ↦ z.2.chosen) G S₀.available t
    _ _ (ksssSparseGraphProductConstant q coeff) error
    (fun z hz ↦ ⟨(hsupport z hz).1.1, (hsupport z hz).2.1⟩) ?_ hC herror
  intro Q edges hQ hQA hQE hedge hcard
  have hraw := timedStoppedGreedyProcess_boundedSharp_graph_compatible n F G active Inv D d M t S₀
    hchosen₀ hInvInitial
    (FiniteLaw.timedStopped_initial_active_of_failure_lt_one n (fun _ ↦ greedyKernel F) active S₀
      (hfailure.trans_lt hsmall)) hInvStep (fun _ hS ↦ ⟨hS.1, hS.2.2, hS.2.1⟩) hambient
    (fun i hi ↦ (hlocal i hi).floor_pos)
    (fun i S _ _ ha ↦ ((hactive i S ha).2.1.rounded_availability_schedule (hactive i S ha).1).1)
    (fun i S _ _ ha e he hu ↦ (hactive i S ha).2.1.graph_pair_floor e he hu)
    (fun i S _ _ ha ↦ ((hactive i S ha).2.1.rounded_availability_schedule (hactive i S ha).1).2)
    (fun i hi ↦ (hlocal i hi).pair_le_upper) (fun i hi ↦ (hlocal i hi).effective_lt_upper)
    error hfailure Q edges hQ hQA hQE hedge hcard
  have hsurvival := hproducts.1.trans (mul_le_mul_of_nonneg_right hC zero_le)
  have hpoint : transferPointWeight (boundedSharpSurvivalSchedule n M d (3 * t))
      (boundedSharpTransferSchedule n D M d (3 * t)) n ≤
        ksssSparseGraphProductConstant q coeff * (Real.toNNReal E / Real.toNNReal A) := by
    apply hproducts.2.trans
    calc
      _ = (128 * Real.toNNReal (Real.exp (∑ d ∈ ksssOrders q, coeff d))) *
          (Real.toNNReal E / Real.toNNReal A) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) zero_le
  exact hraw.trans (add_le_add (mul_le_mul (pow_le_pow_left' hsurvival edges.card)
    (pow_le_pow_left' hpoint Q.card) zero_le zero_le) le_rfl)

end

end Erdos207
