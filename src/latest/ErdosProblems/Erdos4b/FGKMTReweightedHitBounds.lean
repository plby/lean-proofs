/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTHitBonferroni
import ErdosProblems.Erdos4b.FGKMTReweightedEventMass

/-! # Hit and pair estimates for the actual reweighted edge family -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

theorem reweightedFamily_pairMass_eq_event (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (W : Finset α) (τ : ℝ) (hP : ∀ v ∈ F.vertices, 0 < P v)
    (hτ : τ < 1) (i : I) (v u : α) :
    (F.reweightedFamily P W τ hP hτ).pairMass i v u =
      F.reweightedEventMass P W τ i
        (Finset.univ.filter fun w => v ∈ F.edge i w ∧ u ∈ F.edge i w) := by
  rw [pairMass, Fintype.sum_option]
  simp only [reweightedFamily, optionalEdge, Finset.notMem_empty, false_and, if_false,
    zero_add, reweightedEventMass, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases h : v ∈ F.edge i w ∧ u ∈ F.edge i w <;>
    simp only [h, if_false]

theorem reweightedFamily_hitMass_eq_event (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (W : Finset α) (τ : ℝ) (hP : ∀ v ∈ F.vertices, 0 < P v)
    (hτ : τ < 1) (i : I) (e : Finset α) :
    (F.reweightedFamily P W τ hP hτ).hitMass i e =
      F.reweightedEventMass P W τ i
        (Finset.univ.filter fun w => (e ∩ F.edge i w).Nonempty) := by
  rw [hitMass, Fintype.sum_option]
  simp only [reweightedFamily, optionalEdge, Finset.inter_empty, Finset.not_nonempty_empty,
    if_false, zero_add, reweightedEventMass, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases h : (e ∩ F.edge i w).Nonempty <;> simp only [h, if_true, if_false]

theorem reweightedFamily_vertexMass_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (W : Finset α)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (i : I) (v : α) :
    (F.reweightedFamily P W τ (fun a ha => hκ0.trans_le (hP a ha))
      (hτ.trans_lt (by norm_num))).vertexMass i v ≤
      2 * (1 / κ ^ F.rank) * F.vertexMass i v := by
  rw [F.reweightedFamily_vertexMass_eq_event]
  have h := F.reweightedEventMass_le hκ0 hκ1 hP W hτ0 hτ i
    (Finset.univ.filter fun w => v ∈ F.edge i w)
  simpa only [Finset.sum_filter, vertexMass] using h

theorem reweightedFamily_pairMass_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (W : Finset α)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (i : I) (v u : α) :
    (F.reweightedFamily P W τ (fun a ha => hκ0.trans_le (hP a ha))
      (hτ.trans_lt (by norm_num))).pairMass i v u ≤
      2 * (1 / κ ^ F.rank) * F.pairMass i v u := by
  rw [F.reweightedFamily_pairMass_eq_event]
  have h := F.reweightedEventMass_le hκ0 hκ1 hP W hτ0 hτ i
    (Finset.univ.filter fun w => v ∈ F.edge i w ∧ u ∈ F.edge i w)
  simpa only [Finset.sum_filter, pairMass] using h

theorem reweightedFamily_hitMass_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (W : Finset α)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (i : I) (e : Finset α) :
    (F.reweightedFamily P W τ (fun a ha => hκ0.trans_le (hP a ha))
      (hτ.trans_lt (by norm_num))).hitMass i e ≤
      2 * (1 / κ ^ F.rank) * F.hitMass i e := by
  rw [F.reweightedFamily_hitMass_eq_event]
  have h := F.reweightedEventMass_le hκ0 hκ1 hP W hτ0 hτ i
    (Finset.univ.filter fun w => (e ∩ F.edge i w).Nonempty)
  simpa only [Finset.sum_filter, hitMass] using h

theorem reweightedFamily_codegree_le (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (W : Finset α)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (v u : α) :
    (F.reweightedFamily P W τ (fun a ha => hκ0.trans_le (hP a ha))
      (hτ.trans_lt (by norm_num))).codegree v u ≤
      2 * (1 / κ ^ F.rank) * F.codegree v u := by
  unfold codegree
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _hi =>
    F.reweightedFamily_pairMass_le hκ0 hκ1 hP W hτ0 hτ i v u

theorem reweightedFamily_hitMass_le_card (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ b : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (W : Finset α)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (i : I) (e : Finset α)
    (hcap : ∀ v ∈ e, F.vertexMass i v ≤ b) :
    (F.reweightedFamily P W τ (fun a ha => hκ0.trans_le (hP a ha))
      (hτ.trans_lt (by norm_num))).hitMass i e ≤
      2 * (1 / κ ^ F.rank) * (e.card : ℝ) * b := by
  calc
    _ ≤ 2 * (1 / κ ^ F.rank) * F.hitMass i e :=
      F.reweightedFamily_hitMass_le hκ0 hκ1 hP W hτ0 hτ i e
    _ ≤ 2 * (1 / κ ^ F.rank) * ((e.card : ℝ) * b) :=
      mul_le_mul_of_nonneg_left (F.hitMass_le_card_mul i e hcap) (by positivity)
    _ = _ := by ring

theorem reweightedFamily_sum_hitMass_error (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ δ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ v ∈ F.vertices, κ ≤ P v) (W : Finset α)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (e : Finset α) (hδ : 0 ≤ δ)
    (hcodeg : ∀ v ∈ e, ∀ u ∈ e, u ≠ v → F.codegree v u ≤ δ) :
    let G := F.reweightedFamily P W τ (fun a ha => hκ0.trans_le (hP a ha))
      (hτ.trans_lt (by norm_num))
    |(∑ i, G.hitMass i e) - ∑ v ∈ e, G.degree v| ≤
      2 * (1 / κ ^ F.rank) * (e.card : ℝ) ^ 2 * δ := by
  intro G
  have hcap (v : α) (hv : v ∈ e) (u : α) (hu : u ∈ e) (huv : u ≠ v) :
      G.codegree v u ≤ 2 * (1 / κ ^ F.rank) * δ :=
    (F.reweightedFamily_codegree_le hκ0 hκ1 hP W hτ0 hτ v u).trans
      (mul_le_mul_of_nonneg_left (hcodeg v hv u hu huv) (by positivity))
  have h := G.sum_hitMass_error_le e (by positivity : 0 ≤ 2 * (1 / κ ^ F.rank) * δ) hcap
  calc
    _ ≤ (e.card : ℝ) ^ 2 * (2 * (1 / κ ^ F.rank) * δ) := h
    _ = _ := by ring

end

end Erdos4b.FGKMT.FiniteEdgeFamily
