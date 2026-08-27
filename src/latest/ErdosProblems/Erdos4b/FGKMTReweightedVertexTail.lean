/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConditionedVertexTail
import ErdosProblems.Erdos4b.FGKMTReweightedEventError

/-! # Conditional concentration of the genuine reweighted vertex degree -/

namespace Erdos4b.FGKMT.FiniteEdgeFamily

noncomputable section

open scoped BigOperators

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

def reweightedVertexDegree (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (W : Finset α) (τ : ℝ) (v : α) : ℝ :=
  ∑ i, F.reweightedEventMass P W τ i (F.vertexOutcomes i v)

def vertexReplacementLoss (F : FiniteEdgeFamily I Ω α) (P : α → ℝ)
    (W : Finset α) (τ : ℝ) (v : α) : ℝ :=
  ∑ i, |F.reweightedEventMass P W τ i (F.vertexOutcomes i v) -
    F.rawEventMass P W i (F.vertexOutcomes i v)|

theorem reweightedVertexDegree_eq_degree (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (W : Finset α) (τ : ℝ) (v : α)
    (hP : ∀ u ∈ F.vertices, 0 < P u) (hτ : τ < 1) :
    F.reweightedVertexDegree P W τ v = (F.reweightedFamily P W τ hP hτ).degree v := by
  unfold reweightedVertexDegree degree
  apply Finset.sum_congr rfl
  intro i _hi
  exact (F.reweightedFamily_vertexMass_eq_event P W τ hP hτ i v).symm

theorem vertexReplacementLoss_nonneg (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (W : Finset α) (τ : ℝ) (v : α) :
    0 ≤ F.vertexReplacementLoss P W τ v := Finset.sum_nonneg fun _i _hi => abs_nonneg _

theorem reweightedVertexDegree_sub_raw_le (F : FiniteEdgeFamily I Ω α)
    (P : α → ℝ) (W : Finset α) (τ : ℝ) (v : α) :
    |F.reweightedVertexDegree P W τ v - F.rawVertexDegree P W v| ≤
      F.vertexReplacementLoss P W τ v := by
  rw [reweightedVertexDegree, rawVertexDegree, ← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

variable {Ξ : Type*} [Fintype Ξ]

theorem vertexReplacementLoss_conditioned_tail (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ τ β u : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP : ∀ a ∈ F.vertices, κ ≤ P a) (ρ : Ξ → ℝ) (W : Ξ → Finset α)
    (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2) (v : α)
    (hbad : ∀ i, F.badNormalizerMass P ρ W τ i ≤ β)
    (e : Finset α) (hq : 0 < containmentMass ρ W e) (hu : 0 < u) :
    (∑ s, if u ≤ F.vertexReplacementLoss P (W s) τ v
      then conditionedStateMass ρ W e s else 0) ≤
      ((β + 2 * τ) * ((1 / κ ^ F.rank) * F.degree v)) / (containmentMass ρ W e * u) := by
  have h := F.reweightedEventMass_error_conditioned_tail_le hκ0 hκ1 hP ρ W hρ hρsum hτ0 hτ
    (fun i => F.vertexOutcomes i v) hbad e hq hu
  rw [F.vertexOutcomes_degree_mass] at h
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro s _hs
  unfold vertexReplacementLoss
  split_ifs <;> rfl

theorem finite_triangle_tail_le (μ X Y L : Ξ → ℝ) (hμ : ∀ s, 0 ≤ μ s)
    (hL : ∀ s, |X s - Y s| ≤ L s) (c t u : ℝ) :
    (∑ s, if t + u ≤ |X s - c| then μ s else 0) ≤
      (∑ s, if t ≤ |Y s - c| then μ s else 0) + (∑ s, if u ≤ L s then μ s else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _hs
  by_cases hbig : t + u ≤ |X s - c|
  · have hor : t ≤ |Y s - c| ∨ u ≤ L s := by
      by_contra hn
      push Not at hn
      have htri := abs_sub_le (X s) (Y s) c
      have herr := hL s
      linarith
    rw [if_pos hbig]
    rcases hor with hraw | hloss
    · rw [if_pos hraw]
      split_ifs <;> linarith [hμ s]
    · rw [if_pos hloss]
      split_ifs <;> linarith [hμ s]
  · rw [if_neg hbig]
    exact add_nonneg (ite_nonneg (hμ s) le_rfl) (ite_nonneg (hμ s) le_rfl)

theorem reweightedVertexDegree_conditioned_tail (F : FiniteEdgeFamily I Ω α)
    {P : α → ℝ} {κ δ η τ β t u : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hP0 : ∀ a ∈ F.vertices, κ ≤ P a) (hP1 : ∀ a ∈ F.vertices, P a ≤ 1)
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (hρ : ∀ s, 0 ≤ ρ s) (hρsum : ∑ s, ρ s = 1)
    (e : Finset α) (heV : e ⊆ F.vertices) (v : α) (hve : v ∈ e) (hδ : 0 ≤ δ)
    (hcodeg : ∀ a ∈ F.vertices, a ≠ v → F.codegree v a ≤ δ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1 / 2)
    (ht : 0 < t) (hu : 0 < u) (hbad : ∀ i, F.badNormalizerMass P ρ W τ i ≤ β)
    (hcor : ∀ A ⊆ F.vertices, A.card ≤ e.card + 2 * F.rank →
      |containmentMass ρ W A - survivalProduct P A| ≤ η * survivalProduct P A) :
    (∑ s, if t + u ≤ |F.reweightedVertexDegree P (W s) τ v - F.degree v / P v|
      then conditionedStateMass ρ W e s else 0) ≤
      F.vertexVarianceError P e κ δ η v / t ^ 2 +
        ((β + 2 * τ) * ((1 / κ ^ F.rank) * F.degree v)) / (containmentMass ρ W e * u) := by
  have he := hcor e heV (Nat.le_add_right _ _)
  have hq := containmentMass_pos_of_relative_error
    (fun a ha => hκ0.trans_le (hP0 a (heV ha))) (lt_of_le_of_lt hη (by norm_num)) he
  have hraw := F.rawVertexDegree_tail_from_containment
    hκ0 hκ1 hP0 hP1 ρ W hρ e heV v hve hδ hcodeg hη0 hη ht hcor
  have hloss := F.vertexReplacementLoss_conditioned_tail
    hκ0 hκ1 hP0 ρ W hρ hρsum hτ0 hτ v hbad e hq hu
  exact (finite_triangle_tail_le (conditionedStateMass ρ W e)
    (fun s => F.reweightedVertexDegree P (W s) τ v)
    (fun s => F.rawVertexDegree P (W s) v)
    (fun s => F.vertexReplacementLoss P (W s) τ v)
    (conditionedStateMass_nonneg hρ hq)
    (fun s => F.reweightedVertexDegree_sub_raw_le P (W s) τ v)
    (F.degree v / P v) t u).trans (add_le_add hraw hloss)

end

end Erdos4b.FGKMT.FiniteEdgeFamily
