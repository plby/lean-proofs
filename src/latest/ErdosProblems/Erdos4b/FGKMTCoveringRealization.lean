/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoveringLaw

/-! # A deterministic covering realization in the support of the joint law -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open FiniteEdgeFamily

theorem exists_pos_mass_le_mean {Ξ : Type*} [Fintype Ξ] (ρ value : Ξ → ℝ)
    (hρ : ∀ s, 0 ≤ ρ s) (hsum : ∑ s, ρ s = 1) :
    ∃ s, 0 < ρ s ∧ value s ≤ ∑ t, ρ t * value t := by
  classical
  have hpos : ∃ s, 0 < ρ s := by
    by_contra! hno
    have hzero : ∑ s, ρ s = 0 := Finset.sum_eq_zero
      (fun s _ => le_antisymm (hno s) (hρ s))
    linarith
  let T := Finset.univ.filter fun s => 0 < ρ s
  have hT : T.Nonempty := by
    obtain ⟨s, hs⟩ := hpos
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩⟩
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image T value hT
  refine ⟨s, (Finset.mem_filter.mp hs).2, ?_⟩
  calc
    value s = (∑ t, ρ t) * value s := by rw [hsum, one_mul]
    _ = ∑ t, ρ t * value s := by rw [Finset.sum_mul]
    _ ≤ ∑ t, ρ t * value t := by
      apply Finset.sum_le_sum
      intro t ht
      by_cases hpt : 0 < ρ t
      · exact mul_le_mul_of_nonneg_left (hmin t (Finset.mem_filter.mpr ⟨ht, hpt⟩)) (hρ t)
      · have hzero : ρ t = 0 := le_antisymm (le_of_not_gt hpt) (hρ t)
        simp only [hzero, zero_mul, le_refl]

theorem covering_cardinality_expectation {Ξ α : Type*} [Fintype Ξ] [DecidableEq α]
    (ρ : Ξ → ℝ) (W : Ξ → Finset α) (V : Finset α) (hW : ∀ s, W s ⊆ V) :
    (∑ s, ρ s * (W s).card) = ∑ a ∈ V, containmentMass ρ W {a} := by
  have hcard s : ((W s).card : ℝ) = ∑ a ∈ V, if a ∈ W s then (1 : ℝ) else 0 := by
    calc
      ((W s).card : ℝ) = ∑ _a ∈ W s, (1 : ℝ) := by simp
      _ = ∑ a ∈ W s, if a ∈ W s then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [if_pos ha]
      _ = ∑ a ∈ V, if a ∈ W s then (1 : ℝ) else 0 := by
        apply Finset.sum_subset (hW s)
        intro a _ ha
        exact if_neg ha
  simp_rw [hcard, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp only [containmentMass, Finset.singleton_subset_iff]

universe u v w

variable {I : ℕ → Type u} {Ω : ℕ → Type v} {α : Type w}
  [∀ j, Fintype (I j)] [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (I j)] [DecidableEq α]
  {F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α}
  {V : Finset α} {r A m : ℕ} {κ δ D : ℝ}

namespace CoveringConditions

variable (H : CoveringConditions F V r A m κ δ D)

include H

theorem remaining_card_mean_le (hsize : 1 + 2 * r * m ≤ A) :
    (∑ s : CoverHistory I Ω m,
      coveringHistoryMass F V δ m s * (coveringRemaining F V m s).card) ≤
      (1 + coveringTolerance δ (m + 1)) * ∑ a ∈ V, coveringSurvival F m a := by
  rw [covering_cardinality_expectation _ _ V (coveringRemaining_subset F V m),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hcor := (abs_le.mp (H.history_containment_error le_rfl {a}
    (Finset.singleton_subset_iff.mpr ha) (by simpa only [Finset.card_singleton] using hsize))).2
  simp only [survivalProduct, Finset.prod_singleton] at hcor
  linarith

omit [∀ j, DecidableEq (I j)] in
theorem exists_supported_covering_history (hsize : 1 + 2 * r * m ≤ A) :
    ∃ s : CoverHistory I Ω m, 0 < coveringHistoryMass F V δ m s ∧
      ((coveringRemaining F V m s).card : ℝ) ≤
        (1 + coveringTolerance δ (m + 1)) * ∑ a ∈ V, coveringSurvival F m a := by
  classical
  obtain ⟨s, hs, hmean⟩ := exists_pos_mass_le_mean (coveringHistoryMass F V δ m)
    (fun s => ((coveringRemaining F V m s).card : ℝ))
    (H.historyMass_nonneg le_rfl) (H.historyMass_sum_one le_rfl)
  exact ⟨s, hs, hmean.trans (H.remaining_card_mean_le hsize)⟩

end CoveringConditions

end

end Erdos4b.FGKMT
