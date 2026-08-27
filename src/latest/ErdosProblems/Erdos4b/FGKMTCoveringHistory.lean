/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoveringStage

/-! # Finite histories of the reweighted covering process -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open FiniteEdgeFamily

universe u v w

@[reducible] def CoverHistory (I : ℕ → Type u) (Ω : ℕ → Type v) : ℕ → Type (max u v)
  | 0 => PUnit
  | j + 1 => CoverHistory I Ω j × (I j → Option (Ω j))

variable {I : ℕ → Type u} {Ω : ℕ → Type v} {α : Type w}
  [∀ j, Fintype (I j)] [∀ j, Fintype (Ω j)] [DecidableEq α]

@[reducible] instance coverHistoryFintype [∀ j, DecidableEq (I j)] :
    (j : ℕ) → Fintype (CoverHistory I Ω j)
  | 0 => inferInstanceAs (Fintype PUnit)
  | j + 1 => @instFintypeProd _ _ (coverHistoryFintype j) inferInstance

variable (F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α)

def coveringSurvival : ℕ → α → ℝ
  | 0 => fun _ => 1
  | j + 1 => (F j).nextSurvival (coveringSurvival j)

theorem coveringSurvival_pos (j : ℕ) (a : α) : 0 < coveringSurvival F j a := by
  induction j with
  | zero => exact zero_lt_one
  | succ j ih => exact (F j).nextSurvival_pos ih

theorem coveringSurvival_succ_le (j : ℕ) (a : α) :
    coveringSurvival F (j + 1) a ≤ coveringSurvival F j a :=
  (F j).nextSurvival_le (coveringSurvival_pos F j a).le

theorem coveringSurvival_le_one (j : ℕ) (a : α) : coveringSurvival F j a ≤ 1 := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact (coveringSurvival_succ_le F j a).trans ih

def coveringRemaining (V : Finset α) : (j : ℕ) → CoverHistory I Ω j → Finset α
  | 0, _ => V
  | j + 1, s => (F j).reweightedRemaining (coveringRemaining V j s.1) s.2

def coveringCovered : (j : ℕ) → CoverHistory I Ω j → Finset α
  | 0, _ => ∅
  | j + 1, s => coveringCovered j s.1 ∪ Finset.univ.biUnion
      (fun i => (F j).optionalEdge i (s.2 i))

theorem coveringRemaining_eq_sdiff (V : Finset α) (j : ℕ) (s : CoverHistory I Ω j) :
    coveringRemaining F V j s = V \ coveringCovered F j s := by
  induction j with
  | zero => simp only [coveringRemaining, coveringCovered, Finset.sdiff_empty]
  | succ j ih =>
    change (coveringRemaining F V j s.1) \ _ = V \ (coveringCovered F j s.1 ∪ _)
    rw [ih s.1]
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
    exact and_assoc

theorem coveringRemaining_subset (V : Finset α) (j : ℕ) (s : CoverHistory I Ω j) :
    coveringRemaining F V j s ⊆ V := by
  rw [coveringRemaining_eq_sdiff]
  exact Finset.sdiff_subset

def coveringHistoryMass (V : Finset α) (δ : ℝ) : (j : ℕ) → CoverHistory I Ω j → ℝ
  | 0, _ => 1
  | j + 1, s => (F j).transitionMass (coveringSurvival F j) (coveringRemaining F V j)
      (coveringThreshold δ (j + 1)) (coveringHistoryMass V δ j) s.1 s.2

theorem coveringHistoryMass_nonneg (V : Finset α) (δ : ℝ) (j : ℕ)
    (hτ : ∀ k < j, coveringThreshold δ (k + 1) < 1) (s : CoverHistory I Ω j) :
    0 ≤ coveringHistoryMass F V δ j s := by
  induction j with
  | zero => exact zero_le_one
  | succ j ih =>
    exact (F j).transitionMass_nonneg (fun a _ => coveringSurvival_pos F j a)
      (coveringRemaining F V j) (hτ j (Nat.lt_succ_self j))
      (coveringHistoryMass F V δ j)
      (ih (fun k hk => hτ k (Nat.lt_succ_of_lt hk))) s.1 s.2

variable [∀ j, DecidableEq (I j)]

theorem coveringHistoryMass_succ_marginal (V : Finset α) (δ : ℝ) (j : ℕ)
    (hτ : coveringThreshold δ (j + 1) < 1) (s : CoverHistory I Ω j) :
    (∑ ξ : I j → Option (Ω j), coveringHistoryMass F V δ (j + 1) (s, ξ)) =
      coveringHistoryMass F V δ j s :=
  (F j).transitionMass_marginal (coveringSurvival F j) (coveringRemaining F V j)
    hτ (coveringHistoryMass F V δ j) s

theorem coveringHistoryMass_sum_one (V : Finset α) (δ : ℝ) (j : ℕ)
    (hτ : ∀ k < j, coveringThreshold δ (k + 1) < 1) :
    (∑ s : CoverHistory I Ω j, coveringHistoryMass F V δ j s) = 1 := by
  induction j with
  | zero => simp only [CoverHistory, coveringHistoryMass, Fintype.sum_unique]
  | succ j ih =>
    change (∑ s : CoverHistory I Ω j × (I j → Option (Ω j)),
      coveringHistoryMass F V δ (j + 1) s) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [coveringHistoryMass_succ_marginal F V δ j (hτ j (Nat.lt_succ_self j))]
    exact ih (fun k hk => hτ k (Nat.lt_succ_of_lt hk))

theorem coveringHistory_containment_succ (V : Finset α) (δ : ℝ) (j : ℕ) (e : Finset α) :
    containmentMass (coveringHistoryMass F V δ (j + 1)) (coveringRemaining F V (j + 1)) e =
      (F j).transitionContainmentMass (coveringSurvival F j) (coveringHistoryMass F V δ j)
        (coveringRemaining F V j) (coveringThreshold δ (j + 1)) e := by
  unfold containmentMass transitionContainmentMass
  change (∑ s : CoverHistory I Ω j × (I j → Option (Ω j)), _) = _
  rw [Fintype.sum_prod_type]
  rfl

end

end Erdos4b.FGKMT
