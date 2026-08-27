/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoveringHistory

/-! # Exact prefix marginals of the final covering law -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open FiniteEdgeFamily

universe u v w

variable {I : ℕ → Type u} {Ω : ℕ → Type v}

def coverHistoryPrefix {j m : ℕ} (h : j ≤ m) : CoverHistory I Ω m → CoverHistory I Ω j :=
  Nat.leRecOn (C := fun k => CoverHistory I Ω k → CoverHistory I Ω j)
    h (fun f s => f s.1) id

theorem coverHistoryPrefix_self (j : ℕ) (s : CoverHistory I Ω j) :
    coverHistoryPrefix (Nat.le_refl j) s = s := by
  simp only [coverHistoryPrefix, Nat.leRecOn_self, id_eq]

theorem coverHistoryPrefix_succ {j m : ℕ} (h : j ≤ m)
    (s : CoverHistory I Ω (m + 1)) :
    coverHistoryPrefix (Nat.le_succ_of_le h) s = coverHistoryPrefix h s.1 := by
  unfold coverHistoryPrefix
  rw [Nat.leRecOn_succ h]

theorem coverHistoryPrefix_comp {i j m : ℕ} (hij : i ≤ j) (hjm : j ≤ m)
    (s : CoverHistory I Ω m) :
    coverHistoryPrefix hij (coverHistoryPrefix hjm s) =
      coverHistoryPrefix (hij.trans hjm) s := by
  induction hjm with
  | refl => simp only [coverHistoryPrefix_self]
  | @step m h ih =>
    simp only [coverHistoryPrefix_succ h, coverHistoryPrefix_succ (hij.trans h)]
    exact ih s.1

variable {α : Type w} [∀ j, Fintype (I j)] [∀ j, Fintype (Ω j)]
  [∀ j, DecidableEq (I j)] [DecidableEq α]
  (F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α)

theorem coveringHistory_succ_expectation (V : Finset α) (δ : ℝ) (j : ℕ)
    (hτ : coveringThreshold δ (j + 1) < 1) (f : CoverHistory I Ω j → ℝ) :
    (∑ s : CoverHistory I Ω (j + 1), coveringHistoryMass F V δ (j + 1) s * f s.1) =
      ∑ s : CoverHistory I Ω j, coveringHistoryMass F V δ j s * f s := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  dsimp only
  rw [← Finset.sum_mul, coveringHistoryMass_succ_marginal F V δ j hτ]

theorem coveringHistory_prefix_expectation (V : Finset α) (δ : ℝ) {j m : ℕ}
    (h : j ≤ m) (hτ : ∀ k < m, coveringThreshold δ (k + 1) < 1)
    (f : CoverHistory I Ω j → ℝ) :
    (∑ s : CoverHistory I Ω m, coveringHistoryMass F V δ m s *
      f (coverHistoryPrefix h s)) =
      ∑ t : CoverHistory I Ω j, coveringHistoryMass F V δ j t * f t := by
  induction h with
  | refl => simp only [coverHistoryPrefix_self]
  | @step m h ih =>
    simp_rw [coverHistoryPrefix_succ h]
    rw [coveringHistory_succ_expectation F V δ m (hτ m (Nat.lt_succ_self m))
      (fun t => f (coverHistoryPrefix h t))]
    exact ih (fun k hk => hτ k (Nat.lt_succ_of_lt hk))

theorem coveringHistory_prefix_event (V : Finset α) (δ : ℝ) {j m : ℕ}
    (h : j ≤ m) (hτ : ∀ k < m, coveringThreshold δ (k + 1) < 1)
    (E : CoverHistory I Ω j → Prop) [DecidablePred E] :
    (∑ s : CoverHistory I Ω m,
      if E (coverHistoryPrefix h s) then coveringHistoryMass F V δ m s else 0) =
      ∑ t : CoverHistory I Ω j, if E t then coveringHistoryMass F V δ j t else 0 := by
  simpa only [mul_ite, mul_one, mul_zero] using
    coveringHistory_prefix_expectation F V δ h hτ (fun t => if E t then 1 else 0)

theorem coveringHistory_prefix_containment (V : Finset α) (δ : ℝ) {j m : ℕ}
    (h : j ≤ m) (hτ : ∀ k < m, coveringThreshold δ (k + 1) < 1) (e : Finset α) :
    containmentMass (coveringHistoryMass F V δ m)
      (fun s => coveringRemaining F V j (coverHistoryPrefix h s)) e =
      containmentMass (coveringHistoryMass F V δ j) (coveringRemaining F V j) e := by
  exact coveringHistory_prefix_event F V δ h hτ (fun t => e ⊆ coveringRemaining F V j t)

theorem coveringHistory_prefix_marginal (V : Finset α) (δ : ℝ) {j m : ℕ}
    [DecidableEq (CoverHistory I Ω j)]
    (h : j ≤ m) (hτ : ∀ k < m, coveringThreshold δ (k + 1) < 1)
    (t : CoverHistory I Ω j) :
    (∑ s : CoverHistory I Ω m,
      if coverHistoryPrefix h s = t then coveringHistoryMass F V δ m s else 0) =
      coveringHistoryMass F V δ j t := by
  rw [coveringHistory_prefix_event F V δ h hτ (fun s => s = t)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end

end Erdos4b.FGKMT
