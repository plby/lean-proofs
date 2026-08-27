/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoveringConditions
import ErdosProblems.Erdos4b.FGKMTCoveringSupport

/-! # The quantitative covering induction on one finite history space -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators
open FiniteEdgeFamily

universe u v w

variable {I : ℕ → Type u} {Ω : ℕ → Type v} {α : Type w}
  [∀ j, Fintype (I j)] [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (I j)] [DecidableEq α]
  {F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α}
  {V : Finset α} {r A m : ℕ} {κ δ D : ℝ}

namespace CoveringConditions

variable (H : CoveringConditions F V r A m κ δ D)

include H

omit [∀ j, DecidableEq (I j)] in
theorem historyMass_nonneg {j : ℕ} (hj : j ≤ m) (s : CoverHistory I Ω j) :
    0 ≤ coveringHistoryMass F V δ j s :=
  coveringHistoryMass_nonneg F V δ j (fun k hk => H.threshold_lt_one k (hk.trans_le hj)) s

theorem historyMass_sum_one {j : ℕ} (hj : j ≤ m) :
    (∑ s : CoverHistory I Ω j, coveringHistoryMass F V δ j s) = 1 :=
  coveringHistoryMass_sum_one F V δ j (fun k hk => H.threshold_lt_one k (hk.trans_le hj))

theorem history_containment_error {j : ℕ} (hj : j ≤ m) (e : Finset α)
    (heV : e ⊆ V) (hsize : e.card + 2 * r * j ≤ A) :
    |containmentMass (coveringHistoryMass F V δ j) (coveringRemaining F V j) e -
      survivalProduct (coveringSurvival F j) e| ≤
      coveringTolerance δ (j + 1) * survivalProduct (coveringSurvival F j) e := by
  induction j generalizing e with
  | zero =>
    have hmass : containmentMass (coveringHistoryMass F V δ 0)
        (coveringRemaining F V 0) e = 1 := by
      simp [containmentMass, coveringHistoryMass, coveringRemaining, heV]
    have hprod : survivalProduct (coveringSurvival F 0) e = 1 := by
      simp [survivalProduct, coveringSurvival]
    rw [hmass, hprod]
    simp only [sub_self, abs_zero, mul_one]
    exact (coveringTolerance_pos H.error_pos _).le
  | succ j ih =>
    have hjm : j < m := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
    have hjle : j ≤ m := Nat.le_of_lt hjm
    have hvertices := H.vertices_eq j hjm
    have hrank := H.rank_le j hjm
    have hbudget : e.card + 2 * (F j).rank ≤ A := by
      simp only [Nat.mul_add, Nat.mul_one] at hsize
      omega
    have hcor (B : Finset α) (hBV : B ⊆ (F j).vertices)
        (hB : B.card ≤ e.card + 2 * (F j).rank) :
        |containmentMass (coveringHistoryMass F V δ j) (coveringRemaining F V j) B -
          survivalProduct (coveringSurvival F j) B| ≤
          coveringTolerance δ (j + 1) * survivalProduct (coveringSurvival F j) B := by
      apply ih hjle B (hvertices ▸ hBV)
      simp only [Nat.mul_add, Nat.mul_one] at hsize
      omega
    rw [coveringHistory_containment_succ]
    exact (F j).transitionContainmentMass_covering_error e H.size_pos H.degree_ge_one
      (Nat.succ_pos j) H.survival_pos H.survival_le_one H.error_pos
      (H.stage_smallness hj) hbudget (H.labels_pos j hjm)
      (fun a ha => H.survival_lower j hjle a (hvertices ▸ ha))
      (fun a _ => coveringSurvival_le_one F j a)
      (coveringHistoryMass F V δ j) (coveringRemaining F V j)
      (H.historyMass_nonneg hjle) (H.historyMass_sum_one hjle)
      (hvertices.symm ▸ heV)
      (fun a ha b hb hba => H.codegree_bound j hjm a (heV ha) b (hvertices ▸ hb) hba)
      (fun a ha => H.degree_bound j hjm a (heV ha)) hcor
      (fun i a ha => H.vertex_bound j hjm i a (hvertices ▸ ha))

theorem final_prefix_containment_error {j : ℕ} (hj : j ≤ m) (e : Finset α)
    (heV : e ⊆ V) (hsize : e.card + 2 * r * j ≤ A) :
    |containmentMass (coveringHistoryMass F V δ m)
      (fun s => coveringRemaining F V j (coverHistoryPrefix hj s)) e -
      survivalProduct (coveringSurvival F j) e| ≤
      coveringTolerance δ (j + 1) * survivalProduct (coveringSurvival F j) e := by
  rw [coveringHistory_prefix_containment F V δ hj H.threshold_lt_one e]
  exact H.history_containment_error hj e heV hsize

omit [∀ j, DecidableEq (I j)] in
theorem final_selectedEdge_support {j : ℕ} (hj : j < m) (s : CoverHistory I Ω m)
    (hs : 0 < coveringHistoryMass F V δ m s) (i : I j) :
    coveringSelectedEdge F hj s i = ∅ ∨
      ∃ ω, 0 < (F j).mass i ω ∧ coveringSelectedEdge F hj s i = (F j).edge i ω :=
  coveringSelectedEdge_support F V δ hj H.threshold_lt_one s hs i

end CoveringConditions

end

end Erdos4b.FGKMT
