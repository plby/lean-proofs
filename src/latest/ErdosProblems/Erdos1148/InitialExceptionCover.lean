import ErdosProblems.Erdos1148.OrderedIntervalLiftCover

/-! # An exceptional initial interval contributes its height cost only once -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma initial_refinement_cost (J K b T G : ℝ) (k : ℕ) :
    (J * Real.exp (b / 2)) * K ^ k * Real.exp (T - b - G / 2) =
      J * K ^ k * Real.exp (T - (b + G) / 2) := by
  calc
    _ = J * K ^ k * (Real.exp (b / 2) * Real.exp (T - b - G / 2)) := by ring
    _ = _ := by
      rw [← Real.exp_add, show b / 2 + (T - b - G / 2) = T - (b + G) / 2 by ring]

theorem ordered_interval_lift_cover_initial_exception {η K J T : ℝ} {E : Set SL(2, ℝ)}
    (hK : 1 ≤ K) (hJ : 1 ≤ J) (hT : 0 ≤ T) (hE : LiftForwardClose η 0 E)
    (hordinary : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → ∀ F ⊆ E,
      LiftForwardClose η s F → LiftCoverBound η t F (K * Real.exp (t - s)))
    (l : List (ℝ × ℝ)) (hpair : l.Pairwise (fun p q => p.2 ≤ q.1))
    (hbounds : ∀ p ∈ l, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ T)
    (hreturn : ∀ p ∈ l, p.1 ≠ 0 → ∀ F ⊆ E, LiftForwardClose η p.1 F →
      LiftCoverBound η p.2 F (K * Real.exp ((p.2 - p.1) / 2)))
    (hinitial : ∀ p ∈ l, p.1 = 0 → LiftCoverBound η p.2 E (J * Real.exp (p.2 / 2))) :
    LiftCoverBound η T E
      (J * K ^ (2 * l.length + 1) * Real.exp (T - (l.map (fun p => p.2 - p.1)).sum / 2)) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  have hpure (hno : ∀ p ∈ l, p.1 ≠ 0) :
      LiftCoverBound η T E
        (J * K ^ (2 * l.length + 1) * Real.exp (T - (l.map (fun p => p.2 - p.1)).sum / 2)) := by
    have hstart := hE.coverBound.mono_bound hJ
    have h := ordered_interval_lift_cover hK0 hordinary l le_rfl hT hpair
      (fun p hp => ⟨(hbounds p hp).1, (hbounds p hp).2.1.le, (hbounds p hp).2.2⟩)
      (fun p hp => hreturn p hp (hno p hp)) hstart
    simpa only [sub_zero] using h
  cases l with
  | nil => exact hpure (by simp)
  | cons p l =>
      have hpair' := List.pairwise_cons.mp hpair
      have hp := hbounds p List.mem_cons_self
      by_cases hp0 : p.1 = 0
      · have hfirst := hinitial p List.mem_cons_self hp0
        have hp2 : 0 ≤ p.2 := hp.1.trans hp.2.1.le
        have htailBounds (q : ℝ × ℝ) (hq : q ∈ l) : p.2 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ T :=
          ⟨hpair'.1 q hq, (hbounds q (List.mem_cons_of_mem p hq)).2.1.le,
            (hbounds q (List.mem_cons_of_mem p hq)).2.2⟩
        have htailReturn (q : ℝ × ℝ) (hq : q ∈ l) : ∀ F ⊆ E,
            LiftForwardClose η q.1 F → LiftCoverBound η q.2 F (K * Real.exp ((q.2 - q.1) / 2)) := by
          apply hreturn q (List.mem_cons_of_mem p hq)
          have hstart := hpair'.1 q hq
          intro hz
          linarith [hp.1, hp.2.1]
        have htail := ordered_interval_lift_cover hK0 hordinary l hp2 hp.2.2 hpair'.2
          htailBounds htailReturn hfirst
        apply htail.mono_bound
        rw [initial_refinement_cost]
        simp only [List.length_cons, List.map_cons, List.sum_cons, hp0, sub_zero]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK (by omega)) hJ0
      · apply hpure
        intro q hq
        rcases List.mem_cons.mp hq with hq | hq
        · simpa only [hq] using hp0
        · have hstart := hpair'.1 q hq
          intro hz
          linarith [hp.1, hp.2.1]

end Erdos1148.DukeArithmetic
