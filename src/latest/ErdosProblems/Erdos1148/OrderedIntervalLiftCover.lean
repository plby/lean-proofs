import ErdosProblems.Erdos1148.FiniteLiftCoverComposition
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Composing ordinary and returning refinements along ordered disjoint intervals -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma interval_refinement_cost (M K S a b T G : ℝ) (k : ℕ) :
    (M * (K * Real.exp (a - S)) * (K * Real.exp ((b - a) / 2))) * K ^ k *
      Real.exp (T - b - G / 2) =
    M * K ^ (k + 2) * Real.exp (T - S - ((b - a) + G) / 2) := by
  calc
    _ = M * K ^ (k + 2) *
        (Real.exp (a - S) * Real.exp ((b - a) / 2) * Real.exp (T - b - G / 2)) := by
      rw [pow_add, pow_two]
      ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      have heq : (a - S + (b - a) / 2) + (T - b - G / 2) =
          T - S - ((b - a) + G) / 2 := by ring
      rw [heq]

theorem ordered_interval_lift_cover {η K : ℝ} {E : Set SL(2, ℝ)} (hK : 0 ≤ K)
    (hordinary : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → ∀ F ⊆ E,
      LiftForwardClose η s F → LiftCoverBound η t F (K * Real.exp (t - s)))
    (l : List (ℝ × ℝ)) :
    ∀ {S T M : ℝ}, 0 ≤ S → S ≤ T → l.Pairwise (fun p q => p.2 ≤ q.1) →
      (∀ p ∈ l, S ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ T) →
      (∀ p ∈ l, ∀ F ⊆ E, LiftForwardClose η p.1 F →
        LiftCoverBound η p.2 F (K * Real.exp ((p.2 - p.1) / 2))) →
      LiftCoverBound η S E M →
      LiftCoverBound η T E
        (M * K ^ (2 * l.length + 1) *
          Real.exp (T - S - (l.map (fun p => p.2 - p.1)).sum / 2)) := by
  induction l with
  | nil =>
      intro S T M hS hST _ _ _ hstart
      have h := hstart.refine (mul_nonneg hK (Real.exp_pos _).le) (hordinary hS hST)
      simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, pow_one, List.map_nil,
        List.sum_nil, zero_div, sub_zero, mul_assoc] using h
  | cons p l ih =>
      intro S T M hS hST hpair hbounds hreturn hstart
      obtain ⟨hSp, hpp, hpT⟩ := hbounds p List.mem_cons_self
      have hfirst := hstart.refine (mul_nonneg hK (Real.exp_pos _).le) (hordinary hS hSp)
      have hsecond := hfirst.refine (mul_nonneg hK (Real.exp_pos _).le)
        (hreturn p List.mem_cons_self)
      have hpair' := List.pairwise_cons.mp hpair
      have htailBounds (q : ℝ × ℝ) (hq : q ∈ l) : p.2 ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ T :=
        ⟨hpair'.1 q hq, (hbounds q (List.mem_cons_of_mem p hq)).2⟩
      have hfinal := ih ((hS.trans hSp).trans hpp) hpT hpair'.2 htailBounds
        (fun q hq => hreturn q (List.mem_cons_of_mem p hq)) hsecond
      rw [interval_refinement_cost] at hfinal
      have hn : 2 * (l.length + 1) + 1 = (2 * l.length + 1) + 2 := by omega
      simpa only [List.length_cons, List.map_cons, List.sum_cons, hn] using hfinal

end Erdos1148.DukeArithmetic
