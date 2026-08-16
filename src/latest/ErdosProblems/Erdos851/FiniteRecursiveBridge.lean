/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.BetaSieveFundamental
import ErdosProblems.Erdos851.FiniteCombinatorialSieve

/-!
# The finite/recursive Rosser bridge

This file identifies the finite alternating sublist sums with the recursive
Buchstab evaluators.  The finite list is read in increasing order, while the
recursive evaluator reads its reverse.
-/

namespace Erdos851

open List

namespace FiniteRecursiveBridge

open FiniteCombinatorialSieve

variable {α : Type*}

private theorem lowerAdmissible_of_append_right
    (A : List α → Prop) (u v : List α)
    (h : LowerAdmissible A (u ++ v)) :
    LowerAdmissible A v := by
  induction u with
  | nil => simpa using h
  | cons p u ih =>
      exact ih ((lowerAdmissible_cons A p (u ++ v)).mp h).1

private theorem upperAdmissible_of_append_right
    (A : List α → Prop) (u v : List α)
    (h : UpperAdmissible A (u ++ v)) :
    UpperAdmissible A v := by
  induction u with
  | nil => simpa using h
  | cons p u ih =>
      exact ih ((upperAdmissible_cons A p (u ++ v)).mp h).1

private noncomputable def lowerContinuationTerm
    (A : List α → Prop) (g : α → ℝ)
    (selected future : List α) : ℝ := by
  classical
  exact if LowerAdmissible A (selected ++ future).reverse then
    (-1 : ℝ) ^ future.length * chainWeight g future
  else 0

private noncomputable def upperContinuationTerm
    (A : List α → Prop) (g : α → ℝ)
    (selected future : List α) : ℝ := by
  classical
  exact if UpperAdmissible A (selected ++ future).reverse then
    (-1 : ℝ) ^ future.length * chainWeight g future
  else 0

private noncomputable def lowerContinuation
    (A : List α → Prop) (g : α → ℝ)
    (selected remaining : List α) : ℝ :=
  (remaining.sublists'.map (lowerContinuationTerm A g selected)).sum

private noncomputable def upperContinuation
    (A : List α → Prop) (g : α → ℝ)
    (selected remaining : List α) : ℝ :=
  (remaining.sublists'.map (upperContinuationTerm A g selected)).sum

private theorem lowerContinuationTerm_cons
    (A : List α → Prop) (g : α → ℝ)
    (selected : List α) (p : α) (future : List α) :
    lowerContinuationTerm A g selected (p :: future) =
      -(g p * lowerContinuationTerm A g (selected ++ [p]) future) := by
  classical
  unfold lowerContinuationTerm
  have happ : selected ++ p :: future = (selected ++ [p]) ++ future := by
    simp
  rw [happ]
  simp only [List.length_cons, chainWeight_cons, pow_succ]
  split <;> ring

private theorem upperContinuationTerm_cons
    (A : List α → Prop) (g : α → ℝ)
    (selected : List α) (p : α) (future : List α) :
    upperContinuationTerm A g selected (p :: future) =
      -(g p * upperContinuationTerm A g (selected ++ [p]) future) := by
  classical
  unfold upperContinuationTerm
  have happ : selected ++ p :: future = (selected ++ [p]) ++ future := by
    simp
  rw [happ]
  simp only [List.length_cons, chainWeight_cons, pow_succ]
  split <;> ring

private theorem sum_map_neg_mul {β : Type*} (c : ℝ) (f : β → ℝ) :
    ∀ l : List β, (l.map fun a => -(c * f a)).sum = -c * (l.map f).sum
  | [] => by simp
  | a :: l => by
      simp only [List.map_cons, List.sum_cons, sum_map_neg_mul c f l]
      ring

private theorem lowerContinuation_cons
    (A : List α → Prop) (g : α → ℝ)
    (selected : List α) (p : α) (remaining : List α) :
    lowerContinuation A g selected (p :: remaining) =
      lowerContinuation A g selected remaining -
        g p * lowerContinuation A g (selected ++ [p]) remaining := by
  classical
  simp only [lowerContinuation, List.sublists'_cons, List.map_append,
    List.sum_append, List.map_map, Function.comp_def,
    lowerContinuationTerm_cons, sum_map_neg_mul]
  ring

private theorem upperContinuation_cons
    (A : List α → Prop) (g : α → ℝ)
    (selected : List α) (p : α) (remaining : List α) :
    upperContinuation A g selected (p :: remaining) =
      upperContinuation A g selected remaining -
        g p * upperContinuation A g (selected ++ [p]) remaining := by
  classical
  simp only [upperContinuation, List.sublists'_cons, List.map_append,
    List.sum_append, List.map_map, Function.comp_def,
    upperContinuationTerm_cons, sum_map_neg_mul]
  ring

private theorem lowerContinuation_eq_zero_of_selected
    (A : List α → Prop) (g : α → ℝ)
    (selected remaining : List α)
    (hselected : ¬ LowerAdmissible A selected.reverse) :
    lowerContinuation A g selected remaining = 0 := by
  classical
  unfold lowerContinuation
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨future, _hfuture, rfl⟩ := List.mem_map.mp hy
  have hfull : ¬ LowerAdmissible A (selected ++ future).reverse := by
    intro h
    rw [List.reverse_append] at h
    exact hselected
      (lowerAdmissible_of_append_right A future.reverse selected.reverse h)
  unfold lowerContinuationTerm
  rw [if_neg hfull]

private theorem upperContinuation_eq_zero_of_selected
    (A : List α → Prop) (g : α → ℝ)
    (selected remaining : List α)
    (hselected : ¬ UpperAdmissible A selected.reverse) :
    upperContinuation A g selected remaining = 0 := by
  classical
  unfold upperContinuation
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨future, _hfuture, rfl⟩ := List.mem_map.mp hy
  have hfull : ¬ UpperAdmissible A (selected ++ future).reverse := by
    intro h
    rw [List.reverse_append] at h
    exact hselected
      (upperAdmissible_of_append_right A future.reverse selected.reverse h)
  unfold upperContinuationTerm
  rw [if_neg hfull]

private theorem rosserLowerEval_cons
    (stop : List α → Bool) (g : α → ℝ) (fuel : ℕ)
    (selected : List α) (p : α) (remaining : List α) :
    rosserLowerEval stop g (fuel + 1) selected (p :: remaining) =
      rosserLowerEval stop g (fuel + 1) selected remaining -
        g p * rosserUpperEval stop g fuel (selected ++ [p]) remaining := by
  simp only [rosserLowerEval, buchstabChildren_cons, List.map_cons, List.sum_cons]
  ring

private theorem rosserUpperEval_cons
    (stop : List α → Bool) (g : α → ℝ) (fuel : ℕ)
    (selected : List α) (p : α) (remaining : List α) :
    rosserUpperEval stop g (fuel + 1) selected (p :: remaining) =
      rosserUpperEval stop g (fuel + 1) selected remaining -
        (if stop (selected ++ [p]) then
          g p * rosserLowerEval stop g fuel (selected ++ [p]) remaining
        else 0) := by
  simp only [rosserUpperEval, buchstabChildren_cons, List.map_cons, List.sum_cons]
  ring

private theorem lowerContinuation_eq_evals
    (A : List α → Prop) [DecidablePred A] (g : α → ℝ) :
    ∀ remaining : List α, ∀ fuel selected,
      remaining.length ≤ fuel →
      (Even selected.length → LowerAdmissible A selected.reverse →
        lowerContinuation A g selected remaining =
          rosserLowerEval (fun s => decide (A s.reverse)) g fuel selected remaining) ∧
      (Odd selected.length → LowerAdmissible A selected.reverse →
        lowerContinuation A g selected remaining =
          rosserUpperEval (fun s => decide (A s.reverse)) g fuel selected remaining) := by
  intro remaining
  induction remaining with
  | nil =>
      intro fuel selected _hlen
      constructor <;> intro _hpar hadm <;> cases fuel <;>
        simp [lowerContinuation, lowerContinuationTerm, hadm,
          rosserLowerEval, rosserUpperEval]
  | cons p remaining ih =>
      intro fuel selected hlen
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          simp only [List.length_cons] at hlen
          have htail : remaining.length ≤ fuel := by omega
          have htailSucc : remaining.length ≤ fuel + 1 := htail.trans (Nat.le_succ _)
          constructor
          · intro heven hadm
            have hodd : Odd (selected ++ [p]).length := by
              simpa using heven.add_one
            have hnewAdm : LowerAdmissible A (selected ++ [p]).reverse := by
              have hrev : (selected ++ [p]).reverse = p :: selected.reverse := by
                simp
              rw [hrev, lowerAdmissible_cons]
              refine ⟨hadm, ?_⟩
              intro he
              exact False.elim ((Nat.not_even_iff_odd.mpr (by simpa using hodd)) he)
            rw [lowerContinuation_cons, rosserLowerEval_cons,
              (ih (fuel + 1) selected htailSucc).1 heven hadm,
              (ih fuel (selected ++ [p]) htail).2 hodd hnewAdm]
          · intro hodd hadm
            rw [lowerContinuation_cons, rosserUpperEval_cons,
              (ih (fuel + 1) selected htailSucc).2 hodd hadm]
            cases hstop : decide (A (selected ++ [p]).reverse)
            · have hnotA : ¬ A (selected ++ [p]).reverse :=
                of_decide_eq_false hstop
              have heven : Even (selected ++ [p]).length := by
                simpa using hodd.add_one
              have hbad : ¬ LowerAdmissible A (selected ++ [p]).reverse := by
                have hrev : (selected ++ [p]).reverse = p :: selected.reverse := by
                  simp
                rw [hrev, lowerAdmissible_cons]
                intro hnew
                apply hnotA
                rw [hrev]
                exact hnew.2 (by simpa using heven)
              rw [lowerContinuation_eq_zero_of_selected A g
                (selected ++ [p]) remaining hbad]
              simp
            · have hA : A (selected ++ [p]).reverse :=
                of_decide_eq_true hstop
              have heven : Even (selected ++ [p]).length := by
                simpa using hodd.add_one
              have hnewAdm : LowerAdmissible A (selected ++ [p]).reverse := by
                have hrev : (selected ++ [p]).reverse = p :: selected.reverse := by
                  simp
                rw [hrev, lowerAdmissible_cons]
                refine ⟨hadm, fun _ => ?_⟩
                rwa [hrev] at hA
              rw [(ih fuel (selected ++ [p]) htail).1 heven hnewAdm]
              simp

private theorem upperContinuation_eq_evals
    (A : List α → Prop) [DecidablePred A] (g : α → ℝ) :
    ∀ remaining : List α, ∀ fuel selected,
      remaining.length ≤ fuel →
      (Even selected.length → UpperAdmissible A selected.reverse →
        upperContinuation A g selected remaining =
          rosserUpperEval (fun s => decide (A s.reverse)) g fuel selected remaining) ∧
      (Odd selected.length → UpperAdmissible A selected.reverse →
        upperContinuation A g selected remaining =
          rosserLowerEval (fun s => decide (A s.reverse)) g fuel selected remaining) := by
  intro remaining
  induction remaining with
  | nil =>
      intro fuel selected _hlen
      constructor <;> intro _hpar hadm <;> cases fuel <;>
        simp [upperContinuation, upperContinuationTerm, hadm,
          rosserLowerEval, rosserUpperEval]
  | cons p remaining ih =>
      intro fuel selected hlen
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          simp only [List.length_cons] at hlen
          have htail : remaining.length ≤ fuel := by omega
          have htailSucc : remaining.length ≤ fuel + 1 := htail.trans (Nat.le_succ _)
          constructor
          · intro heven hadm
            rw [upperContinuation_cons, rosserUpperEval_cons,
              (ih (fuel + 1) selected htailSucc).1 heven hadm]
            cases hstop : decide (A (selected ++ [p]).reverse)
            · have hnotA : ¬ A (selected ++ [p]).reverse :=
                of_decide_eq_false hstop
              have hodd : Odd (selected ++ [p]).length := by
                simpa using heven.add_one
              have hbad : ¬ UpperAdmissible A (selected ++ [p]).reverse := by
                have hrev : (selected ++ [p]).reverse = p :: selected.reverse := by
                  simp
                rw [hrev, upperAdmissible_cons]
                intro hnew
                apply hnotA
                rw [hrev]
                exact hnew.2 (by simpa using hodd)
              rw [upperContinuation_eq_zero_of_selected A g
                (selected ++ [p]) remaining hbad]
              simp
            · have hA : A (selected ++ [p]).reverse :=
                of_decide_eq_true hstop
              have hodd : Odd (selected ++ [p]).length := by
                simpa using heven.add_one
              have hnewAdm : UpperAdmissible A (selected ++ [p]).reverse := by
                have hrev : (selected ++ [p]).reverse = p :: selected.reverse := by
                  simp
                rw [hrev, upperAdmissible_cons]
                refine ⟨hadm, fun _ => ?_⟩
                rwa [hrev] at hA
              rw [(ih fuel (selected ++ [p]) htail).2 hodd hnewAdm]
              simp
          · intro hodd hadm
            have heven : Even (selected ++ [p]).length := by
              simpa using hodd.add_one
            have hnewAdm : UpperAdmissible A (selected ++ [p]).reverse := by
              have hrev : (selected ++ [p]).reverse = p :: selected.reverse := by
                simp
              rw [hrev, upperAdmissible_cons]
              refine ⟨hadm, ?_⟩
              intro ho
              exact False.elim ((Nat.not_odd_iff_even.mpr (by simpa using heven)) ho)
            rw [upperContinuation_cons, rosserLowerEval_cons,
              (ih (fuel + 1) selected htailSucc).2 hodd hadm,
              (ih fuel (selected ++ [p]) htail).1 heven hnewAdm]

private theorem lowerContinuation_reverse
    (A : List α → Prop) (g : α → ℝ) (P : List α) :
    lowerContinuation A g [] P.reverse = lowerMainTerm A g P := by
  classical
  simp only [lowerContinuation, List.sublists'_reverse, List.map_map,
    lowerMainTerm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  simp [lowerContinuationTerm, lowerTerm, chainWeight]

private theorem upperContinuation_reverse
    (A : List α → Prop) (g : α → ℝ) (P : List α) :
    upperContinuation A g [] P.reverse = upperMainTerm A g P := by
  classical
  simp only [upperContinuation, List.sublists'_reverse, List.map_map,
    upperMainTerm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  simp [upperContinuationTerm, upperTerm, chainWeight]

/-- The finite lower main term is exactly the lower Buchstab evaluator on the
reversed list, with the stopping predicate transported by reversal. -/
theorem lowerMainTerm_eq_rosserLowerEval
    (A : List α → Prop) [DecidablePred A] (g : α → ℝ) (P : List α) :
    lowerMainTerm A g P =
      rosserLowerEval (fun s => decide (A s.reverse)) g P.length [] P.reverse := by
  rw [← lowerContinuation_reverse A g P]
  exact (lowerContinuation_eq_evals A g P.reverse P.length [] (by simp)).1
    (by simp) (by simp)

/-- The finite upper main term is exactly the upper Buchstab evaluator on the
reversed list, with the stopping predicate transported by reversal. -/
theorem upperMainTerm_eq_rosserUpperEval
    (A : List α → Prop) [DecidablePred A] (g : α → ℝ) (P : List α) :
    upperMainTerm A g P =
      rosserUpperEval (fun s => decide (A s.reverse)) g P.length [] P.reverse := by
  rw [← upperContinuation_reverse A g P]
  exact (upperContinuation_eq_evals A g P.reverse P.length [] (by simp)).1
    (by simp) (by simp)

private theorem finiteEulerProduct_eq_buchstabProduct_reverse
    (g : α → ℝ) (P : List α) :
    finiteEulerProduct g P = buchstabProduct g P.reverse := by
  simp [finiteEulerProduct, buchstabProduct, List.map_reverse]

/-- Under the same reversal, the finite lower boundary error is exactly the
recursive lower first-failure boundary mass. -/
theorem lowerBoundaryError_eq_rosserLowerBoundary
    (A : List α → Prop) [DecidablePred A] (g : α → ℝ) (P : List α) :
    lowerBoundaryError A g P =
      rosserLowerBoundary (fun s => decide (A s.reverse)) g
        P.length [] P.reverse := by
  have hrecursive :=
    (rosser_eval_sub_product_eq_boundary
      (fun s => decide (A s.reverse)) g P.length [] P.reverse (by simp)).2
  calc
    lowerBoundaryError A g P =
        finiteEulerProduct g P - lowerMainTerm A g P := by
      rw [lowerMainTerm_eq_euler_sub_boundary]
      ring
    _ = buchstabProduct g P.reverse -
        rosserLowerEval (fun s => decide (A s.reverse)) g
          P.length [] P.reverse := by
      rw [finiteEulerProduct_eq_buchstabProduct_reverse,
        lowerMainTerm_eq_rosserLowerEval]
    _ = rosserLowerBoundary (fun s => decide (A s.reverse)) g
          P.length [] P.reverse := hrecursive

/-- Under the same reversal, the finite upper boundary error is exactly the
recursive upper first-failure boundary mass. -/
theorem upperBoundaryError_eq_rosserUpperBoundary
    (A : List α → Prop) [DecidablePred A] (g : α → ℝ) (P : List α) :
    upperBoundaryError A g P =
      rosserUpperBoundary (fun s => decide (A s.reverse)) g
        P.length [] P.reverse := by
  have hrecursive :=
    (rosser_eval_sub_product_eq_boundary
      (fun s => decide (A s.reverse)) g P.length [] P.reverse (by simp)).1
  calc
    upperBoundaryError A g P =
        upperMainTerm A g P - finiteEulerProduct g P := by
      rw [upperMainTerm_eq_euler_add_boundary]
      ring
    _ = rosserUpperEval (fun s => decide (A s.reverse)) g
          P.length [] P.reverse - buchstabProduct g P.reverse := by
      rw [finiteEulerProduct_eq_buchstabProduct_reverse,
        upperMainTerm_eq_rosserUpperEval]
    _ = rosserUpperBoundary (fun s => decide (A s.reverse)) g
          P.length [] P.reverse := hrecursive

end FiniteRecursiveBridge

end Erdos851
