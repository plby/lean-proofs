import ErdosProblems.Erdos239.External.Erdos67.BCC
import ErdosProblems.Erdos239.External.Erdos67.MRTMajorArc

/-!
# Embedding the discrete short-interval mean square into a real endpoint integral

The source proof of Lemma 14 performs its high-frequency argument after
integrating the starting point continuously.  A discrete short sum based at
`n` is embedded as a step function on the unit cell `[n,n+1)`.  The cells are
disjoint and have volume one, so this loses no constant at all.
-/

open scoped BigOperators
open Finset MeasureTheory Set

namespace Erdos67

noncomputable section

/-- The ordinary unnormalised short sum based at the integer `n`. -/
def integerShortSum (a : ℕ → ℂ) (n H : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 H, a (n + j)

/-- Step-function embedding of all integer short sums based in `(X,2X]`.
The value based at `n` is placed on the half-open real unit cell `[n,n+1)`.
-/
def realEndpointStepShortSum (a : ℕ → ℂ) (X H : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc X (2 * X),
    (Set.Ico (n : ℝ) ((n : ℝ) + 1)).indicator
      (fun _ ↦ integerShortSum a n H) x

/-- An integer belongs to the real interval `(x,x+H]` throughout the unit
cell `[n,n+1)` exactly when it belongs to the discrete interval `(n,n+H]`.
-/
theorem nat_mem_real_shortInterval_iff
    {n H m : ℕ} {x : ℝ}
    (hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    (x < m ∧ (m : ℝ) ≤ x + H) ↔ m ∈ Finset.Ioc n (n + H) := by
  rw [Finset.mem_Ioc]
  constructor
  · rintro ⟨hxm, hmxH⟩
    constructor
    · exact_mod_cast hx.1.trans_lt hxm
    · have hmcast : (m : ℝ) < (n + H : ℕ) + 1 := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        calc
          (m : ℝ) ≤ x + H := hmxH
          _ < ((n : ℝ) + 1) + H := by
            simpa [add_comm] using add_lt_add_right hx.2 (H : ℝ)
          _ = (n : ℝ) + H + 1 := by ring
      have hmnat : m < n + H + 1 := by exact_mod_cast hmcast
      omega
  · rintro ⟨hnm, hmnH⟩
    constructor
    · have hcast : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
      exact hx.2.trans_le hcast
    · have hcast : (m : ℝ) ≤ n + H := by exact_mod_cast hmnH
      exact hcast.trans (by
        simpa [add_comm] using add_le_add_right hx.1 (H : ℝ))

private theorem unitCells_pointwise_disjoint
    {x : ℝ} {m n : ℕ}
    (hm : x ∈ Set.Ico (m : ℝ) ((m : ℝ) + 1))
    (hn : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    m = n := by
  have hmn : m < n + 1 := by exact_mod_cast (hm.1.trans_lt hn.2)
  have hnm : n < m + 1 := by exact_mod_cast (hn.1.trans_lt hm.2)
  omega

/-- On its own cell the real endpoint embedding is exactly the corresponding
integer short sum. -/
theorem realEndpointStepShortSum_eq_on_unitCell
    (a : ℕ → ℂ) {X H n : ℕ} {x : ℝ}
    (hn : n ∈ Finset.Ioc X (2 * X))
    (hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)) :
    realEndpointStepShortSum a X H x = integerShortSum a n H := by
  classical
  unfold realEndpointStepShortSum
  rw [Finset.sum_eq_single n]
  · exact Set.indicator_of_mem hx _
  · intro m hm hmn
    have hnot : x ∉ Set.Ico (m : ℝ) ((m : ℝ) + 1) := by
      intro hxm
      exact hmn (unitCells_pointwise_disjoint hxm hx)
    exact Set.indicator_of_notMem hnot _
  · intro hnot
    exact (hnot hn).elim

/-- The step embedding is supported in the real interval
`[X+1,2X+1)`. -/
theorem realEndpointStepShortSum_eq_zero_of_not_mem_window
    (a : ℕ → ℂ) {X H : ℕ} {x : ℝ}
    (hx : x ∉ Set.Ico ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1)) :
    realEndpointStepShortSum a X H x = 0 := by
  classical
  unfold realEndpointStepShortSum
  apply Finset.sum_eq_zero
  intro n hn
  have hnbounds := Finset.mem_Ioc.mp hn
  have hsub : Set.Ico (n : ℝ) ((n : ℝ) + 1) ⊆
      Set.Ico ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1) := by
    intro y hy
    constructor
    · have hnat : X + 1 ≤ n := by omega
      exact (by exact_mod_cast hnat : (X : ℝ) + 1 ≤ n) |>.trans hy.1
    · have hnat : n + 1 ≤ 2 * X + 1 := by omega
      exact hy.2.trans_le (by exact_mod_cast hnat)
  exact Set.indicator_of_notMem (fun hxn ↦ hx (hsub hxn)) _

theorem normSq_realEndpointStepShortSum
    (a : ℕ → ℂ) (X H : ℕ) (x : ℝ) :
    Complex.normSq (realEndpointStepShortSum a X H x) =
      ∑ n ∈ Finset.Ioc X (2 * X),
        (Set.Ico (n : ℝ) ((n : ℝ) + 1)).indicator
          (fun _ ↦ Complex.normSq (integerShortSum a n H)) x := by
  classical
  unfold realEndpointStepShortSum
  rw [normSq_sum_eq_sum_normSq_of_pairwise_disjoint]
  · apply Finset.sum_congr rfl
    intro n hn
    by_cases hx : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  · intro m hm n hn hmn
    by_cases hxm : x ∈ Set.Ico (m : ℝ) ((m : ℝ) + 1)
    · by_cases hxn : x ∈ Set.Ico (n : ℝ) ((n : ℝ) + 1)
      · exact (hmn (unitCells_pointwise_disjoint hxm hxn)).elim
      · exact Or.inr (Set.indicator_of_notMem hxn _)
    · exact Or.inl (Set.indicator_of_notMem hxm _)

private theorem integral_unitCell_const (n : ℕ) (c : ℝ) :
    (∫ _x : ℝ in Set.Ico (n : ℝ) ((n : ℝ) + 1), c) = c := by
  rw [setIntegral_const, measureReal_def, Real.volume_Ico]
  norm_num

/-- Exact discrete-to-continuous identity.  In particular, a continuous-x
Perron argument may be run on the step embedding without first sampling its
finite-height Perron transform at integer points. -/
theorem integral_normSq_realEndpointStepShortSum_eq
    (a : ℕ → ℂ) (X H : ℕ) :
    (∫ x : ℝ, Complex.normSq (realEndpointStepShortSum a X H x)) =
      uncenteredShortIntervalMeanSquare a X H := by
  classical
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (normSq_realEndpointStepShortSum a X H))]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [MeasureTheory.integral_indicator measurableSet_Ico]
    unfold uncenteredShortIntervalMeanSquare integerShortSum
    apply Finset.sum_congr rfl
    intro n hn
    exact integral_unitCell_const n _
  · intro n hn
    have hconst : MeasureTheory.IntegrableOn
        (fun _x : ℝ ↦ Complex.normSq (integerShortSum a n H))
        (Set.Ico (n : ℝ) ((n : ℝ) + 1)) := by
      apply MeasureTheory.integrableOn_const
      rw [Real.volume_Ico]
      exact ENNReal.ofReal_ne_top
      exact enorm_ne_top
    exact hconst.integrable_indicator measurableSet_Ico

/-- Restricted-window form of the exact discrete-to-continuous identity. -/
theorem integral_normSq_realEndpointStepShortSum_window_eq
    (a : ℕ → ℂ) (X H : ℕ) :
    (∫ x in Set.Ico ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1),
        Complex.normSq (realEndpointStepShortSum a X H x)) =
      uncenteredShortIntervalMeanSquare a X H := by
  let S : Set ℝ := Set.Ico ((X : ℝ) + 1) (((2 * X : ℕ) : ℝ) + 1)
  have hindicator : S.indicator
      (fun x ↦ Complex.normSq (realEndpointStepShortSum a X H x)) =
      fun x ↦ Complex.normSq (realEndpointStepShortSum a X H x) := by
    funext x
    by_cases hx : x ∈ S
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx,
        realEndpointStepShortSum_eq_zero_of_not_mem_window a hx]
      simp
  rw [show (∫ x in S,
      Complex.normSq (realEndpointStepShortSum a X H x)) =
        ∫ x : ℝ, Complex.normSq (realEndpointStepShortSum a X H x) by
      calc
        (∫ x in S, Complex.normSq (realEndpointStepShortSum a X H x)) =
            ∫ x : ℝ, S.indicator
              (fun x ↦ Complex.normSq (realEndpointStepShortSum a X H x)) x :=
          (MeasureTheory.integral_indicator measurableSet_Ico).symm
        _ = _ := congrArg (fun F : ℝ → ℝ ↦ ∫ x : ℝ, F x) hindicator]
  exact integral_normSq_realEndpointStepShortSum_eq a X H

end

end Erdos67
