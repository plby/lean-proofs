/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedCutoffBijection
import ErdosProblems.Erdos4b.GeneralFourierPinnedWeightExpansion

/-!
# Exact pinning of the natural source weight

The positive natural base point prevents truncated subtraction in the
companion forms. Supported summands have both pinned coordinates one,
so the original full square equals the reduced integer square exactly.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def IndexedSourceDivisorCondition {K : ℕ} (w m q n : ℕ)
    (d e : Fin K → ℕ) : Prop :=
  ∀ i, d i ∣ n + primorial w * i.val * q ∧
    e i ∣ m * (n + primorial w * i.val * q) - 1

open Classical in
def indexedSourceWeight {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (P : Finset ℕ) (w m q n : ℕ) (LD LE : ℝ) : ℝ :=
  (∑ d ∈ cutoffDivisorTupleSupport (Fin K) P,
    ∑ e ∈ cutoffDivisorTupleSupport (Fin K) P,
      if IndexedSourceDivisorCondition w m q n d e then
        sourceAnalyticSelbergCoefficient S F G LD LE d e else 0) ^ 2

theorem indexedFirstForm_eq_pinnedIntegerForm
    {K w p₀ q n : ℕ} (h : Fin K) (hpin : n + primorial w * h.val * q = p₀)
    (i : PinnedShiftIndex h) :
    ((n + primorial w * i.val.val * q : ℕ) : ℤ) =
      pinnedFirstIntegerForm h w p₀ q i := by
  have he : (n : ℤ) + (primorial w : ℤ) * h.val * q = p₀ := by exact_mod_cast hpin
  unfold pinnedFirstIntegerForm
  push_cast
  rw [← he]
  ring

theorem indexedSourceDivisorCondition_extend_iff
    {K w m p₀ q n : ℕ} (h : Fin K) (hm : 0 < m) (hn : 0 < n)
    (hpin : n + primorial w * h.val * q = p₀)
    (d e : PinnedShiftIndex h → ℕ) :
    IndexedSourceDivisorCondition w m q n
        (extendPinnedDivisorTuple h d) (extendPinnedDivisorTuple h e) ↔
      PinnedIntegerSingleCondition h w m p₀ q d e := by
  have hform (i : PinnedShiftIndex h) := indexedFirstForm_eq_pinnedIntegerForm h hpin i
  have hcomp (i : PinnedShiftIndex h) :
      ((m * (n + primorial w * i.val.val * q) - 1 : ℕ) : ℤ) =
        (m : ℤ) * pinnedFirstIntegerForm h w p₀ q i - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr
      (Nat.mul_pos hm (by omega : 0 < n + primorial w * i.val.val * q)))]
    push_cast
    rw [← hform]
    push_cast
    rfl
  constructor
  · intro hc i
    have hi := hc i.val
    simp only [extendPinnedDivisorTuple_at_other] at hi
    constructor
    · rw [← hform]
      exact_mod_cast hi.1
    · rw [← hcomp]
      exact_mod_cast hi.2
  · intro hc i
    by_cases hi : i = h
    · subst i
      simp
    · have hd := (hc ⟨i, hi⟩).1
      have he := (hc ⟨i, hi⟩).2
      rw [← hform ⟨i, hi⟩] at hd
      rw [← hcomp ⟨i, hi⟩] at he
      simp only [extendPinnedDivisorTuple, dif_neg hi]
      exact ⟨by exact_mod_cast hd, by exact_mod_cast he⟩

theorem indexedSourceWeight_eq_pinnedSourceIntegerWeight
    {K w m p₀ q n Y : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {LD : ℝ} (hLD : 0 < LD) (hY : 1 < Y) (hm : 0 < m) (hn : 0 < n)
    (hp₀ : p₀.Prime) (hpin : n + primorial w * h.val * q = p₀)
    (hFsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t → F j i t ≠ 0 → t ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1)
    (hD : LD / 10 < Real.log p₀) (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    (indexedSourceWeight S F G P w m q n LD (Real.log Y) : ℂ) =
      pinnedSourceIntegerWeight S F G h P w m p₀ q LD (Real.log Y) := by
  classical
  unfold indexedSourceWeight pinnedSourceIntegerWeight
  push_cast
  simp only [apply_ite Complex.ofReal, Complex.ofReal_zero]
  congr 1
  rw [sum_cutoffDivisorPairs_eq_pinned h P hP _ (by
    intro d hd e he hne
    by_cases hc : IndexedSourceDivisorCondition w m q n d e
    · rw [if_pos hc] at hne
      have hreal : sourceAnalyticSelbergCoefficient S F G LD (Real.log Y) d e ≠ 0 := by
        exact_mod_cast hne
      apply sourceAnalyticSelbergCoefficient_pinned_coordinates_eq_one
        S F G hLD hY hp₀ hFsupport hGsupport hD hcop d e hreal h
      · simpa only [hpin] using (hc h).1
      · simpa only [hpin] using (hc h).2
    · simp only [if_neg hc, ne_eq, not_true_eq_false] at hne)]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  rw [indexedSourceDivisorCondition_extend_iff h hm hn hpin,
    sourceAnalyticSelbergCoefficient_extend_eq_pinned]

end

end Erdos4b
