import ErdosProblems.Erdos421.FiniteDifferenceCalculus

/-! # Uniform bounds for reciprocal differences of every order -/

namespace Erdos421

noncomputable def differenceCoefficient (k : ℕ) (hs : List ℝ) : ℝ :=
  ((k + 1).ascFactorial hs.length : ℝ) * hs.prod

theorem differenceCoefficient_nonneg (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) : 0 ≤ differenceCoefficient k hs := by
  unfold differenceCoefficient
  exact mul_nonneg (Nat.cast_nonneg _) (List.prod_nonneg hhs)

theorem differenceCoefficient_cons (k : ℕ) (h : ℝ) (hs : List ℝ) :
    differenceCoefficient k (h :: hs) =
      ((k + 1 : ℕ) : ℝ) * h * differenceCoefficient (k + 1) hs := by
  have hc : (k + 1).ascFactorial (hs.length + 1) =
      (k + 1) * (k + 2).ascFactorial hs.length := by
    rw [Nat.ascFactorial_succ, ← Nat.succ_ascFactorial]
  simp only [differenceCoefficient, List.length_cons, List.prod_cons, hc, Nat.cast_mul]
  ring

theorem reciprocalDifference_bounds (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {x : ℝ} (hx : 0 < x) :
    differenceCoefficient k hs / (x + hs.sum) ^ (k + 1 + hs.length) ≤
        reciprocalDifference k hs x ∧
      reciprocalDifference k hs x ≤ differenceCoefficient k hs / x ^ (k + 1 + hs.length) := by
  induction hs generalizing k x with
  | nil => simp [differenceCoefficient, reciprocalDifference, iteratedDifference]
  | cons h hs ih =>
    have hh : 0 ≤ h := hhs h (List.mem_cons_self ..)
    have htail : ∀ a ∈ hs, 0 ≤ a := fun a ha ↦ hhs a (List.mem_cons_of_mem h ha)
    by_cases hh0 : h = 0
    · subst h
      simp [reciprocalDifference_cons, differenceCoefficient_cons]
    have hhp : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
    obtain ⟨c, hc, heq⟩ := reciprocalDifference_mean_value k hs htail hx hhp
    have hcp : 0 < c := hx.trans hc.1
    have hb := ih (k := k + 1) htail hcp
    have hsum : 0 ≤ hs.sum := List.sum_nonneg htail
    have hcoef : 0 ≤ differenceCoefficient (k + 1) hs := differenceCoefficient_nonneg _ _ htail
    have hA : 0 ≤ ((k + 1 : ℕ) : ℝ) * h := by positivity
    rw [heq, differenceCoefficient_cons]
    simp only [List.sum_cons, List.length_cons]
    have hpower : k + 1 + (hs.length + 1) = k + 1 + 1 + hs.length := by omega
    rw [hpower]
    constructor
    · calc
        _ = (((k + 1 : ℕ) : ℝ) * h) *
            (differenceCoefficient (k + 1) hs / (x + (h + hs.sum)) ^ (k + 1 + 1 + hs.length)) := by
              ring
        _ ≤ (((k + 1 : ℕ) : ℝ) * h) *
            (differenceCoefficient (k + 1) hs / (c + hs.sum) ^ (k + 1 + 1 + hs.length)) := by
          apply mul_le_mul_of_nonneg_left _ hA
          apply div_le_div_of_nonneg_left hcoef (by positivity)
          exact pow_le_pow_left₀ (by positivity) (by linarith [hc.2]) _
        _ ≤ _ := mul_le_mul_of_nonneg_left hb.1 hA
    · calc
        _ ≤ (((k + 1 : ℕ) : ℝ) * h) *
            (differenceCoefficient (k + 1) hs / c ^ (k + 1 + 1 + hs.length)) :=
          mul_le_mul_of_nonneg_left hb.2 hA
        _ ≤ (((k + 1 : ℕ) : ℝ) * h) *
            (differenceCoefficient (k + 1) hs / x ^ (k + 1 + 1 + hs.length)) := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact div_le_div_of_nonneg_left hcoef (by positivity)
            (pow_le_pow_left₀ hx.le hc.1.le _)
        _ = _ := by ring

theorem reciprocalDifference_nonneg (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {x : ℝ} (hx : 0 < x) :
    0 ≤ reciprocalDifference k hs x := by
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  have hcoef := differenceCoefficient_nonneg k hs hhs
  exact (by positivity : 0 ≤ differenceCoefficient k hs / (x + hs.sum) ^ (k + 1 + hs.length)).trans
    (reciprocalDifference_bounds k hs hhs hx).1

theorem differenceCoefficient_pos (k : ℕ) (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) : 0 < differenceCoefficient k hs := by
  unfold differenceCoefficient
  exact mul_pos (by exact_mod_cast Nat.ascFactorial_pos k hs.length) (List.prod_pos hhs)

end Erdos421
