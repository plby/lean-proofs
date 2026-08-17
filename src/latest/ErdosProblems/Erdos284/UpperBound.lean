/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.Basic

/-!
# Erdős Problem 284: the elementary upper bound

A `k + 1`-term representation with first denominator `u` is termwise bounded
above by the reciprocal sum of `u, u+1, ..., u+k`.  Telescoping logarithms
then give the sharp limiting constant `1 / (exp 1 - 1)`.
-/

namespace Erdos284.UpperBound

open Filter Finset Real Set
open scoped BigOperators Topology

noncomputable section

private lemma strictMono_gap_forward {k : ℕ} {n : Fin (k + 1) → ℕ}
    (hn : StrictMono n) (i : ℕ) (hi : i ≤ k) :
    n 0 + i ≤ n ⟨i, Nat.lt_succ_of_le hi⟩ := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hi' : i ≤ k := by omega
      have hprev : n 0 + i ≤ n ⟨i, Nat.lt_succ_of_le hi'⟩ := ih hi'
      have hlt :
          n ⟨i, Nat.lt_succ_of_le hi'⟩ <
            n ⟨i + 1, Nat.succ_lt_succ_iff.mpr hi⟩ := by
        apply hn
        simp
      omega

private lemma one_div_nat_succ_le_log_succ_sub_log {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m + 1 : ℕ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by positivity
  have hsuccpos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hsuccpos hmpos)
  rw [Real.log_div hsuccpos.ne' hmpos.ne'] at h
  have hleft :
      1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) =
        (1 : ℝ) / ((m + 1 : ℕ) : ℝ) := by
    field_simp [hmpos.ne', hsuccpos.ne']
    norm_num
  calc
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ) =
        1 - (((((m + 1 : ℕ) : ℝ)) / (m : ℝ))⁻¹) := hleft.symm
    _ ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := h

/-- The quantitative logarithmic estimate behind the elementary half of
Erdős 284. -/
theorem first_denominator_log_bound {k : ℕ} {n : Fin (k + 1) → ℕ}
    (hn : StrictMono n) (hn0 : 0 ∉ Set.range n)
    (hsum : 1 = ∑ i, (1 : ℝ) / n i) :
    1 ≤ (1 : ℝ) / n 0 +
      Real.log (n 0 + k : ℕ) - Real.log (n 0 : ℕ) := by
  let u := n 0
  have hu : 0 < u := by
    exact Nat.pos_of_ne_zero fun hzero ↦ hn0 ⟨0, hzero⟩
  have hterm (j : Fin k) :
      (1 : ℝ) / n j.succ ≤
        Real.log (u + j.val + 1 : ℕ) - Real.log (u + j.val : ℕ) := by
    have hgap := strictMono_gap_forward hn (j.val + 1) (by omega)
    have hdenom : u + j.val + 1 ≤ n j.succ := by
      have hidx :
          (⟨j.val + 1, by omega⟩ : Fin (k + 1)) = j.succ := by
        ext
        rfl
      rw [hidx] at hgap
      simpa [u, Nat.add_assoc] using hgap
    have hpos : (0 : ℝ) < ((u + j.val + 1 : ℕ) : ℝ) := by positivity
    have hdenomR : ((u + j.val + 1 : ℕ) : ℝ) ≤ (n j.succ : ℝ) := by
      exact_mod_cast hdenom
    calc
      (1 : ℝ) / n j.succ ≤ (1 : ℝ) / (u + j.val + 1 : ℕ) := by
        simpa only using (one_div_le_one_div_of_le hpos hdenomR)
      _ ≤ Real.log (u + j.val + 1 : ℕ) - Real.log (u + j.val : ℕ) := by
        simpa [Nat.add_assoc] using
          (one_div_nat_succ_le_log_succ_sub_log (m := u + j.val) (by omega))
  have hsum_range :
      1 = (1 : ℝ) / n 0 +
        ∑ j : Fin k, (1 : ℝ) / n j.succ := by
    simpa only [Fin.sum_univ_succ] using hsum
  have hsum_le :
      (∑ j : Fin k, (1 : ℝ) / n j.succ) ≤
        ∑ j : Fin k,
          (Real.log (u + j.val + 1 : ℕ) - Real.log (u + j.val : ℕ)) := by
    exact Finset.sum_le_sum fun j _ ↦ hterm j
  have htel :
      (∑ j : Fin k,
          (Real.log (u + j.val + 1 : ℕ) - Real.log (u + j.val : ℕ))) =
        Real.log (u + k : ℕ) - Real.log (u : ℕ) := by
    change (∑ j : Fin k,
      ((fun t : ℕ ↦ Real.log (u + t : ℕ)) (j.val + 1) -
        (fun t : ℕ ↦ Real.log (u + t : ℕ)) j.val)) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦
        (fun t : ℕ ↦ Real.log (u + t : ℕ)) (j + 1) -
          (fun t : ℕ ↦ Real.log (u + t : ℕ)) j) k]
    rw [Finset.sum_range_sub (fun t : ℕ ↦ Real.log (u + t : ℕ)) k]
    simp
  change 1 ≤ (1 : ℝ) / u + Real.log (u + k : ℕ) - Real.log (u : ℕ)
  calc
    1 = (1 : ℝ) / n 0 + ∑ j : Fin k, (1 : ℝ) / n j.succ := hsum_range
    _ ≤ (1 : ℝ) / n 0 +
        ∑ j : Fin k,
          (Real.log (u + j.val + 1 : ℕ) - Real.log (u + j.val : ℕ)) :=
      add_le_add (le_refl _) hsum_le
    _ = (1 : ℝ) / u + Real.log (u + k : ℕ) - Real.log (u : ℕ) := by
      rw [htel]
      dsimp [u]
      ring

/-- Exponentiated form of `first_denominator_log_bound`. -/
theorem first_denominator_exp_bound {k : ℕ} {n : Fin (k + 1) → ℕ}
    (hn : StrictMono n) (hn0 : 0 ∉ Set.range n)
    (hsum : 1 = ∑ i, (1 : ℝ) / n i) :
    Real.exp (1 - (1 : ℝ) / n 0) * (n 0 : ℝ) ≤ n 0 + k := by
  have hu : (0 : ℝ) < n 0 := by
    exact_mod_cast Nat.pos_of_ne_zero fun hzero ↦ hn0 ⟨0, hzero⟩
  have hlog := first_denominator_log_bound hn hn0 hsum
  have hlog' :
      1 - (1 : ℝ) / n 0 ≤
        Real.log (((n 0 + k : ℕ) : ℝ) / n 0) := by
    have hnumNat : 0 < n 0 + k := Nat.add_pos_left (by exact_mod_cast hu) k
    have hnum : (0 : ℝ) < ((n 0 + k : ℕ) : ℝ) := by exact_mod_cast hnumNat
    rw [Real.log_div hnum.ne' hu.ne']
    linarith
  have hexp := Real.exp_le_exp.mpr hlog'
  have hnumNat : 0 < n 0 + k := Nat.add_pos_left (by exact_mod_cast hu) k
  have hnum : (0 : ℝ) < ((n 0 + k : ℕ) : ℝ) := by exact_mod_cast hnumNat
  rw [Real.exp_log (div_pos hnum hu)] at hexp
  have hmul := mul_le_mul_of_nonneg_right hexp hu.le
  calc
    Real.exp (1 - (1 : ℝ) / n 0) * (n 0 : ℝ) ≤
        ((((n 0 + k : ℕ) : ℝ)) / n 0) * (n 0 : ℝ) := hmul
    _ = (n 0 + k : ℕ) := by field_simp [hu.ne']
    _ = (n 0 : ℝ) + k := by push_cast; ring

end

end Erdos284.UpperBound

#print axioms Erdos284.UpperBound.first_denominator_log_bound
#print axioms Erdos284.UpperBound.first_denominator_exp_bound
