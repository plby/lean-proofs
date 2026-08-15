/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős 285: the elementary lower bound

This file isolates the elementary half of the asymptotic theorem.  A strictly
increasing list of `k + 1` positive denominators with reciprocal sum one has
last denominator `N` satisfying

`exp 1 / (exp 1 - 1) * (k + 1) ≤ N + 1`.

The proof compares the denominators with the final interval of `k + 1`
positive integers ending at `N`, then telescopes logarithms.  The final `+ 1`
is negligible after division by `k + 1`.
-/

namespace Erdos285Lower

open Filter Finset Real Set
open scoped BigOperators Topology

private lemma strictMono_gap {k : ℕ} {n : Fin (k + 1) → ℕ} (hn : StrictMono n)
    (i : ℕ) (hi : i ≤ k) :
    n ⟨i, Nat.lt_succ_of_le hi⟩ + (k - i) ≤ n (Fin.last k) := by
  induction hi using Nat.decreasingInduction with
  | self =>
      simpa only [Nat.sub_self, add_zero] using
        hn.monotone (show (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ≤ Fin.last k by exact le_rfl)
  | of_succ i hi ih =>
      have hlt :
          n ⟨i, Nat.lt_succ_of_le (Nat.le_of_lt hi)⟩ <
            n ⟨i + 1, Nat.succ_lt_succ_iff.mpr hi⟩ := by
        apply hn
        simp
      omega

/-- The quantitative lower bound behind the elementary half of Erdős 285. -/
theorem max_denominator_lower_bound {k : ℕ} {n : Fin (k + 1) → ℕ}
    (hn : StrictMono n) (hn0 : 0 ∉ Set.range n)
    (hsum : 1 = ∑ i, (1 : ℝ) / n i) :
    Real.exp 1 / (Real.exp 1 - 1) * (k + 1 : ℕ) ≤
      (n (Fin.last k) : ℝ) + 1 := by
  let N := n (Fin.last k)
  let L := N - k
  have hn_pos (i : Fin (k + 1)) : 0 < n i := by
    exact Nat.pos_of_ne_zero fun hi ↦ hn0 ⟨i, hi⟩
  have hgap_zero := strictMono_gap hn 0 (Nat.zero_le k)
  have hkN : k < N := by
    dsimp [N] at hgap_zero
    have := hn_pos (0 : Fin (k + 1))
    omega
  have hL_pos_nat : 0 < L := by
    dsimp [L]
    omega
  have hdenom (i : Fin (k + 1)) : n i ≤ L + i.val := by
    have hi : i.val ≤ k := by omega
    have hgap := strictMono_gap hn i.val hi
    have heq : n ⟨i.val, Nat.lt_succ_of_le hi⟩ = n i := by congr
    rw [heq] at hgap
    dsimp [L, N]
    omega
  have hterm (i : Fin (k + 1)) :
      Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ)) ≤
        (1 : ℝ) / n i := by
    have hLi_pos_nat : 0 < L + i.val := Nat.add_pos_left hL_pos_nat _
    have hLi_pos : (0 : ℝ) < (L + i.val : ℕ) := by exact_mod_cast hLi_pos_nat
    have hratio_pos :
        (0 : ℝ) < ((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ) := by
      positivity
    calc
      Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ))
          ≤ (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ)) - 1 :=
        Real.log_le_sub_one_of_pos hratio_pos
      _ = (1 : ℝ) / (L + i.val : ℕ) := by
        field_simp
        norm_num
      _ ≤ (1 : ℝ) / n i := by
        apply one_div_le_one_div_of_le
        · exact_mod_cast hn_pos i
        · exact_mod_cast hdenom i
  have hlog_sum :
      (∑ i : Fin (k + 1),
          Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ))) ≤ 1 := by
    calc
      (∑ i : Fin (k + 1),
          Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ)))
          ≤ ∑ i : Fin (k + 1), (1 : ℝ) / n i := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = 1 := hsum.symm
  have htel :
      (∑ i : Fin (k + 1),
          Real.log (((L + i.val + 1 : ℕ) : ℝ) / (L + i.val : ℕ))) =
        Real.log (N + 1 : ℕ) - Real.log L := by
    have hlog_step (j : ℕ) :
        Real.log (((L + j + 1 : ℕ) : ℝ) / (L + j : ℕ)) =
          Real.log (L + (j + 1) : ℕ) - Real.log (L + j : ℕ) := by
      rw [Real.log_div (by positivity) (by positivity)]
      norm_num [add_assoc]
    change (∑ i : Fin (k + 1),
      (fun j : ℕ ↦ Real.log (((L + j + 1 : ℕ) : ℝ) / (L + j : ℕ))) i) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ ↦ Real.log (((L + j + 1 : ℕ) : ℝ) / (L + j : ℕ))) (k + 1)]
    simp_rw [hlog_step]
    change (∑ i ∈ Finset.range (k + 1),
      ((fun t : ℕ ↦ Real.log (L + t : ℕ)) (i + 1) -
        (fun t : ℕ ↦ Real.log (L + t : ℕ)) i)) = _
    rw [Finset.sum_range_sub (fun t : ℕ ↦ Real.log (L + t : ℕ)) (k + 1)]
    have hLk : L + k = N := by
      dsimp [L]
      exact Nat.sub_add_cancel (Nat.le_of_lt hkN)
    rw [← hLk]
    norm_num [add_assoc]
  rw [htel] at hlog_sum
  have hlog_ratio : Real.log (((N + 1 : ℕ) : ℝ) / L) ≤ 1 := by
    rw [Real.log_div (by positivity) (by positivity)]
    exact hlog_sum
  have hratio_pos : (0 : ℝ) < (((N + 1 : ℕ) : ℝ) / L) := by positivity
  have hratio : (((N + 1 : ℕ) : ℝ) / L) ≤ Real.exp 1 := by
    have hexp := (Real.exp_le_exp.mpr hlog_ratio)
    rwa [Real.exp_log hratio_pos] at hexp
  have hlinear : ((N + 1 : ℕ) : ℝ) ≤ Real.exp 1 * L := by
    exact (div_le_iff₀ (by exact_mod_cast hL_pos_nat)).mp hratio
  have hexp_sub_pos : (0 : ℝ) < Real.exp 1 - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)
  change Real.exp 1 / (Real.exp 1 - 1) * (k + 1 : ℕ) ≤ (N : ℝ) + 1
  rw [div_mul_eq_mul_div, div_le_iff₀ hexp_sub_pos]
  push_cast
  have hlinear' : ((N : ℝ) + 1) ≤ Real.exp 1 * (L : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_one] at hlinear ⊢
    exact hlinear
  rw [show (L : ℝ) = (N : ℝ) - k by
    dsimp [L]
    rw [Nat.cast_sub (Nat.le_of_lt hkN)]] at hlinear'
  nlinarith

/-- Pointwise lower bound for the least last denominator, in the exact
`IsLeast` formulation used by the formal-conjectures statement. -/
theorem lower_bound_of_isLeast (f : ℕ → ℕ) (S : Set ℕ)
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k)) :
    ∀ k ∈ S, Real.exp 1 / (Real.exp 1 - 1) * (k + 1 : ℕ) ≤ (f k : ℝ) + 1 := by
  intro k hk
  rcases (h k hk).1 with ⟨n, hn, hn0, hsum, hnlast⟩
  rw [← hnlast]
  simpa only [Nat.succ_eq_add_one] using max_denominator_lower_bound hn hn0 hsum

/-- The asymptotic lower-bound half: every positive epsilon may be removed
from the leading constant, eventually and uniformly for represented indices. -/
theorem eventually_lower_bound_of_isLeast (f : ℕ → ℕ) (S : Set ℕ)
    (h : ∀ k ∈ S,
      IsLeast
        { n (Fin.last k) | (n : Fin k.succ → ℕ) (_ : StrictMono n)
          (_ : 0 ∉ Set.range n) (_ : 1 = ∑ i, (1 : ℝ) / n i) }
        (f k))
    { ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, k ∈ S →
      (Real.exp 1 / (Real.exp 1 - 1) - ε) * (k + 1 : ℕ) ≤ f k := by
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop M] with k hk hkS
  have hpoint := lower_bound_of_isLeast f S h k hkS
  have hM_real : (1 : ℝ) / ε < M := by exact_mod_cast hM
  have hεM : (1 : ℝ) < ε * M := by
    have := (div_lt_iff₀ hε).mp hM_real
    simpa [mul_comm] using this
  have hMk : (M : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (hk.trans (Nat.le_add_right k 1))
  have hone : (1 : ℝ) ≤ ε * (k + 1 : ℕ) := by
    exact hεM.le.trans (mul_le_mul_of_nonneg_left hMk hε.le)
  norm_num [Nat.cast_add, Nat.cast_one] at hone
  push_cast at hpoint ⊢
  calc
    (Real.exp 1 / (Real.exp 1 - 1) - ε) * ((k : ℝ) + 1) =
        Real.exp 1 / (Real.exp 1 - 1) * ((k : ℝ) + 1) - ε * ((k : ℝ) + 1) := by ring
    _ ≤ ((f k : ℝ) + 1) - 1 := sub_le_sub hpoint hone
    _ = (f k : ℝ) := by ring

#print axioms Erdos285Lower.max_denominator_lower_bound
#print axioms Erdos285Lower.lower_bound_of_isLeast
#print axioms Erdos285Lower.eventually_lower_bound_of_isLeast

end Erdos285Lower
