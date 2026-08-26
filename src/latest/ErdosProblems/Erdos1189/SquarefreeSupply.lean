/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An elementary positive-density supply of squarefree seed divisors.
Informal argument: union bound over square divisors and a telescoping reciprocal sum.
This supplies a weaker density estimate than the asymptotic quoted in Section 6.3
of Pickhardt and Omniscience Research Agent, sufficient for its constructions.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.WeightBounds
import Mathlib.Data.Nat.Squarefree

namespace Erdos1189

open Finset

def squarefreeUpto (N : ℕ) : Finset ℕ := (Ioc 0 N).filter Squarefree

lemma nonsquarefree_count_le (N : ℕ) :
    ((Ioc 0 N).filter (fun n => ¬ Squarefree n)).card ≤
      ∑ d ∈ Icc 2 N, N / d ^ 2 := by
  let M := fun d => (Ioc 0 N).filter (fun n => d ^ 2 ∣ n)
  have hsub : (Ioc 0 N).filter (fun n => ¬ Squarefree n) ⊆ (Icc 2 N).biUnion M := by
    intro n hn
    obtain ⟨hnI, hns⟩ := mem_filter.mp hn
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hnI
    have hp : ∃ p, p.Prime ∧ p * p ∣ n := by
      simpa only [Nat.squarefree_iff_prime_squarefree, not_forall, not_not, exists_prop] using hns
    obtain ⟨p, hp, hpd⟩ := hp
    have hpN : p ≤ N := (Nat.le_of_dvd hn0 ((dvd_mul_right p p).trans hpd)).trans hnN
    exact mem_biUnion.mpr ⟨p, mem_Icc.mpr ⟨hp.two_le, hpN⟩,
      mem_filter.mpr ⟨hnI, by simpa only [pow_two] using hpd⟩⟩
  calc
    _ ≤ ((Icc 2 N).biUnion M).card := card_le_card hsub
    _ ≤ ∑ d ∈ Icc 2 N, (M d).card := card_biUnion_le
    _ = ∑ d ∈ Icc 2 N, N / d ^ 2 := by
      apply sum_congr rfl
      intro d _
      exact Nat.Ioc_filter_dvd_card_eq_div N (d ^ 2)

lemma sum_inv_sq_bound_aux {N : ℕ} (hN : 2 ≤ N) :
    (∑ d ∈ Icc 2 N, (d : ℝ)⁻¹ ^ 2) ≤ 3 / 4 - (N : ℝ)⁻¹ := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hstep : (((N + 1 : ℕ) : ℝ)⁻¹) ^ 2 ≤ (N : ℝ)⁻¹ - ((N + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        field_simp
        nlinarith
      linarith

lemma sum_inv_sq_bound (N : ℕ) : (∑ d ∈ Icc 2 N, (d : ℝ)⁻¹ ^ 2) ≤ 3 / 4 := by
  by_cases hN : 2 ≤ N
  · exact (sum_inv_sq_bound_aux hN).trans (sub_le_self _ (by positivity))
  · have hempty : Icc 2 N = ∅ := Icc_eq_empty_of_lt (by omega)
    rw [hempty, sum_empty]
    norm_num

/-- At least one quarter of every initial interval is squarefree. -/
theorem squarefree_count_quarter (N : ℕ) : N ≤ 4 * (squarefreeUpto N).card := by
  have hbad := nonsquarefree_count_le N
  have hcast : (((Ioc 0 N).filter (fun n => ¬ Squarefree n)).card : ℝ) ≤
      (N : ℝ) * (3 / 4) := by
    calc
      _ ≤ ((∑ d ∈ Icc 2 N, N / d ^ 2 : ℕ) : ℝ) := by exact_mod_cast hbad
      _ = ∑ d ∈ Icc 2 N, ((N / d ^ 2 : ℕ) : ℝ) := by simp only [Nat.cast_sum]
      _ ≤ ∑ d ∈ Icc 2 N, (N : ℝ) * (d : ℝ)⁻¹ ^ 2 := by
        apply sum_le_sum
        intro d _
        have hd := Nat.cast_div_le (α := ℝ) (m := N) (n := d ^ 2)
        simpa only [Nat.cast_pow, div_eq_mul_inv, inv_pow] using hd
      _ = (N : ℝ) * ∑ d ∈ Icc 2 N, (d : ℝ)⁻¹ ^ 2 := (mul_sum _ _ _).symm
      _ ≤ (N : ℝ) * (3 / 4) := mul_le_mul_of_nonneg_left (sum_inv_sq_bound N) (by positivity)
  have hpartition := card_filter_add_card_filter_not (s := Ioc 0 N) Squarefree
  simp only [Nat.card_Ioc, Nat.sub_zero] at hpartition
  change (squarefreeUpto N).card + ((Ioc 0 N).filter (fun n => ¬ Squarefree n)).card = N
    at hpartition
  have hpartition' : ((squarefreeUpto N).card : ℝ) +
      (((Ioc 0 N).filter (fun n => ¬ Squarefree n)).card : ℝ) = N := by
    exact_mod_cast hpartition
  have hout : (N : ℝ) ≤ 4 * (squarefreeUpto N).card := by linarith
  exact_mod_cast hout

end Erdos1189
