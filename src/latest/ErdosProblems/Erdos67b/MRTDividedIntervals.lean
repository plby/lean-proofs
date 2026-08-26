import ErdosProblems.Erdos67b.MRTTypicalReduction

/-! # Exact divided short intervals and their starting-point multiplicities -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrtDividedLength (n h d : ℕ) : ℕ := (n + h) / d - n / d

theorem mrtDividedLength_add (n h d : ℕ) :
    n / d + mrtDividedLength n h d = (n + h) / d := by
  have hh : n / d ≤ (n + h) / d := Nat.div_le_div_right (Nat.le_add_right n h)
  unfold mrtDividedLength
  exact Nat.add_sub_of_le hh

theorem mrtDividedLength_eq_or (n h d : ℕ) :
    mrtDividedLength n h d = h / d ∨ mrtDividedLength n h d = h / d + 1 := by
  have hlo : n / d + h / d ≤ (n + h) / d := Nat.div_add_div_le_add_div
  have hhi := Nat.add_div_le_div_add_div_add_one n h d
  unfold mrtDividedLength
  generalize n / d = a at *
  generalize h / d = b at *
  generalize (n + h) / d = c at *
  omega

theorem mrtMem_typicalShortSupport_mul_iff {blocks : Finset (ℕ × ℕ)} {d : ℕ}
    (hd : 0 < d) (hlarge : ∀ I ∈ blocks, ∀ p ∈ primesInBlock I, d < p)
    (Z n h m : ℕ) :
    d * m ∈ typicalShortSupport blocks Z n h ↔
      m ∈ typicalShortSupport blocks (Z / d) (n / d) (mrtDividedLength n h d) := by
  simp only [mem_typicalShortSupport, mem_typicalFactorizationSet_mul_iff hd hlarge,
    mrtDividedLength_add, Nat.div_lt_iff_lt_mul hd, Nat.le_div_iff_mul_le hd, mul_comm]

theorem mrtDivided_start_bounds {Y n d : ℕ} (hn : n ∈ Finset.Ioc Y (2 * Y)) :
    n / d ∈ Finset.Icc (Y / d) (2 * (Y / d) + 1) := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.1 hn
  have hl := Nat.div_le_div_right (c := d) hlo.le
  have hu := Nat.div_le_div_right (c := d) hhi
  have hdouble := Nat.add_div_le_div_add_div_add_one Y Y d
  rw [← two_mul Y] at hdouble
  rw [Finset.mem_Icc]
  generalize Y / d = a at *
  generalize n / d = b at *
  generalize (2 * Y) / d = c at *
  omega

theorem mrtDivided_start_fiber_card_le (Y t : ℕ) {d : ℕ} (hd : 0 < d) :
    ((Finset.Ioc Y (2 * Y)).filter (fun n ↦ n / d = t)).card ≤ d := by
  have hsub : (Finset.Ioc Y (2 * Y)).filter (fun n ↦ n / d = t) ⊆
      Finset.Ico (t * d) ((t + 1) * d) := by
    intro n hn
    have heq := (Finset.mem_filter.1 hn).2
    apply Finset.mem_Ico.2
    constructor
    · exact (Nat.le_div_iff_mul_le hd).1 heq.ge
    · exact (Nat.div_lt_iff_lt_mul hd).1 (by omega)
  have hh := Finset.card_le_card hsub
  simpa only [Nat.card_Ico, Nat.add_mul, one_mul, Nat.add_sub_cancel_left] using hh

theorem mrtSum_divided_starts_le (G : ℕ → ℝ) (hG : ∀ t, 0 ≤ G t)
    (Y : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), G (n / d)) ≤
      (d : ℝ) * ∑ t ∈ Finset.Icc (Y / d) (2 * (Y / d) + 1), G t := by
  classical
  rw [Finset.sum_comp G (fun n ↦ n / d)]
  calc
    _ ≤ ∑ t ∈ (Finset.Ioc Y (2 * Y)).image (fun n ↦ n / d), (d : ℝ) * G t := by
      apply Finset.sum_le_sum
      intro t _
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast mrtDivided_start_fiber_card_le Y t hd) (hG t)
    _ ≤ ∑ t ∈ Finset.Icc (Y / d) (2 * (Y / d) + 1), (d : ℝ) * G t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 ht
        exact mrtDivided_start_bounds hn
      · intro t _ _
        exact mul_nonneg (Nat.cast_nonneg d) (hG t)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem mrtSum_divided_starts_le_dyadic_add_boundary (G : ℕ → ℝ)
    (hG : ∀ t, 0 ≤ G t) (Y : ℕ) {d : ℕ} (hd : 0 < d) {B E : ℝ}
    (hmain : (∑ t ∈ Finset.Ioc (Y / d) (2 * (Y / d)), G t) ≤ B)
    (hleft : G (Y / d) ≤ E) (hright : G (2 * (Y / d) + 1) ≤ E) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), G (n / d)) ≤ (d : ℝ) * (B + 2 * E) := by
  classical
  apply (mrtSum_divided_starts_le G hG Y hd).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  have hset : Finset.Icc (Y / d) (2 * (Y / d) + 1) =
      insert (Y / d) (insert (2 * (Y / d) + 1) (Finset.Ioc (Y / d) (2 * (Y / d)))) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hset, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ioc]; omega),
    Finset.sum_insert (by simp)]
  linarith only [hmain, hleft, hright]

end

end Erdos67b
