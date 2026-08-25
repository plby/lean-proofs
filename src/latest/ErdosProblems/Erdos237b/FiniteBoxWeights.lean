import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Finite step weights on disjoint boxes, before any arithmetic specialization. -/

namespace Erdos237b

open Finset

noncomputable def finiteBoxWeight {ι β : Type*} (I : Finset ι)
    (boxes : ι → Finset β) (coeff : ι → ℝ) (u : β) : ℝ := by
  classical
  exact ∑ i ∈ I, if u ∈ boxes i then coeff i else 0

theorem abs_finiteBoxWeight_le {ι β : Type*} (I : Finset ι)
    (boxes : ι → Finset β) (coeff : ι → ℝ) (u : β) :
    |finiteBoxWeight I boxes coeff u| ≤ ∑ i ∈ I, |coeff i| := by
  classical
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i _
  split_ifs <;> simp

theorem finiteBoxWeight_nonneg {ι β : Type*} (I : Finset ι)
    (boxes : ι → Finset β) (coeff : ι → ℝ) (hc : ∀ i ∈ I, 0 ≤ coeff i) (u : β) :
    0 ≤ finiteBoxWeight I boxes coeff u := by
  classical
  apply sum_nonneg
  intro i hi
  split_ifs
  · exact hc i hi
  · rfl

theorem finiteBoxWeight_le_at {ι β : Type*} (I : Finset ι)
    (boxes : ι → Finset β) (coeff : ι → ℝ)
    (hdisj : (I : Set ι).Pairwise fun i j => Disjoint (boxes i) (boxes j))
    (u : β) (g : ℝ) (hg : 0 ≤ g)
    (hle : ∀ i ∈ I, u ∈ boxes i → coeff i ≤ g) :
    finiteBoxWeight I boxes coeff u ≤ g := by
  classical
  by_cases hex : ∃ i ∈ I, u ∈ boxes i
  · obtain ⟨i, hi, hui⟩ := hex
    have heq : finiteBoxWeight I boxes coeff u = coeff i := by
      unfold finiteBoxWeight
      rw [sum_eq_single i]
      · exact if_pos hui
      · intro j hj hji
        exact if_neg fun huj => disjoint_left.mp (hdisj hj hi hji) huj hui
      · exact fun hn => False.elim (hn hi)
    rw [heq]
    exact hle i hi hui
  · have hz : finiteBoxWeight I boxes coeff u = 0 :=
      sum_eq_zero fun i hi => if_neg fun hui => hex ⟨i, hi, hui⟩
    rw [hz]
    exact hg

theorem sum_finiteBoxWeight_mul {ι β : Type*} (I : Finset ι) (T : Finset β)
    (boxes : ι → Finset β) (coeff : ι → ℝ) (weight : β → ℝ)
    (hsub : ∀ i ∈ I, boxes i ⊆ T) :
    (∑ u ∈ T, finiteBoxWeight I boxes coeff u * weight u) =
      ∑ i ∈ I, coeff i * ∑ u ∈ boxes i, weight u := by
  classical
  simp_rw [finiteBoxWeight, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hfilter : T.filter (fun u => u ∈ boxes i) = boxes i := by
    ext u
    simp only [mem_filter]
    exact ⟨And.right, fun hu => ⟨hsub i hi hu, hu⟩⟩
  simp_rw [ite_mul, zero_mul]
  rw [← sum_filter, hfilter, ← mul_sum]

theorem finiteBoxWeight_sq {ι β : Type*} [DecidableEq β] (I : Finset ι)
    (boxes : ι → Finset β) (coeff : ι → ℝ)
    (hdisj : (I : Set ι).Pairwise fun i j => Disjoint (boxes i) (boxes j)) (u : β) :
    finiteBoxWeight I boxes coeff u ^ 2 =
      ∑ i ∈ I, if u ∈ boxes i then coeff i ^ 2 else 0 := by
  classical
  by_cases h : ∃ i ∈ I, u ∈ boxes i
  · obtain ⟨i, hi, hui⟩ := h
    have hnot (j : ι) (hj : j ∈ I) (hji : j ≠ i) : u ∉ boxes j := by
      intro huj
      exact disjoint_left.mp (hdisj hj hi hji) huj hui
    have hsum : finiteBoxWeight I boxes coeff u = coeff i := by
      unfold finiteBoxWeight
      rw [sum_eq_single i]
      · exact if_pos hui
      · intro j hj hji
        exact if_neg (hnot j hj hji)
      · exact fun hn => False.elim (hn hi)
    rw [hsum, sum_eq_single i]
    · rw [if_pos hui]
    · intro j hj hji
      exact if_neg (hnot j hj hji)
    · exact fun hn => False.elim (hn hi)
  · have hnot : ∀ i ∈ I, u ∉ boxes i := fun i hi hu => h ⟨i, hi, hu⟩
    have hsum : finiteBoxWeight I boxes coeff u = 0 := by
      exact sum_eq_zero fun i hi => if_neg (hnot i hi)
    rw [hsum, zero_pow (by decide)]
    exact (sum_eq_zero fun i hi => if_neg (hnot i hi)).symm

theorem sum_finiteBoxWeight_sq_mul {ι β : Type*} (I : Finset ι) (T : Finset β)
    (boxes : ι → Finset β) (coeff : ι → ℝ) (weight : β → ℝ)
    (hdisj : (I : Set ι).Pairwise fun i j => Disjoint (boxes i) (boxes j))
    (hsub : ∀ i ∈ I, boxes i ⊆ T) :
    (∑ u ∈ T, finiteBoxWeight I boxes coeff u ^ 2 * weight u) =
      ∑ i ∈ I, coeff i ^ 2 * ∑ u ∈ boxes i, weight u := by
  classical
  simp_rw [finiteBoxWeight_sq I boxes coeff hdisj, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  have hfilter : T.filter (fun u => u ∈ boxes i) = boxes i := by
    ext u
    simp only [mem_filter]
    exact ⟨And.right, fun hu => ⟨hsub i hi hu, hu⟩⟩
  simp_rw [ite_mul, zero_mul]
  rw [← sum_filter, hfilter, ← mul_sum]

end Erdos237b
