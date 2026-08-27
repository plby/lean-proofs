/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBoundaryMass
import ErdosProblems.Erdos4b.FGKMTBoundarySupport

/-!
# The boundary logarithmic moment

Dividing a squarefree divisor by one of its prime factors injects it
back into the same finite divisor support. Summing the prime logarithms
then bounds the moment by the absolute mass times `∑ (log p) / p`.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem boundarySupport_div_mem {M n p : ℕ} (hM : M ≠ 0)
    (hn : n ∈ boundarySupport M) (hpn : p ∣ n) : n / p ∈ boundarySupport M := by
  obtain ⟨hnsq, hnM⟩ := (mem_boundarySupport hM).mp hn
  have hd := Nat.div_dvd_of_dvd hpn
  exact (mem_boundarySupport hM).mpr ⟨hnsq.squarefree_of_dvd hd, hd.trans hnM⟩

theorem boundary_prime_reciprocal_sum_le {M : ℕ} (hM : M ≠ 0) (p : ℕ) :
    (∑ n ∈ (boundarySupport M).filter (fun n => p ∣ n), 1 / (n : ℝ)) ≤
      (1 / (p : ℝ)) * ∑ n ∈ boundarySupport M, 1 / (n : ℝ) := by
  let s := (boundarySupport M).filter (fun n => p ∣ n)
  let t := s.image (fun n => n / p)
  have hinj : ∀ a ∈ s, ∀ b ∈ s, a / p = b / p → a = b := by
    intro a ha b hb hab
    have haeq := Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2
    have hbeq := Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2
    calc
      a = p * (a / p) := haeq.symm
      _ = p * (b / p) := by rw [hab]
      _ = b := hbeq
  have hsub : t ⊆ boundarySupport M := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
    exact boundarySupport_div_mem hM (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
  have hsum : (∑ n ∈ s, 1 / (n : ℝ)) = (1 / (p : ℝ)) * ∑ n ∈ t, 1 / (n : ℝ) := by
    dsimp only [t]
    rw [Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hprod := Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
    conv_lhs => rw [← hprod, Nat.cast_mul]
    simp only [one_div, mul_inv]
  change (∑ n ∈ s, 1 / (n : ℝ)) ≤ _
  rw [hsum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)

theorem log_eq_sum_primeFactors_of_squarefree {n : ℕ} (hn : Squarefree n) :
    Real.log n = ∑ p ∈ n.primeFactors, Real.log p := by
  calc
    Real.log n = Real.log (∏ p ∈ n.primeFactors, (p : ℝ)) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn]
    _ = ∑ p ∈ n.primeFactors, Real.log p :=
      Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)

theorem boundarySupport_log_sum_le {M : ℕ} (hM : M ≠ 0) :
    (∑ n ∈ boundarySupport M, Real.log n / (n : ℝ)) ≤
      (∑ n ∈ boundarySupport M, 1 / (n : ℝ)) *
        ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ) := by
  have hfactor : ∀ n ∈ boundarySupport M,
      M.primeFactors.filter (fun p => p ∣ n) = n.primeFactors := by
    intro n hn
    obtain ⟨hnsq, hnM⟩ := (mem_boundarySupport hM).mp hn
    ext p
    constructor
    · intro hp
      obtain ⟨hpM, hpn⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hpM, hpn, hnsq.ne_zero⟩
    · intro hp
      have hpn := Nat.dvd_of_mem_primeFactors hp
      exact Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpn.trans hnM, hM⟩, hpn⟩
  have hpoint : ∀ n ∈ boundarySupport M,
      Real.log n / (n : ℝ) =
        ∑ p ∈ M.primeFactors, if p ∣ n then Real.log p / (n : ℝ) else 0 := by
    intro n hn
    rw [← Finset.sum_filter, hfactor n hn, ← Finset.sum_div,
      ← log_eq_sum_primeFactors_of_squarefree ((mem_boundarySupport hM).mp hn).1]
  calc
    _ = ∑ n ∈ boundarySupport M,
        ∑ p ∈ M.primeFactors, if p ∣ n then Real.log p / (n : ℝ) else 0 :=
      Finset.sum_congr rfl hpoint
    _ = ∑ p ∈ M.primeFactors,
        ∑ n ∈ boundarySupport M, if p ∣ n then Real.log p / (n : ℝ) else 0 :=
      Finset.sum_comm
    _ = ∑ p ∈ M.primeFactors, Real.log p *
        ∑ n ∈ (boundarySupport M).filter (fun n => p ∣ n), 1 / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ ∑ p ∈ M.primeFactors, Real.log p *
        ((1 / (p : ℝ)) * ∑ n ∈ boundarySupport M, 1 / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left (boundary_prime_reciprocal_sum_le hM p)
        (Real.log_natCast_nonneg p)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring

theorem preSieveBoundary_log_tsum_le {M : ℕ} (hM : 0 < M) :
    (∑' n, |preSieveBoundary M n| * Real.log n) ≤
      ((M : ℝ) / M.totient) * ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ) := by
  rw [preSieveBoundary_log_tsum_eq hM.ne']
  calc
    _ ≤ (∑ n ∈ boundarySupport M, 1 / (n : ℝ)) *
        ∑ p ∈ M.primeFactors, Real.log p / (p : ℝ) := boundarySupport_log_sum_le hM.ne'
    _ ≤ _ := by
      rw [← preSieveBoundary_abs_tsum_eq hM.ne']
      apply mul_le_mul_of_nonneg_right (preSieveBoundary_abs_tsum_le_totientRatio hM)
      exact Finset.sum_nonneg (fun p _ =>
        div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.preSieveBoundary_log_tsum_le
