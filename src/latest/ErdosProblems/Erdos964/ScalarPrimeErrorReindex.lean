import ErdosProblems.Erdos964.ScalarSemiprimeDistributionError

/-!
# Reindexing the prime-divisor error

Writing a squarefree modulus as `p*q` turns its prime-divisor error into a
prime-indexed family of squarefree modulus sums. The divisor weight loses
only its fixed base, not a power of the radius.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega

theorem squarefree_prime_divisor_weight (k u p : ℕ) (hu : Squarefree u)
    (hp : p.Prime) (hpu : p ∣ u) :
    ((k ^ ω u : ℕ) : ℝ) = k * ((k ^ ω (u / p) : ℕ) : ℝ) := by
  have hmul : p * (u / p) = u := Nat.mul_div_cancel' hpu
  have hcop : p.Coprime (u / p) := by
    apply Nat.coprime_of_squarefree_mul
    rwa [hmul]
  have hω : ω u = 1 + ω (u / p) := by
    calc
      _ = ω (p * (u / p)) := congrArg ArithmeticFunction.cardDistinctFactors hmul.symm
      _ = _ := by
        rw [ArithmeticFunction.cardDistinctFactors_mul hcop,
          ArithmeticFunction.cardDistinctFactors_apply_prime hp]
  rw [hω, pow_add, pow_one, Nat.cast_mul]

theorem sum_squarefree_prime_divisor_error_le (U k p : ℕ) (hp : p.Prime)
    (E : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q) :
    (∑ u ∈ ((Finset.Ioc 0 U).filter Squarefree).filter (fun u => p ∣ u),
      ((k ^ ω u : ℕ) : ℝ) * E (u / p)) ≤
      k * ∑ q ∈ (Finset.Ioc 0 (U / p)).filter Squarefree, ((k ^ ω q : ℕ) : ℝ) * E q := by
  let T := ((Finset.Ioc 0 U).filter Squarefree).filter (fun u => p ∣ u)
  have hmem (u : ℕ) (hu : u ∈ T) : 0 < u ∧ u ≤ U ∧ Squarefree u ∧ p ∣ u := by
    have hu' := Finset.mem_filter.mp hu
    have hu'' := Finset.mem_filter.mp hu'.1
    have hb := Finset.mem_Ioc.mp hu''.1
    exact ⟨hb.1, hb.2, hu''.2, hu'.2⟩
  have himage : T.image (fun u => u / p) ⊆ (Finset.Ioc 0 (U / p)).filter Squarefree := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    have hu' := hmem u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hu'.1 hu'.2.2.2) hp.pos,
        Nat.div_le_div_right hu'.2.1⟩,
      hu'.2.2.1.squarefree_of_dvd (Nat.div_dvd_of_dvd hu'.2.2.2)⟩
  have hinj : Set.InjOn (fun u => u / p) (↑T : Set ℕ) := by
    intro u hu v hv huv
    have h := congrArg (fun q => p * q) huv
    rwa [Nat.mul_div_cancel' (hmem u hu).2.2.2,
      Nat.mul_div_cancel' (hmem v hv).2.2.2] at h
  calc
    _ = k * ∑ u ∈ T, ((k ^ ω (u / p) : ℕ) : ℝ) * E (u / p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      rw [squarefree_prime_divisor_weight k u p (hmem u hu).2.2.1 hp (hmem u hu).2.2.2]
      ring
    _ = k * ∑ q ∈ T.image (fun u => u / p), ((k ^ ω q : ℕ) : ℝ) * E q := by
      rw [Finset.sum_image hinj]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun q _ _ => mul_nonneg (Nat.cast_nonneg _) (hE q))) (Nat.cast_nonneg k)

theorem sum_squarefree_prime_divisor_errors_le (U k : ℕ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (E : ℕ → ℕ → ℝ) (hE : ∀ p q, 0 ≤ E p q) :
    (∑ u ∈ (Finset.Ioc 0 U).filter Squarefree,
      ((k ^ ω u : ℕ) : ℝ) * ∑ p ∈ P.filter (fun p => p ∣ u), E p (u / p)) ≤
      k * ∑ p ∈ P, ∑ q ∈ (Finset.Ioc 0 (U / p)).filter Squarefree,
        ((k ^ ω q : ℕ) : ℝ) * E p q := by
  have hswap : (∑ u ∈ (Finset.Ioc 0 U).filter Squarefree,
      ((k ^ ω u : ℕ) : ℝ) * ∑ p ∈ P.filter (fun p => p ∣ u), E p (u / p)) =
      ∑ p ∈ P, ∑ u ∈ ((Finset.Ioc 0 U).filter Squarefree).filter (fun u => p ∣ u),
        ((k ^ ω u : ℕ) : ℝ) * E p (u / p) := by
    simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : Squarefree u <;> simp only [hu, ↓reduceIte, Finset.sum_const_zero]
  rw [hswap, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  exact sum_squarefree_prime_divisor_error_le U k p (hP p hp) (E p) (hE p)

end Erdos964
