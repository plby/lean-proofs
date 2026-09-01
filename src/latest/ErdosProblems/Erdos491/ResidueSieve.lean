import ErdosProblems.Erdos491.PeriodicSieve

/-! # A finite bound for integers avoiding prescribed residue classes -/

open scoped BigOperators

namespace Erdos491

lemma finite_gram_upper {ι κ : Type*}
    (S : Finset ι) (J : Finset κ) (phi : κ → ι → ℝ) (diag weight : κ → ℝ)
    (hw : ∀ i ∈ J, 0 ≤ weight i)
    (hdiag : ∀ i ∈ J, (∑ n ∈ S, phi i n ^ 2) ≤ diag i)
    (hoff : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      |∑ n ∈ S, phi i n * phi j n| ≤ weight i * weight j) :
    (∑ n ∈ S, (∑ i ∈ J, phi i n) ^ 2) ≤
      (∑ i ∈ J, diag i) + (∑ i ∈ J, weight i) ^ 2 := by
  classical
  have hterm : ∀ i ∈ J, ∀ j ∈ J,
      (∑ n ∈ S, phi i n * phi j n) ≤
        (if i = j then diag i else 0) + weight i * weight j := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      simpa only [pow_two] using (hdiag i hi).trans
        (le_add_of_nonneg_right (mul_nonneg (hw i hi) (hw i hi)))
    · rw [if_neg hij, zero_add]
      exact (le_abs_self _).trans (hoff i hi j hj hij)
  have hexp : (∑ n ∈ S, (∑ i ∈ J, phi i n) ^ 2) =
      ∑ i ∈ J, ∑ j ∈ J, ∑ n ∈ S, phi i n * phi j n := by
    simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [hexp]
  calc
    _ ≤ ∑ i ∈ J, ∑ j ∈ J,
        ((if i = j then diag i else 0) + weight i * weight j) :=
      Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ hterm i hi j hj
    _ = (∑ i ∈ J, diag i) + (∑ i ∈ J, weight i) ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        simp [hi]
      · rw [sq]
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul]

theorem residue_second_moment {ι : Type*}
    (Q : Finset ι) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (A : ∀ i, Finset (ZMod (q i))) (T : ℕ)
    (hcop : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → (q i).Coprime (q j)) :
    (∑ n ∈ Finset.range T, (∑ i ∈ Q, centeredResidue (A i) n) ^ 2) ≤
      (T : ℝ) * (∑ i ∈ Q, ((A i).card : ℝ) / q i) +
        (∑ i ∈ Q, (q i : ℝ)) + (∑ i ∈ Q, (q i : ℝ)) ^ 2 := by
  classical
  have h := finite_gram_upper (Finset.range T) Q
    (fun i n ↦ centeredResidue (A i) n)
    (fun i ↦ (T : ℝ) / q i * (A i).card + q i) (fun i ↦ (q i : ℝ))
    (fun i _ ↦ Nat.cast_nonneg _) (fun i _ ↦ centeredResidue_diagonal (A i) T)
    (fun i hi j hj hij ↦ centeredResidue_covariance (hcop i hi j hj hij) (A i) (A j) T)
  convert h using 1
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every member of `P` misses every prescribed residue set. Its contribution
to the second moment is therefore the square of the total excluded density. -/
theorem residue_avoidance_bound {ι : Type*}
    (Q : Finset ι) (q : ι → ℕ) [∀ i, NeZero (q i)]
    (A : ∀ i, Finset (ZMod (q i))) (T : ℕ) (P : Finset ℕ)
    (hP : P ⊆ Finset.range T)
    (hcop : ∀ i ∈ Q, ∀ j ∈ Q, i ≠ j → (q i).Coprime (q j))
    (havoid : ∀ n ∈ P, ∀ i ∈ Q, (n : ZMod (q i)) ∉ A i) :
    (P.card : ℝ) * (∑ i ∈ Q, ((A i).card : ℝ) / q i) ^ 2 ≤
      (T : ℝ) * (∑ i ∈ Q, ((A i).card : ℝ) / q i) +
        (∑ i ∈ Q, (q i : ℝ)) + (∑ i ∈ Q, (q i : ℝ)) ^ 2 := by
  classical
  have hval (n : ℕ) (hn : n ∈ P) :
      (∑ i ∈ Q, centeredResidue (A i) n) =
        -(∑ i ∈ Q, ((A i).card : ℝ) / q i) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [centeredResidue, if_neg (havoid n hn i hi), zero_sub]
  calc
    _ = ∑ n ∈ P, (∑ i ∈ Q, centeredResidue (A i) n) ^ 2 := by
      symm
      calc
        _ = ∑ _n ∈ P, (∑ i ∈ Q, ((A i).card : ℝ) / q i) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hval n hn, neg_sq]
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ Finset.range T, (∑ i ∈ Q, centeredResidue (A i) n) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hP (fun _ _ _ ↦ sq_nonneg _)
    _ ≤ _ := residue_second_moment Q q A T hcop

end Erdos491
