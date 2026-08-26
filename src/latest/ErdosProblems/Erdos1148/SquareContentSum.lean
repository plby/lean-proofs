import ErdosProblems.Erdos1148.SquareContent
import ErdosProblems.Erdos1148.BasicLemmaArithmetic

/-!
# Summing the common square-divisor factor

Each greatest square divisor contributes one term of the square-divisor
sum. Interchanging the two finite sums reduces to the checked count of
noncentral multiples and gives a logarithmic loss.
-/

namespace Erdos1148.DukeArithmetic

lemma pairSquareContent_mem_squareDivisors {d : ℕ} (hd : 0 < d) (ℓ : ℤ) :
    pairSquareContent d ℓ ∈ squareDivisors d := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hG : (d : ℤ).natAbs.gcd ℓ.natAbs ≠ 0 := by
    intro hG
    exact (Int.natAbs_ne_zero.mpr hdZ) (Nat.gcd_eq_zero_iff.mp hG).1
  have hf0 : pairSquareContent d ℓ ≠ 0 := squareContentRoot_ne_zero _ hG
  apply (mem_squareDivisors hd.ne').mpr
  refine ⟨Nat.pos_of_ne_zero hf0, ?_⟩
  exact_mod_cast (pairSquareContent_sq_dvd d ℓ hdZ).1

lemma pairSquareContent_le_squareDivisor_sum {d : ℕ} (hd : 0 < d) (ℓ : ℤ) :
    (pairSquareContent d ℓ : ℝ) ≤
      ∑ f ∈ squareDivisors d, if (f : ℤ) ^ 2 ∣ ℓ then (f : ℝ) else 0 := by
  classical
  have hmem := pairSquareContent_mem_squareDivisors hd ℓ
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdiv := (pairSquareContent_sq_dvd d ℓ hdZ).2
  have h := Finset.single_le_sum (s := squareDivisors d)
    (f := fun f : ℕ => if (f : ℤ) ^ 2 ∣ ℓ then (f : ℝ) else 0)
    (fun f _ => by
      split_ifs
      · exact Nat.cast_nonneg f
      · exact le_rfl) hmem
  simpa only [if_pos hdiv] using h

lemma sum_squareDivisor_weight_eq (center L : ℤ) (f : ℕ) :
    (∑ ℓ ∈ noncentralMultiples center L 1, if (f : ℤ) ^ 2 ∣ ℓ then (f : ℝ) else 0) =
      (f : ℝ) * (noncentralMultiples center L ((f : ℤ) ^ 2)).card := by
  classical
  have hfilter : (noncentralMultiples center L 1).filter (fun ℓ => (f : ℤ) ^ 2 ∣ ℓ) =
      noncentralMultiples center L ((f : ℤ) ^ 2) := by
    ext ℓ
    simp [noncentralMultiples, and_assoc, and_left_comm, and_comm]
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem sum_pairSquareContent_le {d : ℕ} {L : ℤ} (hd : 0 < d) (hL : 0 ≤ L) :
    (∑ ℓ ∈ noncentralMultiples (2 * d) L 1, (pairSquareContent d ℓ : ℝ)) ≤
      2 * (L : ℝ) * (1 + Real.log d) := by
  classical
  calc
    _ ≤ ∑ ℓ ∈ noncentralMultiples (2 * d) L 1,
        ∑ f ∈ squareDivisors d, if (f : ℤ) ^ 2 ∣ ℓ then (f : ℝ) else 0 :=
      Finset.sum_le_sum (fun ℓ _ => pairSquareContent_le_squareDivisor_sum hd ℓ)
    _ = ∑ f ∈ squareDivisors d,
        (f : ℝ) * (noncentralMultiples (2 * d) L ((f : ℤ) ^ 2)).card := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun f _ => sum_squareDivisor_weight_eq _ _ f)
    _ ≤ _ := sum_weighted_card_noncentralMultiples_le hd hL

theorem sum_pairSquareContent_le_rpow {d : ℕ} {L : ℤ} {ε : ℝ}
    (hd : 0 < d) (hL : 0 ≤ L) (hε : 0 < ε) :
    (∑ ℓ ∈ noncentralMultiples (2 * d) L 1, (pairSquareContent d ℓ : ℝ)) ≤
      (2 * (1 + ε⁻¹)) * L * (d : ℝ) ^ ε := by
  classical
  calc
    _ ≤ ∑ ℓ ∈ noncentralMultiples (2 * d) L 1,
        ∑ f ∈ squareDivisors d, if (f : ℤ) ^ 2 ∣ ℓ then (f : ℝ) else 0 :=
      Finset.sum_le_sum (fun ℓ _ => pairSquareContent_le_squareDivisor_sum hd ℓ)
    _ = ∑ f ∈ squareDivisors d,
        (f : ℝ) * (noncentralMultiples (2 * d) L ((f : ℤ) ^ 2)).card := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun f _ => sum_squareDivisor_weight_eq _ _ f)
    _ ≤ _ := sum_weighted_card_noncentralMultiples_le_rpow hd hL hε

end Erdos1148.DukeArithmetic
