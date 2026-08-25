import Util.Bernays.PrimePowerReindex
import Util.Bernays.LocalLogCoefficient
import Util.Bernays.LogWeightRemoval

/-!
# Exact logarithmic convolution for the local norm indicator
-/

namespace Bernays

theorem localParity_log_eq_primePower_sum
    (S : ℕ → Prop) {n : ℕ} (hn : n ≠ 0) :
    localParity S n * Real.log (n : ℝ) =
      ∑ l ∈ n.primeFactors,
        ∑ k ∈ Finset.Icc 1 (n.factorization l),
          localParity S (n / l ^ k) *
            localLogCoeff S l k := by
  rw [PrimePowerConvolution448.weighted_log_eq_sum_primeFactors
    (localParity S) (fun {_ _} hcop =>
      localParity_mul S hcop) hn]
  apply Finset.sum_congr rfl
  intro l hlmem
  have hl : l.Prime := Nat.prime_of_mem_primeFactors hlmem
  let e := n.factorization l
  have hdecomp : l ^ e * ordCompl[l] n = n :=
    Nat.ordProj_mul_ordCompl_eq_self n l
  rw [show ordProj[l] n = l ^ e by rfl,
    localParity_prime_pow_log_convolution S hl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hke : k ≤ e := (Finset.mem_Icc.mp hk).2
  have hquot : n / l ^ k = l ^ (e - k) * ordCompl[l] n := by
    calc
      n / l ^ k = (l ^ e * ordCompl[l] n) / l ^ k := by rw [hdecomp]
      _ = (l ^ k * l ^ (e - k) * ordCompl[l] n) / l ^ k := by
        rw [← Nat.pow_add, Nat.add_sub_of_le hke]
      _ = l ^ (e - k) * ordCompl[l] n := by
        rw [Nat.mul_assoc, Nat.mul_div_right _ (pow_pos hl.pos k)]
  have hcop : (l ^ (e - k)).Coprime (ordCompl[l] n) :=
    (Nat.coprime_ordCompl hl hn).pow_left _
  rw [hquot, localParity_mul S hcop]
  ring


theorem localLogMass_nonneg (S : ℕ → Prop) (N : ℕ) : 0 ≤ localLogMass S N := by
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro k _
  exact localLogCoeff_nonneg S k (Nat.prime_of_mem_primesBelow hp)

theorem localParity_logarithmic_convolution (S : ℕ → Prop) (N : ℕ) :
    logarithmicSum (localParity S) N =
      ∑ m ∈ Finset.Icc 1 N, localParity S m * localLogMass S (N / m) := by
  calc
    logarithmicSum (localParity S) N =
        ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ n.primeFactors,
          ∑ k ∈ Finset.Icc 1 (n.factorization p),
            localParity S (n / p ^ k) * localLogCoeff S p k := by
      apply Finset.sum_congr rfl
      intro n hn
      exact localParity_log_eq_primePower_sum S
        (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1))
    _ = ∑ m ∈ Finset.Icc 1 N, ∑ p ∈ (N / m + 1).primesBelow,
        ∑ k ∈ Finset.Icc 1 (Nat.log p (N / m)), localParity S m * localLogCoeff S p k :=
      primePower_divisor_sum N (fun m p k => localParity S m * localLogCoeff S p k)
    _ = _ := by
      simp only [localLogMass, Finset.mul_sum]

end Bernays
