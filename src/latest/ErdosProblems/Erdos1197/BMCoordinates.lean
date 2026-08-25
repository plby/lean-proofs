import ErdosProblems.Erdos1197.BMPrimes

namespace Erdos1197

open Chebyshev
open MeasureTheory Set
open scoped Asymptotics BigOperators Chebyshev ENNReal

noncomputable section

/-- BM frequency vector on the prime-plus-integer block. -/
def bmAlpha {k ν : ℕ} (p : PrimeIdx k → ℕ) : BMIdx k ν → ℝ
  | Sum.inl i => Real.logb 2 (p i)
  | Sum.inr j => Real.logb 2 (bmIntVal ν j)

/-- BM target vector on the prime-plus-integer block. -/
def bmBeta (k ν : ℕ) : BMIdx k ν → ℝ
  | Sum.inl i => (i : ℝ) / (2 : ℝ) ^ k
  | Sum.inr _ => 0

/-- Flatten the BM sum index to a single `Fin` index for the Kronecker theorem. -/
abbrev bmFlatEquiv (k ν : ℕ) :
    BMIdx k ν ≃ Fin (2 ^ k + (2 ^ (ν - 2) + 1)) :=
  finSumFinEquiv

def bmFlatAlpha {k ν : ℕ} (p : PrimeIdx k → ℕ) :
    Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℝ :=
  bmAlpha p ∘ (bmFlatEquiv k ν).symm

def bmFlatBeta (k ν : ℕ) :
    Fin (2 ^ k + (2 ^ (ν - 2) + 1)) → ℝ :=
  bmBeta k ν ∘ (bmFlatEquiv k ν).symm

lemma bmFlatAlpha_castAdd {k ν : ℕ} (p : PrimeIdx k → ℕ) (i : PrimeIdx k) :
    bmFlatAlpha p (Fin.castAdd (2 ^ (ν - 2) + 1) i) = Real.logb 2 (p i) := by
  simp [bmFlatAlpha, bmAlpha, bmFlatEquiv]

lemma bmFlatAlpha_natAdd {k ν : ℕ} (p : PrimeIdx k → ℕ) (j : IntIdx ν) :
    bmFlatAlpha p (Fin.natAdd (2 ^ k) j) = Real.logb 2 (bmIntVal ν j) := by
  simp [bmFlatAlpha, bmAlpha, bmFlatEquiv]

lemma bmFlatBeta_castAdd {k ν : ℕ} (i : PrimeIdx k) :
    bmFlatBeta k ν (Fin.castAdd (2 ^ (ν - 2) + 1) i) = (i : ℝ) / (2 : ℝ) ^ k := by
  simp [bmFlatBeta, bmBeta, bmFlatEquiv]

lemma bmFlatBeta_natAdd {k ν : ℕ} (j : IntIdx ν) :
    bmFlatBeta k ν (Fin.natAdd (2 ^ k) j) = 0 := by
  simp [bmFlatBeta, bmBeta, bmFlatEquiv]

/-- The first nontrivial prime-grid index, available once `k ≥ 1`. -/
def bmPrimeIdxOne (k : ℕ) (hk : 1 ≤ k) : PrimeIdx k :=
  ⟨1, by
    have hpow : (2 : ℕ) ≤ 2 ^ k := by
      simpa using pow_le_pow_right₀ (show (1 : ℕ) ≤ 2 by decide) hk
    omega⟩

lemma bmBeta_primeIdxOne_eq (k ν : ℕ) (hk : 1 ≤ k) :
    bmBeta k ν (Sum.inl (bmPrimeIdxOne k hk)) = 1 / (2 : ℝ) ^ k := by
  simp [bmBeta, bmPrimeIdxOne]

lemma bmFlatBeta_primeIdxOne_eq (k ν : ℕ) (hk : 1 ≤ k) :
    bmFlatBeta k ν
        (Fin.castAdd (2 ^ (ν - 2) + 1) (bmPrimeIdxOne k hk)) =
      1 / (2 : ℝ) ^ k := by
  simpa [bmFlatBeta, bmBeta, bmFlatEquiv] using bmBeta_primeIdxOne_eq k ν hk

lemma prime_not_dvd_pow_of_not_dvd {p a e : ℕ} (hp : Nat.Prime p) (hnot : ¬ p ∣ a) :
    ¬ p ∣ a ^ e := by
  intro h
  exact hnot (hp.dvd_of_dvd_pow h)

lemma bmIntVal_pos (ν : ℕ) (_hν : 3 ≤ ν) (j : IntIdx ν) : 0 < bmIntVal ν j := by
  have hbase : 0 < 7 * 2 ^ (ν - 3) := by
    have hpow : 0 < 2 ^ (ν - 3) := pow_pos (by omega) _
    omega
  exact lt_of_lt_of_le hbase (Nat.le_add_right _ _)

lemma bm_prime_gt_bmIntVal
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (i : PrimeIdx k) (j : IntIdx ν) :
    bmIntVal ν j < p i := by
  have hj_upper : (bmIntVal ν j : ℝ) ≤ ((9 : ℝ) / 8) * (2 : ℝ) ^ ν :=
    (bmIntVal_mem_Icc ν hν j).2
  have hp_lower : ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) := (hp_window i).1
  have hconst : ((9 : ℝ) / 8) * (2 : ℝ) ^ ν < ((23 : ℝ) / 16) * (2 : ℝ) ^ ν := by
    have hpow : 0 < (2 : ℝ) ^ ν := by positivity
    nlinarith
  have hlt : (bmIntVal ν j : ℝ) < (p i : ℝ) := lt_of_le_of_lt hj_upper (lt_trans hconst hp_lower)
  exact_mod_cast hlt

lemma bm_prime_ne_two
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (i : PrimeIdx k) :
    p i ≠ 2 := by
  have hp_lower : ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) := (hp_window i).1
  have hgt_two : (2 : ℝ) < (p i : ℝ) := by
    have hpow3 : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ ν := by
      exact pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hν
    have hpow : (8 : ℝ) ≤ (2 : ℝ) ^ ν := by
      norm_num at hpow3 ⊢
      exact hpow3
    nlinarith
  exact_mod_cast ne_of_gt hgt_two

lemma bm_prime_not_dvd_intVal
    {k ν : ℕ} (hν : 3 ≤ ν) (p : PrimeIdx k → ℕ)
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hp_window :
      ∀ i, ((23 : ℝ) / 16) * (2 : ℝ) ^ ν < (p i : ℝ) ∧
            (p i : ℝ) < ((3 : ℝ) / 2) * (2 : ℝ) ^ ν)
    (i : PrimeIdx k) (j : IntIdx ν) :
    ¬ p i ∣ bmIntVal ν j := by
  have hlt : bmIntVal ν j < p i := bm_prime_gt_bmIntVal hν p hp_window i j
  have hcop :
      Nat.Coprime (p i) (bmIntVal ν j) :=
    Nat.coprime_of_lt_prime (Nat.ne_of_gt (bmIntVal_pos ν hν j)) hlt (hpPrime i)
  exact (hpPrime i).coprime_iff_not_dvd.mp hcop

lemma bm_prime_not_dvd_other_prime
    {k : ℕ} (p : PrimeIdx k → ℕ)
    (hpPrime : ∀ i, Nat.Prime (p i))
    (hpPairwise : Pairwise (fun i j => p i ≠ p j))
    {i i' : PrimeIdx k} (hii' : i ≠ i') :
    ¬ p i ∣ p i' := by
  intro hdiv
  exact hpPairwise hii' ((Nat.prime_dvd_prime_iff_eq (hpPrime i) (hpPrime i')).1 hdiv)



end

end Erdos1197
