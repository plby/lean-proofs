import ErdosProblems.Erdos380.PrimeBoxes
import ErdosProblems.Erdos380.PrimePoolDilation

/-! # Normalizing the total mass of prime boxes by the singleton count -/

open scoped BigOperators

namespace Erdos380

def primeBoxMass {k : ℕ} (b : PrimeBox k) : ℕ :=
  (dyadicPrimes (2 ^ b.1)).card * ∏ i, (dyadicPrimes (2 ^ (b.2.1 i))).card

def shiftedPrimeBoxMass {k : ℕ} (b : PrimeBox k) : ℕ :=
  (dyadicPrimes (2 ^ (b.1 + 2))).card * ∏ i, (dyadicPrimes (2 ^ (b.2.1 i + 1))).card

def primeBoxEnlargement (k : ℕ) : ℕ := 64 * 4 ^ k

lemma shiftedPrimeBoxMass_sum_eq_card {k : ℕ} (B : Finset (PrimeBox k)) :
    (∑ b ∈ B, shiftedPrimeBoxMass b) = (B.biUnion shiftedPrimeBoxRecords).card := by
  classical
  rw [Finset.card_biUnion (shiftedPrimeBoxRecords_pairwiseDisjoint B)]
  exact Finset.sum_congr rfl fun b _ => (shiftedPrimeBoxRecords_card b).symm

theorem shiftedPrimeBoxMass_sum_le_largeCofactorSingletons {k N R : ℕ} (hk : 0 < k)
    (B : Finset (PrimeBox k)) (hvalid : ∀ b ∈ B, ValidPrimeBox b)
    (hsize : ∀ b ∈ B, primeBoxBaseValue b ≤ N)
    (hlarge : ∀ b ∈ B, ∀ i, R ≤ 2 ^ (b.2.1 i + 1)) :
    (∑ b ∈ B, shiftedPrimeBoxMass b) ≤
      k.factorial * (largeCofactorSingletons (primeBoxEnlargement k * N) R).card := by
  classical
  rw [shiftedPrimeBoxMass_sum_eq_card]
  refine validPrimeRecords_card_le_largeCofactorSingletons _ ?_ ?_ ?_
  · intro r hr
    obtain ⟨b, hb, hrb⟩ := Finset.mem_biUnion.mp hr
    exact shiftedPrimeBoxRecords_valid (hvalid b hb) hrb
  · intro r hr
    obtain ⟨b, hb, hrb⟩ := Finset.mem_biUnion.mp hr
    exact (shiftedPrimeBoxRecords_value_le hrb).trans (Nat.mul_le_mul_left _ (hsize b hb))
  · intro r hr
    obtain ⟨b, hb, hrb⟩ := Finset.mem_biUnion.mp hr
    let i : Fin k := ⟨0, hk⟩
    have hri := (mem_shiftedPrimeBoxRecords.mp hrb).2.1 i
    have hlow := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hri).1).1
    exact ((hlarge b hb i).trans hlow.le).trans
      ((shiftedPrimeBoxRecords_valid (hvalid b hb) hrb).le_cofactor_largest i)

lemma primeBoxMass_le_shifted {k : ℕ} (b : PrimeBox k)
    (h₀ : (dyadicPrimes (2 ^ b.1)).card ≤ 60 * (dyadicPrimes (2 ^ (b.1 + 2))).card)
    (hi : ∀ i, (dyadicPrimes (2 ^ (b.2.1 i))).card ≤
      60 * (dyadicPrimes (2 ^ (b.2.1 i + 1))).card) :
    primeBoxMass b ≤ 60 ^ (k + 1) * shiftedPrimeBoxMass b := by
  calc
    primeBoxMass b ≤ (60 * (dyadicPrimes (2 ^ (b.1 + 2))).card) *
        ∏ i, 60 * (dyadicPrimes (2 ^ (b.2.1 i + 1))).card :=
      Nat.mul_le_mul h₀ (Finset.prod_le_prod' fun i _ => hi i)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, shiftedPrimeBoxMass, pow_succ]
      ring

theorem exists_primeBoxMass_sum_bound (k : ℕ) (hk : 0 < k) :
    ∃ d₀ : ℕ, ∀ N R : ℕ, ∀ B : Finset (PrimeBox k),
      (∀ b ∈ B, ValidPrimeBox b) → (∀ b ∈ B, primeBoxBaseValue b ≤ N) →
      (∀ b ∈ B, d₀ ≤ b.1) → (∀ b ∈ B, ∀ i, d₀ ≤ b.2.1 i) →
      (∀ b ∈ B, ∀ i, R ≤ 2 ^ (b.2.1 i + 1)) →
      (∑ b ∈ B, primeBoxMass b) ≤ 60 ^ (k + 1) * k.factorial *
        (largeCofactorSingletons (primeBoxEnlargement k * N) R).card := by
  obtain ⟨d₀, hd₀⟩ := exists_dyadic_power_pool_comparison
  refine ⟨d₀, ?_⟩
  intro N R B hvalid hsize hbase htuple hlarge
  calc
    (∑ b ∈ B, primeBoxMass b) ≤ ∑ b ∈ B, 60 ^ (k + 1) * shiftedPrimeBoxMass b := by
      apply Finset.sum_le_sum
      intro b hb
      exact primeBoxMass_le_shifted b (hd₀ b.1 (hbase b hb)).2
        (fun i => (hd₀ (b.2.1 i) (htuple b hb i)).1)
    _ = 60 ^ (k + 1) * ∑ b ∈ B, shiftedPrimeBoxMass b := (Finset.mul_sum ..).symm
    _ ≤ 60 ^ (k + 1) * (k.factorial *
        (largeCofactorSingletons (primeBoxEnlargement k * N) R).card) :=
      Nat.mul_le_mul_left _ (shiftedPrimeBoxMass_sum_le_largeCofactorSingletons hk B hvalid hsize hlarge)
    _ = _ := by ring

/-- The total box mass is bounded by the original singleton count, losing
only a fixed constant and `log N / log R`. The large cofactor condition
allows the prime-compression injection to replace a local smooth-number
asymptotic. -/
theorem exists_primeBoxMass_normalization (k : ℕ) (hk : 0 < k) :
    ∃ d₀ P₀ : ℕ, ∀ N R : ℕ, 1 < R → ∀ B : Finset (PrimeBox k),
      (∀ b ∈ B, ValidPrimeBox b) → (∀ b ∈ B, primeBoxBaseValue b ≤ N) →
      (∀ b ∈ B, d₀ ≤ b.1) → (∀ b ∈ B, ∀ i, d₀ ≤ b.2.1 i) →
      (∀ b ∈ B, ∀ i, max P₀ (128 * primeBoxEnlargement k * R) ≤ 2 ^ (b.2.1 i + 1)) →
      ((∑ b ∈ B, primeBoxMass b) : ℝ) ≤
        (60 ^ (k + 1) * k.factorial * (8 * primeBoxEnlargement k) : ℕ) *
          (Real.log (N : ℝ) / Real.log (R : ℝ)) * (singletonBadUpTo N).card := by
  obtain ⟨d₀, hd₀⟩ := exists_primeBoxMass_sum_bound k hk
  have hC : 1 ≤ primeBoxEnlargement k := by
    unfold primeBoxEnlargement
    have hpow := Nat.one_le_pow k 4 (by norm_num : 1 ≤ 4)
    omega
  obtain ⟨P₀, hP₀⟩ := exists_largeCofactorSingletons_dilation_bound hC
  refine ⟨d₀, P₀, ?_⟩
  intro N R hR B hvalid hsize hbase htuple hlarge
  have hmass := hd₀ N (max P₀ (128 * primeBoxEnlargement k * R)) B hvalid hsize hbase htuple hlarge
  have hcompress := hP₀ N R hR
  calc
    ((∑ b ∈ B, primeBoxMass b) : ℝ) ≤
        (60 ^ (k + 1) * k.factorial : ℕ) *
          ((largeCofactorSingletons (primeBoxEnlargement k * N)
            (max P₀ (128 * primeBoxEnlargement k * R))).card : ℝ) := by exact_mod_cast hmass
    _ ≤ ((60 ^ (k + 1) * k.factorial : ℕ) : ℝ) *
        ((8 * primeBoxEnlargement k : ℝ) * (Real.log (N : ℝ) / Real.log (R : ℝ)) *
          (singletonBadUpTo N).card) := mul_le_mul_of_nonneg_left hcompress (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring

end Erdos380
