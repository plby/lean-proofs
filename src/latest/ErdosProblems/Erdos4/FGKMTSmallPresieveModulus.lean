import ErdosProblems.Erdos4.FGKMTHarmonicModulusSize

/-! Omit the exceptional prime only from the small-prime mask; the density loss is at most two. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

def smallPresievePrimeSet (D B : ℕ) : Finset ℕ := (Nat.primesLE D).erase B

def smallPresieveModulus (D B : ℕ) : ℕ := ∏ p ∈ smallPresievePrimeSet D B, p

theorem smallPresieveModulus_pos (D B : ℕ) : 0 < smallPresieveModulus D B := by
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primesLE (Finset.mem_erase.mp hp).2).pos

theorem smallPresieveModulus_dvd_primorial (D B : ℕ) : smallPresieveModulus D B ∣ primorial D := by
  by_cases hB : B ∈ Nat.primesLE D
  · have heq : smallPresieveModulus D B * B = primorial D := by
      rw [primorial_eq_prod_primesLE]
      exact Finset.prod_erase_mul (Nat.primesLE D) id hB
    rw [← heq]
    exact dvd_mul_right _ _
  · unfold smallPresieveModulus smallPresievePrimeSet
    rw [Finset.erase_eq_of_notMem hB, ← primorial_eq_prod_primesLE]

theorem smallPresieveModulus_squarefree (D B : ℕ) : Squarefree (smallPresieveModulus D B) :=
  (squarefree_primorial D).squarefree_of_dvd (smallPresieveModulus_dvd_primorial D B)

theorem smallPresieveModulus_coprime_exception (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    (smallPresieveModulus D B).Coprime B := by
  rcases hB with rfl | hB
  · exact Nat.coprime_one_right _
  · apply Nat.Coprime.prod_left
    intro p hp
    have hs := Finset.mem_erase.mp hp
    exact (Nat.coprime_primes (Nat.prime_of_mem_primesLE hs.2) hB).mpr hs.1

theorem smallPresieveModulus_mul_exception (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    smallPresieveModulus D B * B = harmonicModulus D B := by
  rcases hB with rfl | hB
  · have hnone : 1 ∉ Nat.primesLE D := by
      intro h
      exact Nat.not_prime_one (Nat.prime_of_mem_primesLE h)
    unfold smallPresieveModulus smallPresievePrimeSet harmonicModulus
    rw [Finset.erase_eq_of_notMem hnone, ← primorial_eq_prod_primesLE]
    simp
  · by_cases hdiv : B ∣ primorial D
    · have hmem : B ∈ Nat.primesLE D := Nat.mem_primesLE.mpr ⟨hB.dvd_primorial_iff.mp hdiv, hB⟩
      rw [harmonicModulus, if_pos hdiv, primorial_eq_prod_primesLE]
      exact Finset.prod_erase_mul (Nat.primesLE D) id hmem
    · have hnone : B ∉ Nat.primesLE D := by
        intro h
        exact hdiv (hB.dvd_primorial_iff.mpr (Nat.mem_primesLE.mp h).1)
      unfold smallPresieveModulus smallPresievePrimeSet
      rw [Finset.erase_eq_of_notMem hnone, ← primorial_eq_prod_primesLE, harmonicModulus, if_neg hdiv]

theorem harmonicDensity_smallPresieve_factor (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    coprimeHarmonicDensity (harmonicModulus D B) =
      coprimeHarmonicDensity (smallPresieveModulus D B) * coprimeHarmonicDensity B := by
  rw [← smallPresieveModulus_mul_exception D hB,
    harmonicDensity_mul_coprime (smallPresieveModulus_coprime_exception D hB)]

theorem harmonicDensity_smallPresieve_lower (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    coprimeHarmonicDensity (smallPresieveModulus D B) / 2 ≤
      coprimeHarmonicDensity (harmonicModulus D B) := by
  rw [harmonicDensity_smallPresieve_factor D hB]
  have hBhalf : (1 / 2 : ℝ) ≤ coprimeHarmonicDensity B := by
    rcases hB with rfl | hB
    · norm_num [coprimeHarmonicDensity]
    · exact prime_harmonicDensity_ge_half hB
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hBhalf
    (harmonicDensity_nonneg (smallPresieveModulus D B))

theorem log_smallPresieveModulus_le (D B : ℕ) :
    Real.log (smallPresieveModulus D B : ℝ) ≤ Real.log 4 * (D : ℝ) := by
  have hle : smallPresieveModulus D B ≤ primorial D :=
    Nat.le_of_dvd (primorial_pos D) (smallPresieveModulus_dvd_primorial D B)
  have hpos : (0 : ℝ) < smallPresieveModulus D B := by exact_mod_cast smallPresieveModulus_pos D B
  have hleR : (smallPresieveModulus D B : ℝ) ≤ primorial D := by exact_mod_cast hle
  exact (Real.log_le_log hpos hleR).trans (log_primorial_le D)

end Erdos4.FGKMT
