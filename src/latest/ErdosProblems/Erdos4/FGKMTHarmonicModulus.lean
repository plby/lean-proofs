import ErdosProblems.Erdos4.FGKMTUniformHarmonic
import BoundedGaps.Maynard.MaynardSquarefreeRoughTail
import UnitFractions.ForMathlib.BasicEstimates

/-! A squarefree harmonic modulus including the possible exceptional prime. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open BoundedGaps.Maynard

def harmonicModulus (D B : ℕ) : ℕ :=
  if B ∣ primorial D then primorial D else primorial D * B

theorem harmonicModulus_pos (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime) : 0 < harmonicModulus D B := by
  unfold harmonicModulus
  split_ifs
  · exact primorial_pos D
  · apply Nat.mul_pos (primorial_pos D)
    rcases hB with rfl | hB
    · norm_num
    · exact hB.pos

theorem harmonicModulus_squarefree (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    Squarefree (harmonicModulus D B) := by
  unfold harmonicModulus
  split_ifs with hdiv
  · exact squarefree_primorial D
  · rcases hB with rfl | hB
    · exact (hdiv (one_dvd _)).elim
    · have hcop := (hB.coprime_iff_not_dvd.mpr hdiv).symm
      exact (Nat.squarefree_mul hcop).mpr ⟨squarefree_primorial D, hB.squarefree⟩

theorem primorial_dvd_harmonicModulus (D B : ℕ) : primorial D ∣ harmonicModulus D B := by
  unfold harmonicModulus
  split_ifs
  · exact dvd_rfl
  · exact dvd_mul_right _ _

theorem small_prime_dvd_harmonicModulus (D B : ℕ) {p : ℕ} (hp : p.Prime) (hpD : p ≤ D) :
    p ∣ harmonicModulus D B := by
  have hh : p ∣ primorial D := by
    rw [primorial_eq_prod_primesLE]
    exact Finset.dvd_prod_of_mem (fun p : ℕ => p) (Nat.mem_primesLE.mpr ⟨hpD, hp⟩)
  exact hh.trans (primorial_dvd_harmonicModulus D B)

theorem prime_harmonicDensity_ge_half {p : ℕ} (hp : p.Prime) :
    (1 / 2 : ℝ) ≤ coprimeHarmonicDensity p := by
  unfold coprimeHarmonicDensity
  rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]
  apply (le_div_iff₀ (by exact_mod_cast hp.pos)).mpr
  have hh : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

theorem harmonicDensity_mul_coprime {W B : ℕ} (hcop : W.Coprime B) :
    coprimeHarmonicDensity (W * B) = coprimeHarmonicDensity W * coprimeHarmonicDensity B := by
  unfold coprimeHarmonicDensity
  rw [Nat.totient_mul hcop, Nat.cast_mul, Nat.cast_mul]
  ring

theorem harmonicModulus_density_lower (D : ℕ) {B : ℕ} (hB : B = 1 ∨ B.Prime) :
    coprimeHarmonicDensity (primorial D) / 2 ≤ coprimeHarmonicDensity (harmonicModulus D B) := by
  unfold harmonicModulus
  split_ifs with hdiv
  · have hh := harmonicDensity_nonneg (primorial D)
    linarith
  · rcases hB with rfl | hB
    · exact (hdiv (one_dvd _)).elim
    · rw [harmonicDensity_mul_coprime (hB.coprime_iff_not_dvd.mpr hdiv).symm]
      have hh := mul_le_mul_of_nonneg_left (prime_harmonicDensity_ge_half hB)
        (harmonicDensity_nonneg (primorial D))
      simpa only [mul_one_div] using hh

theorem primorial_density_eq_euler_inverse (D : ℕ) :
    coprimeHarmonicDensity (primorial D) = (partial_euler_product D)⁻¹ := by
  have hset : (Finset.Icc 1 D).filter Nat.Prime = D.primesLE := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hpD⟩, hp⟩
      exact ⟨hpD, hp⟩
    · rintro ⟨hpD, hp⟩
      exact ⟨⟨hp.one_le, hpD⟩, hp⟩
  unfold coprimeHarmonicDensity partial_euler_product
  rw [totient_eq_prod_primeFactors_of_squarefree (squarefree_primorial D), primeFactors_primorial,
    primorial_eq_prod_primesLE, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib,
    hset, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primesLE hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  rw [Nat.totient_prime hprime, Nat.cast_sub hprime.one_le, Nat.cast_one, inv_inv]
  field_simp

theorem exists_harmonicModulus_density_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ D B : ℕ, 2 ≤ D → (B = 1 ∨ B.Prime) →
      c / Real.log (D : ℝ) ≤ coprimeHarmonicDensity (harmonicModulus D B) := by
  obtain ⟨C, hC, hupper⟩ := weak_mertens_third_upper_all
  refine ⟨1 / (2 * C), by positivity, ?_⟩
  intro D B hD hB
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast hD)
  have heuler : 0 < partial_euler_product D := zero_lt_one.trans_le partial_euler_trivial_lower_bound
  have hh : partial_euler_product D ≤ C * Real.log (D : ℝ) := by
    simpa only [Nat.floor_natCast, Real.norm_eq_abs, abs_of_pos heuler, abs_of_pos hlog] using
      hupper (D : ℝ) (by exact_mod_cast hD)
  have hinv := one_div_le_one_div_of_le heuler hh
  have hhalf := div_le_div_of_nonneg_right hinv (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ = (1 / (C * Real.log (D : ℝ))) / 2 := by ring
    _ ≤ (1 / partial_euler_product D) / 2 := hhalf
    _ = coprimeHarmonicDensity (primorial D) / 2 := by rw [primorial_density_eq_euler_inverse, one_div]
    _ ≤ _ := harmonicModulus_density_lower D hB

end Erdos4.FGKMT
