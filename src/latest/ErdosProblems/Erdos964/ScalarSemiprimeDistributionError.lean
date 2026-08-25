import ErdosProblems.Erdos964.ScalarLcmFibers
import ErdosProblems.Erdos964.SemiprimeCoprimeCentering

/-!
# Semiprime distribution errors with the scalar coefficients

The lcm-fiber bound and logarithmic coefficient envelope reduce the
double sieve error to the proved weighted semiprime distribution theorem.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

def scalarSieveDivisors (s : BoundingSieve) (R : ℕ) : Finset ℕ :=
  s.prodPrimes.divisors.filter (fun d => d < R)

theorem scalarSieveDivisors_lcm_mem (s : BoundingSieve) (R d e : ℕ)
    (hd : d ∈ scalarSieveDivisors s R) (he : e ∈ scalarSieveDivisors s R) :
    Nat.lcm d e ∈ (Finset.Ioc 0 (R ^ 2)).filter Squarefree := by
  obtain ⟨hdP, hdR⟩ := Finset.mem_filter.mp hd
  obtain ⟨heP, heR⟩ := Finset.mem_filter.mp he
  have hdpos := Nat.pos_of_mem_divisors hdP
  have hepos := Nat.pos_of_mem_divisors heP
  have hlcmP := Nat.lcm_dvd (Nat.dvd_of_mem_divisors hdP) (Nat.dvd_of_mem_divisors heP)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero (Nat.lcm_ne_zero hdpos.ne' hepos.ne'), ?_⟩,
    s.prodPrimes_squarefree.squarefree_of_dvd hlcmP⟩
  apply (Nat.lcm_le_mul hdpos hepos).trans
  simpa only [pow_two] using (Nat.mul_le_mul hdR.le heR.le)

theorem scalar_coefficient_distribution_error_le (s : BoundingSieve)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (R k : ℕ) (y E : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hy : ∀ u, |y u| ≤ B) (hcut : ∀ u, R ≤ u → y u = 0) (hE : ∀ u, 0 ≤ E u) :
    (∑ d ∈ scalarSieveDivisors s R, ∑ e ∈ scalarSieveDivisors s R,
      ((k ^ ω (Nat.lcm d e) : ℕ) : ℝ) *
        |scalarSelbergCoefficient s y d * scalarSelbergCoefficient s y e| * E (Nat.lcm d e)) ≤
      B ^ 2 * (1 + Real.log R) ^ 648 *
        ∑ u ∈ (Finset.Ioc 0 (R ^ 2)).filter Squarefree, (((4 * k) ^ ω u : ℕ) : ℝ) * E u := by
  have h := sum_scalar_lcm_coefficients_le (scalarSieveDivisors s R)
    ((Finset.Ioc 0 (R ^ 2)).filter Squarefree) k E (scalarSelbergCoefficient s y)
    (fun d hd e he => scalarSieveDivisors_lcm_mem s R d e hd he)
    (fun _ hu => (Finset.mem_filter.mp hu).2) (fun u _ => hE u)
    (B * (1 + Real.log R) ^ 324) (by positivity)
    (fun d _ => abs_scalarSelbergCoefficient_le_log s hs R y B hB hy hcut d)
  have hscale : (B * (1 + Real.log R) ^ 324) ^ 2 = B ^ 2 * (1 + Real.log R) ^ 648 := by
    rw [mul_pow, ← pow_mul]
  rwa [hscale] at h

theorem exists_scalar_semiprime_distribution_logSaving (a k m : ℕ) (hm : 0 < m)
    (η θ : ℝ) (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
        (∀ p ∈ P, Real.rpow (L : ℝ) η < p) →
      ∀ (R : ℕ) (s : BoundingSieve),
        (∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p) →
        1 ≤ R → R ^ 2 ≤ modulusCutoff θ L →
      ∀ y : ℕ → ℝ, (∀ u, |y u| ≤ 7) → (∀ u, R ≤ u → y u = 0) →
      (∑ d ∈ scalarSieveDivisors s R, ∑ e ∈ scalarSieveDivisors s R,
        ((k ^ ω (Nat.lcm d e) : ℕ) : ℝ) *
          |scalarSelbergCoefficient s y d * scalarSelbergCoefficient s y e| *
            semiprimeScaleCoprimeMaxDiscrepancy P L (m * Nat.lcm d e)) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  obtain ⟨C, hC, L₀, hL₀, hbound⟩ :=
    exists_semiprimesAtScale_coprime_weighted_multiples_logSaving (a + 648) (4 * k) m hm
      η θ hη hθ hθ1
  refine ⟨49 * 2 ^ 648 * C, by positivity, L₀, hL₀, ?_⟩
  intro L hL P hP hPL hPlower R s hs hRone hR y hy hcut
  have hL16 : 16 ≤ L := hL₀.trans hL
  have hlogone := one_le_log_natCast (show 4 ≤ L by omega)
  have hlogpos : 0 < Real.log (L : ℝ) := by linarith
  have hmodcut : modulusCutoff θ L ≤ L := by
    have hreal : (modulusCutoff θ L : ℝ) ≤ L :=
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg L) θ)).trans
        (Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ L by omega)) hθ1.le)
    exact_mod_cast hreal
  have hRL : R ≤ L := by have hR2L := hR.trans hmodcut; nlinarith
  have hlogs : 1 + Real.log (R : ℝ) ≤ 2 * Real.log (L : ℝ) := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < R by omega))
      (show (R : ℝ) ≤ L by exact_mod_cast hRL)
    linarith
  have hlogR : 0 ≤ 1 + Real.log (R : ℝ) := by linarith [Real.log_natCast_nonneg R]
  have hT : (Finset.Ioc 0 (R ^ 2)).filter Squarefree ⊆ Finset.Ioc 0 (modulusCutoff θ L) := by
    intro u hu
    have hu' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hu).1
    exact Finset.mem_Ioc.mpr ⟨hu'.1, hu'.2.trans hR⟩
  have hBV := hbound L hL P hP hPL hPlower ((Finset.Ioc 0 (R ^ 2)).filter Squarefree)
    hT (fun _ hu => (Finset.mem_filter.mp hu).2)
  have hfinite := scalar_coefficient_distribution_error_le s hs R k y
    (fun u => semiprimeScaleCoprimeMaxDiscrepancy P L (m * u)) 7 (by norm_num) hy hcut
    (fun u => semiprimeScaleCoprimeMaxDiscrepancy_nonneg P L (m * u))
  norm_num only [show (7 : ℝ) ^ 2 = 49 by norm_num] at hfinite
  calc
    _ ≤ 49 * (1 + Real.log R) ^ 648 *
        ∑ u ∈ (Finset.Ioc 0 (R ^ 2)).filter Squarefree,
          (((4 * k) ^ ω u : ℕ) : ℝ) * semiprimeScaleCoprimeMaxDiscrepancy P L (m * u) := hfinite
    _ ≤ 49 * (1 + Real.log R) ^ 648 *
        (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 648)) :=
      mul_le_mul_of_nonneg_left hBV (by positivity)
    _ ≤ 49 * (2 * Real.log L) ^ 648 *
        (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 648)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogR hlogs 648) (by norm_num))
        (by positivity)
    _ = _ := by
      rw [mul_pow, pow_add]
      field_simp

end Erdos964
