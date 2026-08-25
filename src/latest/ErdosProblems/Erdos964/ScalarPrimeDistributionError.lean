import ErdosProblems.Erdos964.ScalarPrimeErrorReindex
import ErdosProblems.Erdos964.PrimeSliceWeightedSaving

/-!
# Prime distribution errors with the scalar coefficients

The coefficient envelope, lcm fibers, and prime-divisor reindexing reduce
the actual double coefficient error to the unconditional prime-family saving.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

theorem scalar_coefficient_prime_error_le (s : BoundingSieve)
    (hs : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p)
    (R k : ℕ) (y : ℕ → ℝ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (E : ℕ → ℕ → ℝ) (hE : ∀ p q, 0 ≤ E p q)
    (B : ℝ) (hB : 0 ≤ B) (hy : ∀ u, |y u| ≤ B) (hcut : ∀ u, R ≤ u → y u = 0) :
    (∑ d ∈ scalarSieveDivisors s R, ∑ e ∈ scalarSieveDivisors s R,
      ((k ^ ω (Nat.lcm d e) : ℕ) : ℝ) *
        |scalarSelbergCoefficient s y d * scalarSelbergCoefficient s y e| *
          ∑ p ∈ P.filter (fun p => p ∣ Nat.lcm d e), E p (Nat.lcm d e / p)) ≤
      B ^ 2 * (1 + Real.log R) ^ 648 * (4 * k) *
        ∑ p ∈ P, ∑ q ∈ (Finset.Ioc 0 (R ^ 2 / p)).filter Squarefree,
          (((4 * k) ^ ω q : ℕ) : ℝ) * E p q := by
  have hfinite := scalar_coefficient_distribution_error_le s hs R k y
    (fun u => ∑ p ∈ P.filter (fun p => p ∣ u), E p (u / p)) B hB hy hcut
    (fun u => Finset.sum_nonneg (fun p _ => hE p (u / p)))
  apply hfinite.trans
  have h := mul_le_mul_of_nonneg_left
    (sum_squarefree_prime_divisor_errors_le (R ^ 2) (4 * k) P hP E hE)
    (show 0 ≤ B ^ 2 * (1 + Real.log R) ^ 648 by positivity)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at h
  simpa only [mul_assoc] using h

theorem exists_scalar_prime_distribution_logSaving (a k m : ℕ) (hm : 0 < m)
    (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ P : Finset ℕ,
        (∀ p ∈ P, p.Prime) → P ⊆ Finset.Ioc 0 L →
      ∀ F : ℕ → ℕ, (∀ p ∈ P, L ≤ F p ∧ p * F p ≤ L ^ 2) →
      ∀ (R : ℕ) (s : BoundingSieve),
        (∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p) →
        1 ≤ R → R ≤ L → (∀ p ∈ P, R ^ 2 / p ≤ modulusCutoff θ (F p)) →
      ∀ y : ℕ → ℝ, (∀ u, |y u| ≤ 7) → (∀ u, R ≤ u → y u = 0) →
      (∑ d ∈ scalarSieveDivisors s R, ∑ e ∈ scalarSieveDivisors s R,
        ((k ^ ω (Nat.lcm d e) : ℕ) : ℝ) *
          |scalarSelbergCoefficient s y d * scalarSelbergCoefficient s y e| *
            ∑ p ∈ P.filter (fun p => p ∣ Nat.lcm d e),
              maxProgressionDiscrepancy (F p) (m * (Nat.lcm d e / p))) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  obtain ⟨C, hC, L₀, hL₀, hbound⟩ :=
    exists_prime_family_weighted_logSaving (a + 648) (4 * k) m hm θ hθ hθhalf
  refine ⟨49 * 2 ^ 648 * (4 * k) * C, by positivity, L₀, hL₀, ?_⟩
  intro L hL P hP hPL F hF R s hs hRone hRL hmod y hy hcut
  have hlogone := one_le_log_natCast (hL₀.trans hL)
  have hlogpos : 0 < Real.log (L : ℝ) := by linarith
  have hlogs : 1 + Real.log (R : ℝ) ≤ 2 * Real.log (L : ℝ) := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < R by omega))
      (show (R : ℝ) ≤ L by exact_mod_cast hRL)
    linarith
  have hlogR : 0 ≤ 1 + Real.log (R : ℝ) := by linarith [Real.log_natCast_nonneg R]
  have hS (p : ℕ) (hp : p ∈ P) :
      (Finset.Ioc 0 (R ^ 2 / p)).filter Squarefree ⊆ Finset.Ioc 0 (modulusCutoff θ (F p)) := by
    intro q hq
    have hq' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
    exact Finset.mem_Ioc.mpr ⟨hq'.1, hq'.2.trans (hmod p hp)⟩
  have hBV := hbound L hL P hPL F hF
    (fun p => (Finset.Ioc 0 (R ^ 2 / p)).filter Squarefree) hS
    (fun _ _ _ hq => (Finset.mem_filter.mp hq).2)
  have hfinite := scalar_coefficient_prime_error_le s hs R k y P hP
    (fun p q => maxProgressionDiscrepancy (F p) (m * q))
    (fun p q => maxProgressionDiscrepancy_nonneg (F p) (m * q)) 7 (by norm_num) hy hcut
  norm_num only [show (7 : ℝ) ^ 2 = 49 by norm_num] at hfinite
  calc
    _ ≤ 49 * (1 + Real.log R) ^ 648 * (4 * k) *
        ∑ p ∈ P, ∑ q ∈ (Finset.Ioc 0 (R ^ 2 / p)).filter Squarefree,
          (((4 * k) ^ ω q : ℕ) : ℝ) * maxProgressionDiscrepancy (F p) (m * q) := hfinite
    _ ≤ 49 * (1 + Real.log R) ^ 648 * (4 * k) *
        (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 648)) :=
      mul_le_mul_of_nonneg_left hBV (by positivity)
    _ ≤ 49 * (2 * Real.log L) ^ 648 * (4 * k) *
        (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 648)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogR hlogs 648) (by norm_num))
          (by positivity)) (by positivity)
    _ = _ := by
      rw [mul_pow, pow_add]
      field_simp

theorem exists_scalar_prime_interval_distribution_logSaving (a k m : ℕ) (hm : 0 < m)
    (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ P : Finset ℕ,
        (∀ p ∈ P, p.Prime) → P ⊆ Finset.Ioc 0 L →
      ∀ x z : ℕ, x ≤ z → z ≤ L ^ 2 → (∀ p ∈ P, p * L ≤ x) →
      ∀ (R : ℕ) (s : BoundingSieve),
        (∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p = (3 : ℝ) / p) →
        1 ≤ R → R ≤ L → (∀ p ∈ P, R ^ 2 / p ≤ modulusCutoff θ (x / p)) →
      ∀ y : ℕ → ℝ, (∀ u, |y u| ≤ 7) → (∀ u, R ≤ u → y u = 0) →
      (∑ d ∈ scalarSieveDivisors s R, ∑ e ∈ scalarSieveDivisors s R,
        ((k ^ ω (Nat.lcm d e) : ℕ) : ℝ) *
          |scalarSelbergCoefficient s y d * scalarSelbergCoefficient s y e| *
            ∑ p ∈ P.filter (fun p => p ∣ Nat.lcm d e),
              (maxProgressionDiscrepancy (z / p) (m * (Nat.lcm d e / p)) +
                maxProgressionDiscrepancy (x / p) (m * (Nat.lcm d e / p)))) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  obtain ⟨C, hC, L₀, hL₀, hbound⟩ :=
    exists_scalar_prime_distribution_logSaving a k m hm θ hθ hθhalf
  refine ⟨2 * C, by positivity, L₀, hL₀, ?_⟩
  intro L hL P hP hPL x z hxz hz hlo R s hs hRone hRL hmod y hy hcut
  have hxF (p : ℕ) (hp : p ∈ P) : L ≤ x / p ∧ p * (x / p) ≤ L ^ 2 := by
    constructor
    · rw [Nat.le_div_iff_mul_le (hP p hp).pos, Nat.mul_comm]
      exact hlo p hp
    · exact (Nat.mul_div_le x p).trans (hxz.trans hz)
  have hzF (p : ℕ) (hp : p ∈ P) : L ≤ z / p ∧ p * (z / p) ≤ L ^ 2 :=
    ⟨(hxF p hp).1.trans (Nat.div_le_div_right hxz), (Nat.mul_div_le z p).trans hz⟩
  have hzmod (p : ℕ) (hp : p ∈ P) : R ^ 2 / p ≤ modulusCutoff θ (z / p) := by
    apply (hmod p hp).trans
    apply Nat.floor_mono
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_div_right hxz) hθ.le
  have hxerr := hbound L hL P hP hPL (fun p => x / p) hxF R s hs hRone hRL hmod y hy hcut
  have hzerr := hbound L hL P hP hPL (fun p => z / p) hzF R s hs hRone hRL hzmod y hy hcut
  simp_rw [Finset.sum_add_distrib, mul_add]
  have h := add_le_add hzerr hxerr
  simp only [← Finset.sum_add_distrib] at h
  have hright : C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a +
      C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a =
      2 * C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by ring
  rw [hright] at h
  exact h

end Erdos964
