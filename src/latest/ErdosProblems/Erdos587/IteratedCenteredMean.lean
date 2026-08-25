import ErdosProblems.Erdos587.CenteredMean
import ErdosProblems.Erdos587.ReciprocalDivisor

/-!
# Centered quadratic means with an arbitrary fixed root margin

The fourth-root estimate suffices for low nearby frequencies, but not for
the wider terminal rectangle. Iterated small-divisor selection gives the
same centered mean whenever an integer cutoff `D` satisfies
`2*M*L <= D^(4^j)` and `q*D <= 2*M*L`.
-/

open scoped BigOperators

namespace Erdos587

open Erdos438.QuadraticWeyl

lemma twistedResiduePairCount_le_iterated_moments
    (j a q r M N D : ℕ) (hsize : 2 * M * N ≤ D ^ (4 ^ j)) :
    (twistedResiduePairCount a q r M N : ℝ) ≤
      (iteratedDivisorConstant j : ℝ) * ∑ d ∈ Finset.Icc 1 D,
        (d.divisors.card : ℝ) ^ (12 ^ j) *
          twistedDivisorResidueCount a d q r (2 * M * N) := by
  have hfirst : (twistedResiduePairCount a q r M N : ℝ) ≤
      ∑ v ∈ (Finset.Icc 1 (2 * M * N)).filter (fun v ↦ (a * v) % q = r),
        (v.divisors.card : ℝ) := by
    exact_mod_cast twistedResiduePairCount_le_sum_card_divisors a q r M N
  calc
    _ ≤ ∑ v ∈ (Finset.Icc 1 (2 * M * N)).filter (fun v ↦ (a * v) % q = r),
        (v.divisors.card : ℝ) := hfirst
    _ ≤ ∑ v ∈ (Finset.Icc 1 (2 * M * N)).filter (fun v ↦ (a * v) % q = r),
        (iteratedDivisorConstant j : ℝ) *
          ∑ d ∈ (Finset.Icc 1 D).filter (fun d ↦ d ∣ v),
            (d.divisors.card : ℝ) ^ (12 ^ j) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvI := Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1
      exact card_divisors_le_iterated_small_divisor_sum j (Nat.ne_of_gt hvI.1)
        (hvI.2.trans hsize)
    _ = _ := by rw [← Finset.mul_sum, sum_v_sum_d_dvd_twisted_eq]

lemma weighted_twistedResiduePairCount_le_iterated_moments
    (j a q M N n D : ℕ) (haq : a.Coprime q) (hq : 0 < q)
    (hsize : 2 * M * N ≤ D ^ (4 ^ j)) :
    (∑ r ∈ Finset.Icc 1 n,
        (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r)) ≤
      (iteratedDivisorConstant j : ℝ) * (1 + Real.log n) *
        (((2 * M * N : ℕ) : ℝ) *
            (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j) / d) +
          (q : ℝ) * (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j))) := by
  let c : ℝ := iteratedDivisorConstant j
  let b : ℕ := 12 ^ j
  let X := 2 * M * N
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 n,
        (c * ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ b *
          twistedDivisorResidueCount a d q r X) * ((q : ℝ) / r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (twistedResiduePairCount_le_iterated_moments j a q r M N D hsize) (by positivity)
    _ = c * ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ b *
        (∑ r ∈ Finset.Icc 1 n,
          (twistedDivisorResidueCount a d q r X : ℝ) * ((q : ℝ) / r)) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ c * ∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ b *
        (((X : ℝ) / d + q) * (1 + Real.log n)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (sum_twistedDivisorResidueCount_weight_le haq (Finset.mem_Icc.mp hd).1 hq)
        (by positivity)
    _ = c * (1 + Real.log n) *
        ((X : ℝ) * (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ b / d) +
          (q : ℝ) * (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ b)) := by
      rw [mul_assoc]
      congr 1
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring

theorem exists_weighted_iterated_residue_count_bound (j : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a q M N n D : ℕ),
      let X := 2 * M * N
      a.Coprime q → 0 < q → 3 ≤ D → n ≤ X → q * D ≤ X → X ≤ D ^ (4 ^ j) →
        (∑ r ∈ Finset.Icc 1 n,
          (twistedResiduePairCount a q r M N : ℝ) * ((q : ℝ) / r)) ≤
          K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
  obtain ⟨K₁, hK₁, O₁, hO₁, hweighted⟩ := exists_weighted_divisorPower_log_bound (12 ^ j)
  obtain ⟨K₂, hK₂, O₂, hO₂, hmean⟩ := exists_divisorPower_mean_log_bound (12 ^ j)
  let P := O₁ + O₂
  let c : ℝ := iteratedDivisorConstant j
  have hc : 0 < c := by
    change 0 < (iteratedDivisorConstant j : ℝ)
    exact_mod_cast iteratedDivisorConstant_pos j
  refine ⟨2 * c * (K₁ + K₂), by positivity, P + 1, by omega, ?_⟩
  intro a q M N n D
  dsimp only
  let X := 2 * M * N
  intro haq hq hD hnX hqD hsize
  have hDX : D ≤ X := by
    have hh : D ≤ q * D := by
      calc
        D = 1 * D := (one_mul D).symm
        _ ≤ q * D := Nat.mul_le_mul_right D hq
    exact hh.trans hqD
  have hX3 : 3 ≤ X := hD.trans hDX
  have hlogX : 1 ≤ Real.log (X : ℝ) := one_le_log_nat_of_three_le hX3
  have hlogD : 1 ≤ Real.log (D : ℝ) := one_le_log_nat_of_three_le hD
  have hlogDX : Real.log (D : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < D by omega)) (by exact_mod_cast hDX)
  have hpow (o : ℕ) (ho : o ≤ P) : Real.log (D : ℝ) ^ o ≤ Real.log (X : ℝ) ^ P :=
    (pow_le_pow_left₀ (by linarith) hlogDX o).trans (pow_le_pow_right₀ hlogX ho)
  have hW : (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j) / d) ≤
      K₁ * Real.log (X : ℝ) ^ P :=
    (hweighted D hD).trans (mul_le_mul_of_nonneg_left (hpow O₁ (by dsimp [P]; omega)) hK₁.le)
  have hU : (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j)) ≤
      K₂ * D * Real.log (X : ℝ) ^ P :=
    (hmean D hD).trans
      (mul_le_mul_of_nonneg_left (hpow O₂ (by dsimp [P]; omega)) (by positivity))
  by_cases hn : n = 0
  · subst n
    simp only [Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty]
    positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hlogn : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast hnpos)
  have hlognX : Real.log n ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast hnpos) (by exact_mod_cast hnX)
  have hH : 1 + Real.log n ≤ 2 * Real.log (X : ℝ) := by linarith
  have hXW : (X : ℝ) * (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j) / d) ≤
      K₁ * X * Real.log (X : ℝ) ^ P := by
    calc
      _ ≤ (X : ℝ) * (K₁ * Real.log (X : ℝ) ^ P) :=
        mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg X)
      _ = _ := by ring
  have hqU : (q : ℝ) * (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j)) ≤
      K₂ * X * Real.log (X : ℝ) ^ P := by
    calc
      _ ≤ (q : ℝ) * (K₂ * D * Real.log (X : ℝ) ^ P) :=
        mul_le_mul_of_nonneg_left hU (by positivity)
      _ = K₂ * ((q * D : ℕ) : ℝ) * Real.log (X : ℝ) ^ P := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hqD) hK₂.le) (by positivity)
  have hinner :
      (X : ℝ) * (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j) / d) +
        (q : ℝ) * (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j)) ≤
      (K₁ + K₂) * X * Real.log (X : ℝ) ^ P := by
    calc
      _ ≤ K₁ * X * Real.log (X : ℝ) ^ P + K₂ * X * Real.log (X : ℝ) ^ P :=
        add_le_add hXW hqU
      _ = _ := by ring
  calc
    _ ≤ c * (1 + Real.log n) *
        ((X : ℝ) * (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j) / d) +
          (q : ℝ) * (∑ d ∈ Finset.Icc 1 D, (d.divisors.card : ℝ) ^ (12 ^ j))) :=
      weighted_twistedResiduePairCount_le_iterated_moments j a q M N n D haq hq hsize
    _ ≤ c * (2 * Real.log (X : ℝ)) * ((K₁ + K₂) * X * Real.log (X : ℝ) ^ P) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hH hc.le) hinner
        (add_nonneg
          (mul_nonneg (Nat.cast_nonneg X) (Finset.sum_nonneg fun d _ =>
            div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg d)))
          (mul_nonneg (Nat.cast_nonneg q) (Finset.sum_nonneg fun d _ =>
            pow_nonneg (Nat.cast_nonneg _) _)))
        (mul_nonneg hc.le (mul_nonneg (by norm_num) (zero_le_one.trans hlogX)))
    _ = (2 * c * (K₁ + K₂)) * X * Real.log (X : ℝ) ^ (P + 1) := by
      rw [pow_succ]
      ring

theorem exists_iterated_centered_quadratic_mean_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a q M L D : ℕ),
      let X := 2 * M * L
      a.Coprime q → 0 < q → 3 ≤ D → q - 1 ≤ X → q * D ≤ X → X ≤ D ^ (4 ^ j) →
        ∀ (s : ℕ → ℤ) (l : ℕ → ℕ), (∀ m ∈ Finset.Icc 1 M, l m ≤ L) →
          (∑ m ∈ Finset.Icc 1 M,
            ‖centeredQuadraticInterval q ((a * m : ℕ) : ℤ) (s m) (l m)‖ ^ 2) ≤
              C * M * L * Real.log (X : ℝ) ^ O := by
  obtain ⟨K, hK, O, hO, hweighted⟩ := exists_weighted_iterated_residue_count_bound j
  refine ⟨10 + 16 * K, by positivity, O, hO, ?_⟩
  intro a q M L D
  dsimp only
  let X := 2 * M * L
  intro haq hq hD hqX hqD hsize s l hl
  have hnonzero := hweighted a q M L (q - 1) D haq hq hD hqX hqD hsize
  have hnonzero' := hweighted (q - a % q) q M L (q - 1) D
    (complementary_numerator_coprime hq haq) hq hD hqX hqD hsize
  have hcount := sum_rationalMajorant_mul_frequency_le a q 0 M L hq
  simp only [Nat.cast_zero, mul_zero, zero_add] at hcount
  have hXthree : 3 ≤ X := by
    apply hD.trans
    have hh : D ≤ q * D := by
      calc
        D = 1 * D := (one_mul D).symm
        _ ≤ q * D := Nat.mul_le_mul_right D hq
    exact hh.trans hqD
  have hF : 1 ≤ Real.log (X : ℝ) ^ O := one_le_pow₀ (one_le_log_nat_of_three_le hXthree)
  have hsum : (∑ m ∈ Finset.Icc 1 M, ∑ h ∈ Finset.Icc 1 L,
      rationalMajorant (a * m) q 0 h) ≤ 2 * K * (X : ℝ) * Real.log (X : ℝ) ^ O := by
    linarith
  apply (sum_norm_centeredQuadraticInterval_sq_le_majorants a q M L hq s l hl).trans
  calc
    _ ≤ 10 * (M : ℝ) * L + 4 * (2 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by norm_num))
    _ ≤ (10 * (M : ℝ) * L) * Real.log (X : ℝ) ^ O +
        4 * (2 * K * (X : ℝ) * Real.log (X : ℝ) ^ O) := by
      exact add_le_add (le_mul_of_one_le_right (by positivity) hF) le_rfl
    _ = (10 + 16 * K) * M * L * Real.log (X : ℝ) ^ O := by
      dsimp [X]
      push_cast
      ring

end Erdos587
