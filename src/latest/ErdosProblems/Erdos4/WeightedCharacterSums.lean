import ErdosProblems.Erdos4.CharacterCorrelations
import ErdosProblems.Erdos4.SelbergOptimization

/-!
# Character sums against the square majorant

The complete-period bound is retained after restriction to multiples and
after expansion of the concrete square sieve weight.
-/

open scoped BigOperators

namespace Erdos4.WeightedCharacterSums

open SieveMajorant CharacterCorrelations

theorem sum_Icc_one_eq_range {A : Type*} [AddCommMonoid A] (f : ℕ → A) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  symm
  apply Finset.sum_bij (fun (n : ℕ) (_hn : n ∈ Finset.range N) => n + 1)
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hn; omega⟩
  · intro a _ha b _hb hab
    omega
  · intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n _hn
    rfl

theorem sum_multiples_Icc {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (r N : ℕ) (hr : 0 < r) :
    (∑ n ∈ Finset.Icc 1 N, if r ∣ n then f n else 0) =
      ∑ m ∈ Finset.Icc 1 (N / r), f (r * m) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun (m : ℕ) (_hm : m ∈ Finset.Icc 1 (N / r)) => r * m)
  · intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hr hm1, ?_⟩, dvd_mul_right r m⟩
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hr).mp hmN
  · intro a _ha b _hb hab
    exact Nat.eq_of_mul_eq_mul_left hr hab
  · intro n hn
    obtain ⟨hnI, hndvd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
    refine ⟨n / r, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnN⟩, Nat.mul_div_cancel' hndvd⟩
    exact Nat.div_pos (Nat.le_of_dvd hn1 hndvd) hr
  · intro m _hm
    rfl

theorem primitive_sum_multiples_le {d e : ℕ} [NeZero d] [NeZero e]
    (chi : DirichletCharacter ℂ d) (psi : DirichletCharacter ℂ e)
    (hchi : chi.IsPrimitive) (hpsi : psi.IsPrimitive) (hne : d ≠ e)
    (r N : ℕ) (hr : 0 < r) :
    ‖∑ n ∈ Finset.Icc 1 N, if r ∣ n then
      star (chi (n : ZMod d)) * psi (n : ZMod e) else 0‖ ≤ Nat.lcm d e := by
  rw [sum_multiples_Icc _ r N hr, sum_Icc_one_eq_range]
  simpa only [Nat.add_comm] using
    primitive_correlation_multiples_le chi psi hchi hpsi hne r 1 (N / r)

theorem weighted_sum_eq_divisor_pairs (D N : ℕ) (lambda : ℕ → ℝ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, (weight D lambda n : ℂ) * f n) =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ((lambda d * lambda e : ℝ) : ℂ) *
          ∑ n ∈ Finset.Icc 1 N, if Nat.lcm d e ∣ n then f n else 0 := by
  have hpoint : ∀ n, (weight D lambda n : ℂ) * f n =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        ((lambda d * lambda e : ℝ) : ℂ) * (if Nat.lcm d e ∣ n then f n else 0) := by
    intro n
    rw [weight_eq_divisor_pairs, Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _hd
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _he
    by_cases hdiv : Nat.lcm d e ∣ n <;> simp [hdiv]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _he
  rw [Finset.mul_sum]

/-- Square-majorant correlations cost only the square of the coefficient
`l1` norm times the complete-period bound. -/
theorem norm_weighted_sum_le (D N : ℕ) (lambda : ℕ → ℝ) (f : ℕ → ℂ) (L : ℝ)
    (hL : ∀ r : ℕ, 0 < r →
      ‖∑ n ∈ Finset.Icc 1 N, if r ∣ n then f n else 0‖ ≤ L) :
    ‖∑ n ∈ Finset.Icc 1 N, (weight D lambda n : ℂ) * f n‖ ≤
      L * (∑ d ∈ Finset.Icc 1 D, |lambda d|) ^ 2 := by
  rw [weighted_sum_eq_divisor_pairs]
  calc
    ‖∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      ((lambda d * lambda e : ℝ) : ℂ) *
        ∑ n ∈ Finset.Icc 1 N, if Nat.lcm d e ∣ n then f n else 0‖ ≤
        ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
          ‖((lambda d * lambda e : ℝ) : ℂ) *
            ∑ n ∈ Finset.Icc 1 N, if Nat.lcm d e ∣ n then f n else 0‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _hd => norm_sum_le _ _))
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, |lambda d| * |lambda e| * L := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hL _ (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = L * (∑ d ∈ Finset.Icc 1 D, |lambda d|) ^ 2 := by
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      ring

end Erdos4.WeightedCharacterSums
