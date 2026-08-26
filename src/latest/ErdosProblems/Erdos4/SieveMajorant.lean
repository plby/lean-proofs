import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Finite square sieve majorants

The prime-majorization and exact divisor-pair expansion are independent of
how the coefficients are chosen. Their optimization is a separate step.
-/

open scoped BigOperators

namespace Erdos4.SieveMajorant

noncomputable def amplitude (D : ℕ) (lambda : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ n then lambda d else 0

noncomputable def weight (D : ℕ) (lambda : ℕ → ℝ) (n : ℕ) : ℝ :=
  amplitude D lambda n ^ 2

theorem weight_nonneg (D : ℕ) (lambda : ℕ → ℝ) (n : ℕ) :
    0 ≤ weight D lambda n := sq_nonneg _

theorem amplitude_prime {D p : ℕ} (hD : 1 ≤ D) (hp : p.Prime) (hDp : D < p)
    (lambda : ℕ → ℝ) : amplitude D lambda p = lambda 1 := by
  have hterm : ∀ d ∈ Finset.Icc 1 D,
      (if d ∣ p then lambda d else 0) = if d = 1 then lambda 1 else 0 := by
    intro d hd
    by_cases hd1 : d = 1
    · simp [hd1]
    · have hnot : ¬ d ∣ p := by
        intro hdvd
        rcases (Nat.dvd_prime hp).mp hdvd with hd' | hd'
        · exact hd1 hd'
        · have hle := (Finset.mem_Icc.mp hd).2
          omega
      simp [hnot, hd1]
  unfold amplitude
  rw [Finset.sum_congr rfl hterm]
  simp [hD]

theorem weight_prime {D p : ℕ} (hD : 1 ≤ D) (hp : p.Prime) (hDp : D < p)
    (lambda : ℕ → ℝ) (hlambda : lambda 1 = 1) : weight D lambda p = 1 := by
  rw [weight, amplitude_prime hD hp hDp, hlambda, one_pow]

theorem card_multiples_Icc (r N : ℕ) (hr : 0 < r) :
    ((Finset.Icc 1 N).filter (fun n => r ∣ n)).card = N / r := by
  have heq : (Finset.Icc 1 N).filter (fun n => r ∣ n) =
      (Finset.Icc 1 (N / r)).image (fun m => r * m) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnI, m, rfl⟩ := Finset.mem_filter.mp hn
      have hn1 := (Finset.mem_Icc.mp hnI).1
      have hnN := (Finset.mem_Icc.mp hnI).2
      refine Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
      · by_contra hm
        have : m = 0 := by omega
        simp [this] at hn1
      · exact (Nat.le_div_iff_mul_le hr).mpr (by simpa only [Nat.mul_comm] using hnN)
    · intro hn
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right r m⟩
      · exact Nat.mul_pos hr hm1
      · simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hr).mp hmN
  rw [heq, Finset.card_image_of_injective _ (fun a b hab => Nat.eq_of_mul_eq_mul_left hr hab)]
  simp

theorem sum_dvd_indicator (r N : ℕ) (hr : 0 < r) :
    (∑ n ∈ Finset.Icc 1 N, if r ∣ n then (1 : ℝ) else 0) = ((N / r : ℕ) : ℝ) := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_multiples_Icc r N hr]

theorem weight_eq_divisor_pairs (D : ℕ) (lambda : ℕ → ℝ) (n : ℕ) :
    weight D lambda n = ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      (lambda d * lambda e) * (if Nat.lcm d e ∣ n then 1 else 0) := by
  unfold weight amplitude
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd, he, Nat.lcm_dvd_iff]

/-- Exact finite counting formula; no asymptotic or progression assumption
is hidden in this identity. -/
theorem sum_weight_eq (D N : ℕ) (lambda : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, weight D lambda n) =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        (lambda d * lambda e) * ((N / Nat.lcm d e : ℕ) : ℝ) := by
  simp_rw [weight_eq_divisor_pairs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.mul_sum]
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hepos : 0 < e := (Finset.mem_Icc.mp he).1
  rw [sum_dvd_indicator _ _ (Nat.lcm_pos hdpos hepos)]

theorem abs_cast_div_sub_real_div_le_one (N r : ℕ) (hr : 0 < r) :
    |((N / r : ℕ) : ℝ) - (N : ℝ) / (r : ℝ)| ≤ 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hq : ((N / r : ℕ) : ℝ) * (r : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N r
  have hrem : ((N % r : ℕ) : ℝ) < r := by exact_mod_cast Nat.mod_lt N hr
  have hdecomp : ((N % r : ℕ) : ℝ) + (r : ℝ) * ((N / r : ℕ) : ℝ) = N := by
    exact_mod_cast Nat.mod_add_div N r
  have hlo : ((N / r : ℕ) : ℝ) ≤ (N : ℝ) / (r : ℝ) := (le_div_iff₀ hrR).mpr hq
  have hhi : (N : ℝ) / (r : ℝ) < ((N / r : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hrR).mpr
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

noncomputable def mainTerm (D : ℕ) (lambda : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
    lambda d * lambda e / (Nat.lcm d e : ℝ)

/-- Uniform endpoint error for the square majorant, before optimization. -/
theorem sum_weight_le (D N : ℕ) (lambda : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N, weight D lambda n) ≤
      (N : ℝ) * mainTerm D lambda + (∑ d ∈ Finset.Icc 1 D, |lambda d|) ^ 2 := by
  have hterm : ∀ d ∈ Finset.Icc 1 D, ∀ e ∈ Finset.Icc 1 D,
      lambda d * lambda e * ((N / Nat.lcm d e : ℕ) : ℝ) ≤
        (N : ℝ) * (lambda d * lambda e / (Nat.lcm d e : ℝ)) + |lambda d| * |lambda e| := by
    intro d hd e he
    have hpos := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
    have herr := abs_cast_div_sub_real_div_le_one N (Nat.lcm d e) hpos
    have hmul := mul_le_mul_of_nonneg_left herr (abs_nonneg (lambda d * lambda e))
    have habs := le_abs_self ((lambda d * lambda e) *
      (((N / Nat.lcm d e : ℕ) : ℝ) - (N : ℝ) / (Nat.lcm d e : ℝ)))
    simp only [abs_mul, mul_one] at hmul
    simp only [abs_mul] at habs
    have heq : (lambda d * lambda e) *
        (((N / Nat.lcm d e : ℕ) : ℝ) - (N : ℝ) / (Nat.lcm d e : ℝ)) =
        lambda d * lambda e * ((N / Nat.lcm d e : ℕ) : ℝ) -
          (N : ℝ) * (lambda d * lambda e / (Nat.lcm d e : ℝ)) := by ring
    rw [heq] at habs
    linarith
  rw [sum_weight_eq]
  calc
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      lambda d * lambda e * ((N / Nat.lcm d e : ℕ) : ℝ)) ≤
        ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
          ((N : ℝ) * (lambda d * lambda e / (Nat.lcm d e : ℝ)) + |lambda d| * |lambda e|) :=
      Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hterm d hd e he))
    _ = (N : ℝ) * mainTerm D lambda + (∑ d ∈ Finset.Icc 1 D, |lambda d|) ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      rw [mainTerm, Finset.mul_sum]
      simp_rw [Finset.mul_sum]
      congr 1
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

end Erdos4.SieveMajorant
