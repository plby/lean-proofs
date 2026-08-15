import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.RCLike.Basic

open scoped ArithmeticFunction.sigma

namespace Erdos250Scratch

noncomputable section

def sigmaTerm (n : ℕ) : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) / (2 : ℝ) ^ n

def lambertTerm (n : ℕ+) : ℝ := (n : ℝ) / ((2 : ℝ) ^ (n : ℕ) - 1)

lemma raw_eq_lambert (n : ℕ+) :
    (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ (n : ℕ) /
        (1 - (1 / 2 : ℝ) ^ (n : ℕ)) = lambertTerm n := by
  rw [pow_one, one_div_pow]
  simp only [lambertTerm]
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  have hpow : (2 : ℝ) ^ (n : ℕ) ≠ 1 :=
    (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) hn).ne'
  field_simp

lemma raw_sigma_eq_sigmaTerm (n : ℕ+) :
    (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n : ℕ) =
      sigmaTerm n := by
  simp [sigmaTerm, div_eq_mul_inv]

lemma sigmaTerm_nonneg (n : ℕ) : 0 ≤ sigmaTerm n := by
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

lemma sigmaTerm_summable : Summable sigmaTerm := by
  have hpoly : Summable (fun n : ℕ => (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n) := by
    simpa [Real.norm_of_nonneg] using
      (summable_norm_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (r := (1 / 2 : ℝ)) (by norm_num))
  refine hpoly.of_nonneg_of_le sigmaTerm_nonneg (fun n => ?_)
  rw [sigmaTerm, div_eq_mul_inv, ← inv_pow]
  have hs : (ArithmeticFunction.sigma 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
  norm_num at hs ⊢
  exact hs

lemma lambertTerm_summable : Summable lambertTerm := by
  have hraw : Summable (fun n : ℕ =>
      (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n / (1 - (1 / 2 : ℝ) ^ n)) :=
    summable_norm_pow_mul_geometric_div_one_sub 1 (by norm_num)
  have hsub : Summable (fun n : ℕ+ =>
      (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ (n : ℕ) /
        (1 - (1 / 2 : ℝ) ^ (n : ℕ))) := hraw.subtype _
  exact hsub.congr raw_eq_lambert

lemma tsum_lambert_eq_tsum_sigma_pnat :
    (∑' n : ℕ+, lambertTerm n) =
      ∑' n : ℕ+, sigmaTerm n := by
  calc
    (∑' n : ℕ+, lambertTerm n) =
        ∑' n : ℕ+, (n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ (n : ℕ) /
          (1 - (1 / 2 : ℝ) ^ (n : ℕ)) :=
      tsum_congr fun n => (raw_eq_lambert n).symm
    _ = ∑' n : ℕ+, (ArithmeticFunction.sigma 1 (n : ℕ) : ℝ) *
          (1 / 2 : ℝ) ^ (n : ℕ) :=
      tsum_pow_div_one_sub_eq_tsum_sigma (𝕜 := ℝ) (r := (1 / 2 : ℝ))
        (by norm_num) 1
    _ = ∑' n : ℕ+, sigmaTerm n :=
      tsum_congr raw_sigma_eq_sigmaTerm

lemma tsum_sigma_pnat_eq_tsum_nat :
    (∑' n : ℕ+, sigmaTerm n) = ∑' n : ℕ, sigmaTerm n := by
  have h := tsum_zero_pnat_eq_tsum_nat sigmaTerm_summable
  simpa [sigmaTerm] using h

theorem tsum_lambert_eq_tsum_sigma :
    (∑' n : ℕ+, lambertTerm n) = ∑' n : ℕ, sigmaTerm n :=
  tsum_lambert_eq_tsum_sigma_pnat.trans tsum_sigma_pnat_eq_tsum_nat

theorem hasSum_sigma_to_lambert {x : ℝ} (hx : HasSum sigmaTerm x) :
    HasSum lambertTerm x := by
  rw [← hx.tsum_eq, ← tsum_lambert_eq_tsum_sigma]
  exact lambertTerm_summable.hasSum

theorem hasSum_sigma_iff_lambert {x : ℝ} :
    HasSum sigmaTerm x ↔ HasSum lambertTerm x := by
  constructor
  · exact hasSum_sigma_to_lambert
  · intro hx
    rw [← hx.tsum_eq, tsum_lambert_eq_tsum_sigma]
    exact sigmaTerm_summable.hasSum

/-- Directly usable with the function in the formal-conjectures statement. -/
theorem hasSum_erdos250_to_lambert {x : ℝ}
    (hx : HasSum (fun n : ℕ =>
      (ArithmeticFunction.sigma 1 n : ℝ) / (2 : ℝ) ^ n) x) :
    HasSum (fun n : ℕ+ =>
      (n : ℝ) / ((2 : ℝ) ^ (n : ℕ) - 1)) x := by
  change HasSum sigmaTerm x at hx
  change HasSum lambertTerm x
  exact hasSum_sigma_to_lambert hx

theorem hasSum_erdos250_iff_lambert {x : ℝ} :
    HasSum (fun n : ℕ =>
      (ArithmeticFunction.sigma 1 n : ℝ) / (2 : ℝ) ^ n) x ↔
    HasSum (fun n : ℕ+ =>
      (n : ℝ) / ((2 : ℝ) ^ (n : ℕ) - 1)) x := by
  change HasSum sigmaTerm x ↔ HasSum lambertTerm x
  exact hasSum_sigma_iff_lambert

/-! A denominator-sensitive irrationality criterion for integer linear forms. -/

theorem irrational_of_arbitrarily_small_integer_linear_forms (x : ℝ)
    (hsmall : ∀ d : ℕ, 0 < d → ∃ a b : ℤ,
      0 < |(a : ℝ) * x + (b : ℝ)| ∧
        |(a : ℝ) * x + (b : ℝ)| < 1 / (d : ℝ)) :
    Irrational x := by
  by_contra hx
  obtain ⟨r : ℚ, hr⟩ := exists_rat_of_not_irrational hx
  obtain ⟨a, b, hpos, hlt⟩ := hsmall r.den r.den_pos
  let z : ℤ := a * r.num + b * (r.den : ℤ)
  have hform : (a : ℝ) * x + (b : ℝ) = (z : ℝ) / (r.den : ℝ) := by
    rw [hr, Rat.cast_def]
    simp only [z, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    field_simp [r.den_nz]
  have hz : z ≠ 0 := by
    intro hz
    rw [hform, hz] at hpos
    norm_num at hpos
  have hzabs : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz
  have hdpos : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hlower : 1 / (r.den : ℝ) ≤ |(a : ℝ) * x + (b : ℝ)| := by
    rw [hform, abs_div, abs_of_pos hdpos]
    exact (div_le_div_iff_of_pos_right hdpos).2 hzabs
  exact (not_lt_of_ge hlower) hlt

theorem irrational_of_integer_linear_forms_tendsto_zero (x : ℝ)
    (a b : ℕ → ℤ)
    (hne : ∀ᶠ n in Filter.atTop, (a n : ℝ) * x + (b n : ℝ) ≠ 0)
    (hlim : Filter.Tendsto (fun n => (a n : ℝ) * x + (b n : ℝ))
      Filter.atTop (nhds 0)) :
    Irrational x := by
  apply irrational_of_arbitrarily_small_integer_linear_forms x
  intro d hd
  have hdreal : (0 : ℝ) < 1 / (d : ℝ) := by positivity
  have hevent : ∀ᶠ n in Filter.atTop,
      |(a n : ℝ) * x + (b n : ℝ)| < 1 / (d : ℝ) := by
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨N, hN⟩ := hlim (1 / (d : ℝ)) hdreal
    exact Filter.eventually_atTop.2 ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hne.and hevent)
  have hN' := hN N le_rfl
  exact ⟨a N, b N, abs_pos.2 hN'.1, hN'.2⟩

end

end Erdos250Scratch
