/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# A prime at the `m / log(m)^2` scale

This file contains the elementary parameter-selection lemma used in the proof
of Erdős Problem 920.  Bertrand's postulate supplies a prime just above the
floor of `m / (4 * C * log(m)^2)`.  Since every fixed power of the logarithm
is little-oh of the identity, this floor is eventually at least half of the
real number being floored.  The prime therefore has the required lower bound,
while its Bertrand upper bound and monotonicity of `log` give the required
budget inequality.
-/

namespace Erdos920.PrimeScale

open Filter Asymptotics

private lemma eventually_log_sq_linear (C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      8 * C * Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) := by
  have heps : 0 < (8 * C)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) hC)
  have hreal := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound heps
  have hnat := tendsto_natCast_atTop_atTop.eventually hreal
  filter_upwards [hnat] with m hm
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id_eq,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)] at hm
  calc
    8 * C * Real.log (m : ℝ) ^ 2
        ≤ 8 * C * ((8 * C)⁻¹ * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) hC.le)
    _ = (m : ℝ) := by
      field_simp

private lemma eventually_log_large (C : ℝ) (_hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      max 1 (1 / (2 * C)) ≤ Real.log (m : ℝ) := by
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (max 1 (1 / (2 * C))))

/--
For every positive real constant `C`, all sufficiently large natural numbers
`m` have a prime `q` of order `m / log(m)^2` whose `C * q * log(q)^2` cost is
at most `m`.

The explicit factor `8` is inessential; it leaves room both for flooring and
for the factor `2` in Bertrand's postulate.  The extra conclusions `2 ≤ q`
and `q ≤ m` are convenient in applications.
-/
theorem eventually_exists_prime_scale (C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, ∃ q : ℕ,
      q.Prime ∧
      2 ≤ q ∧
      q ≤ m ∧
      (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) ∧
      C * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) := by
  filter_upwards [eventually_log_sq_linear C hC, eventually_log_large C hC]
    with m hlinear hlogLarge
  have hlogm : 0 < Real.log (m : ℝ) :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hlogLarge)
  have hden4 : 0 < 4 * C * Real.log (m : ℝ) ^ 2 := by positivity
  have hden2 : 0 < 2 * C * Real.log (m : ℝ) ^ 2 := by positivity
  have hscale :
      2 ≤ (m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2) := by
    rw [le_div_iff₀ hden4]
    nlinarith
  let r : ℕ := ⌊(m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)⌋₊
  have hfloor :
      (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤ (r : ℝ) := by
    have hsub := Nat.sub_one_lt_floor
      ((m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2))
    change (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) ≤
      (⌊(m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)⌋₊ : ℝ)
    have hhalf :
        (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) =
          ((m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)) / 2 := by ring
    rw [hhalf]
    linarith
  have hr0 : r ≠ 0 := by
    intro hr
    have hone :
        (1 : ℝ) ≤ (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) := by
      have hhalf :
          (m : ℝ) / (8 * C * Real.log (m : ℝ) ^ 2) =
            ((m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)) / 2 := by ring
      rw [hhalf]
      linarith
    have : (1 : ℝ) ≤ (r : ℝ) := hone.trans hfloor
    norm_num [hr] at this
  obtain ⟨q, hqprime, hrq, hq2r⟩ := Nat.bertrand r hr0
  have hq2 : 2 ≤ q := hqprime.two_le
  have hfloorUpper :
      (r : ℝ) ≤ (m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2) := by
    exact Nat.floor_le (by positivity)
  have hqUpper :
      (q : ℝ) ≤ (m : ℝ) / (2 * C * Real.log (m : ℝ) ^ 2) := by
    have hq2r' : (q : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast hq2r
    calc
      (q : ℝ) ≤ 2 * (r : ℝ) := hq2r'
      _ ≤ 2 * ((m : ℝ) / (4 * C * Real.log (m : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hfloorUpper (by norm_num)
      _ = (m : ℝ) / (2 * C * Real.log (m : ℝ) ^ 2) := by ring
  have hdenOne : 1 ≤ 2 * C * Real.log (m : ℝ) ^ 2 := by
    have hlogC : 1 / (2 * C) ≤ Real.log (m : ℝ) :=
      (le_max_right _ _).trans hlogLarge
    have honeC : 1 ≤ 2 * C * Real.log (m : ℝ) := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hC)] at hlogC
      nlinarith
    calc
      1 ≤ 2 * C * Real.log (m : ℝ) := honeC
      _ ≤ (2 * C * Real.log (m : ℝ)) * Real.log (m : ℝ) := by
        exact le_mul_of_one_le_right (by positivity)
          ((le_max_left _ _).trans hlogLarge)
      _ = 2 * C * Real.log (m : ℝ) ^ 2 := by ring
  have hqlem : (q : ℝ) ≤ (m : ℝ) := by
    exact hqUpper.trans (div_le_self (Nat.cast_nonneg m) hdenOne)
  have hqm : q ≤ m := by exact_mod_cast hqlem
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ q from hq2.trans' (by omega)))
  have hlogqm : Real.log (q : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by exact_mod_cast hqprime.pos) hqlem
  have hlogsq : Real.log (q : ℝ) ^ 2 ≤ Real.log (m : ℝ) ^ 2 := by
    nlinarith
  have hproduct :
      (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤
        ((m : ℝ) / (2 * C * Real.log (m : ℝ) ^ 2)) *
          Real.log (m : ℝ) ^ 2 := by
    exact mul_le_mul hqUpper hlogsq (sq_nonneg _) (by positivity)
  refine ⟨q, hqprime, hq2, hqm, ?_, ?_⟩
  · exact hfloor.trans (by exact_mod_cast hrq.le)
  · calc
      C * (q : ℝ) * Real.log (q : ℝ) ^ 2
          = C * ((q : ℝ) * Real.log (q : ℝ) ^ 2) := by ring
      _ ≤ C * (((m : ℝ) / (2 * C * Real.log (m : ℝ) ^ 2)) *
          Real.log (m : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hproduct hC.le
      _ = (m : ℝ) / 2 := by field_simp
      _ ≤ (m : ℝ) := div_le_self (Nat.cast_nonneg m) (by norm_num)

/-- Natural-constant version of `eventually_exists_prime_scale`. -/
theorem eventually_exists_prime_scale_nat (C : ℕ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, ∃ q : ℕ,
      q.Prime ∧
      2 ≤ q ∧
      q ≤ m ∧
      (m : ℝ) / (8 * (C : ℝ) * Real.log (m : ℝ) ^ 2) ≤ (q : ℝ) ∧
      (C : ℝ) * (q : ℝ) * Real.log (q : ℝ) ^ 2 ≤ (m : ℝ) := by
  exact eventually_exists_prime_scale (C : ℝ) (by exact_mod_cast hC)

end Erdos920.PrimeScale
