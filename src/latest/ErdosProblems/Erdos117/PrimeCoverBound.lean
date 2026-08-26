import ErdosProblems.Erdos117.RankOptimization
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A uniform prime-group cover estimate

The improved ternary credit is exactly what allows the leading coefficient
to be at most one half for every prime. The remaining error is bounded
uniformly in the prime in terms of the central-series length.
-/

namespace Erdos117

open scoped BigOperators

theorem nat_sq_le_two_pow {k : ℕ} (hk : 4 ≤ k) : k * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ]
    have h : (k + 1) * (k + 1) ≤ 2 * (k * k) := by nlinarith
    nlinarith

theorem prime_sq_le_two_pow_credit {p : ℕ} [Fact p.Prime] :
    p * p ≤ 2 ^ scalarCreditRate p := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  by_cases h2 : p = 2
  · subst p; norm_num [scalarCreditRate]
  by_cases h3 : p = 3
  · subst p; norm_num [scalarCreditRate]
  simpa only [scalarCreditRate, if_neg h3] using nat_sq_le_two_pow (by omega : 4 ≤ p)

theorem prime_le_scalarCreditRate (p : ℕ) : p ≤ scalarCreditRate p := by
  unfold scalarCreditRate
  split <;> omega

/-- The logarithmic price of one unit of scalar credit is at most `log(2)/2`. -/
theorem log_prime_div_credit_le {p : ℕ} [Fact p.Prime] :
    Real.log p / scalarCreditRate p ≤ Real.log 2 / 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hw : (0 : ℝ) < scalarCreditRate p := by exact_mod_cast scalarCreditRate_pos (p := p)
  have hpow : (p : ℝ) * p ≤ 2 ^ scalarCreditRate p := by
    exact_mod_cast prime_sq_le_two_pow_credit (p := p)
  have hlog := Real.log_le_log (mul_pos hp hp) hpow
  rw [Real.log_mul hp.ne' hp.ne', Real.log_pow] at hlog
  apply (div_le_iff₀ hw).mpr
  linarith

/-- The square-root error has an absolute coefficient, independent of `p`. -/
theorem log_prime_div_sqrt_credit_le {p : ℕ} [Fact p.Prime] :
    Real.log p / Real.sqrt (scalarCreditRate p) ≤ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hw : (0 : ℝ) < scalarCreditRate p := by exact_mod_cast scalarCreditRate_pos (p := p)
  have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp)
  rw [Real.log_sqrt hp.le] at hs
  have hroot : Real.sqrt p ≤ Real.sqrt (scalarCreditRate p) :=
    Real.sqrt_le_sqrt (by exact_mod_cast prime_le_scalarCreditRate p)
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hw)).mpr
  linarith

/-- A real form of the optimized rank bound, with the prime-dependent
leading coefficient replaced by the uniform sharp coefficient. -/
theorem logarithmic_rank_bound {p n L ell S : ℕ} [Fact p.Prime]
    (hrank : (S : ℝ) ≤ (n : ℝ) / scalarCreditRate p +
      (L : ℝ) * scalarDefect p / scalarCreditRate p +
      24 * ((L : ℝ) + ell + 1) *
        Real.sqrt ((n : ℝ) * (L + ell + 1) / scalarCreditRate p) +
      (L : ℝ) * L * ell) :
    (L : ℝ) * Real.log 2 + (S : ℝ) * Real.log p ≤
      Real.log 2 / 2 * n + 2 * L +
        48 * Real.sqrt n * ((L : ℝ) + ell + 1) * Real.sqrt ((L : ℝ) + ell + 1) +
        Real.log p * L * L * ell := by
  let H : ℝ := (L : ℝ) + ell + 1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg _
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlead : (n : ℝ) / scalarCreditRate p * Real.log p ≤ Real.log 2 / 2 * n := by
    have h := mul_le_mul_of_nonneg_right (log_prime_div_credit_le (p := p)) hn
    calc
      _ = (Real.log p / scalarCreditRate p) * n := by ring
      _ ≤ _ := h
  have hdefect : (L : ℝ) * scalarDefect p / scalarCreditRate p * Real.log p ≤ L := by
    have hd : scalarDefect p ≤ 2 := by unfold scalarDefect; split <;> omega
    have hd' : (scalarDefect p : ℝ) ≤ 2 := by exact_mod_cast hd
    have hratio : Real.log p / scalarCreditRate p ≤ 1 / 2 :=
      (log_prime_div_credit_le (p := p)).trans (by linarith)
    have h := mul_le_mul hratio hd' (by positivity : (0 : ℝ) ≤ scalarDefect p)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h' := mul_le_mul_of_nonneg_left h hL
    calc
      _ = (L : ℝ) * (Real.log p / scalarCreditRate p * scalarDefect p) := by ring
      _ ≤ (L : ℝ) * (1 / 2 * 2) := h'
      _ = L := by ring
  have herr : 24 * H * Real.sqrt ((n : ℝ) * H / scalarCreditRate p) * Real.log p ≤
      48 * Real.sqrt n * H * Real.sqrt H := by
    rw [Real.sqrt_div (mul_nonneg hn hH), Real.sqrt_mul hn]
    have h := mul_le_mul_of_nonneg_left (log_prime_div_sqrt_credit_le (p := p))
      (show 0 ≤ 24 * Real.sqrt n * H * Real.sqrt H by positivity)
    calc
      _ = (24 * Real.sqrt n * H * Real.sqrt H) *
          (Real.log p / Real.sqrt (scalarCreditRate p)) := by ring
      _ ≤ (24 * Real.sqrt n * H * Real.sqrt H) * 2 := h
      _ = _ := by ring
  have hmain := mul_le_mul_of_nonneg_right hrank hlp
  have hlength := mul_le_mul_of_nonneg_left hl2 hL
  change 24 * H * Real.sqrt ((n : ℝ) * H / scalarCreditRate p) * Real.log p ≤ _ at herr
  change (L : ℝ) * Real.log 2 + (S : ℝ) * Real.log p ≤
    Real.log 2 / 2 * n + 2 * L + 48 * Real.sqrt n * H * Real.sqrt H +
      Real.log p * L * L * ell
  change (S : ℝ) * Real.log p ≤ ((n : ℝ) / scalarCreditRate p +
    (L : ℝ) * scalarDefect p / scalarCreditRate p +
      24 * H * Real.sqrt ((n : ℝ) * H / scalarCreditRate p) + (L : ℝ) * L * ell) *
        Real.log p at hmain
  nlinarith only [hmain, hlength, hlead, hdefect, herr]

namespace CentralBranch

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {D : CentralChain G p} (B : CentralBranch D)

/-- The logarithm of the branch cover cost, valid for every actual branch. -/
theorem log_cover_cost_le
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n) :
    Real.log (2 ^ B.length * p ^ (∑ k, B.halfRank k) : ℕ) ≤
      Real.log 2 / 2 * n + 2 * B.length +
        48 * Real.sqrt n * ((B.length : ℝ) + Nat.clog p ((2 * n) ^ 2) + 1) *
          Real.sqrt ((B.length : ℝ) + Nat.clog p ((2 * n) ^ 2) + 1) +
        Real.log p * B.length * B.length * Nat.clog p ((2 * n) ^ 2) := by
  have h := logarithmic_rank_bound (p := p) (S := ∑ k, B.halfRank k)
    (by simpa only [Nat.cast_sum] using B.rank_sum_optimized hG hn)
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (pow_ne_zero _ (show (2 : ℝ) ≠ 0 by norm_num)) (pow_ne_zero _ hp),
    Real.log_pow, Real.log_pow]
  exact h

end CentralBranch

/-- Every finite class-two `p`-group has an actual abelian subgroup cover
with the uniform bound. Its central-series length is recorded by the exact
identity `|G'| = p^L`. -/
theorem exists_class_two_prime_cover {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p G)
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ L k : ℕ, Nat.card (commutator G) = p ^ L ∧ HasAbelianCover G k ∧
      Real.log k ≤ Real.log 2 / 2 * n + 2 * L +
        48 * Real.sqrt n * ((L : ℝ) + Nat.clog p ((2 * n) ^ 2) + 1) *
          Real.sqrt ((L : ℝ) + Nat.clog p ((2 * n) ^ 2) + 1) +
        Real.log p * L * L * Nat.clog p ((2 * n) ^ 2) := by
  obtain ⟨D, B, hD, hcard, hcover⟩ := exists_indexed_branch_cover hP hG
  exact ⟨B.length, _, hcard, hcover, B.log_cover_cost_le hG hn⟩

end Erdos117
