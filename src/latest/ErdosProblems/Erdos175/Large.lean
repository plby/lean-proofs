/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
# Assembly of the large-index argument for Erdős Problem 175

This file contains the bookkeeping common to any explicit cutoff and any
positive Section 7 lower-bound constant.  The analytic estimates themselves
belong in their source-specific modules; the theorem `large_case_of_bounds`
records exactly how a Section 7 lower bound, a Theorem 9 upper bound, and a
numerical incompatibility yield a prime-square divisor.
-/

import ErdosProblems.Erdos175.Detector
import ErdosProblems.Erdos175.Sawtooth
import ErdosProblems.Erdos175.ExplicitChebyshev
import ErdosProblems.Erdos175.NumericCutoff
import ErdosProblems.Erdos175.Vaughan

namespace Erdos175.Large

open Nat Finset
open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- The real sawtooth and the division-free detector sawtooth agree on a
natural quotient with positive denominator, including the integral endpoint
where both use the value `0`. -/
lemma psi_natCast_div_eq_sawtoothQuot (a d : ℕ) (hd : 0 < d) :
    Sawtooth.psi ((a : ℝ) / (d : ℝ)) = Detector.sawtoothQuot a d := by
  by_cases hdiv : d ∣ a
  · have hmod : a % d = 0 := Nat.mod_eq_zero_of_dvd hdiv
    have hfract : Int.fract ((a : ℝ) / (d : ℝ)) = 0 := by
      rw [Int.fract_div_natCast_eq_div_natCast_mod, hmod]
      norm_num
    have heq : (a : ℝ) / (d : ℝ) = (⌊(a : ℝ) / (d : ℝ)⌋ : ℝ) := by
      simpa only [Int.fract, sub_eq_zero] using hfract
    rw [Sawtooth.psi, if_pos heq, Detector.sawtoothQuot, if_pos hdiv]
  · have hmod : a % d ≠ 0 := fun h => hdiv (Nat.dvd_of_mod_eq_zero h)
    have hfract : Int.fract ((a : ℝ) / (d : ℝ)) ≠ 0 := by
      rw [Int.fract_div_natCast_eq_div_natCast_mod]
      exact div_ne_zero (by exact_mod_cast hmod) (by exact_mod_cast hd.ne')
    have hne : (a : ℝ) / (d : ℝ) ≠ (⌊(a : ℝ) / (d : ℝ)⌋ : ℝ) := by
      simpa only [Int.fract, sub_ne_zero] using hfract
    rw [Sawtooth.psi, if_neg hne, Detector.sawtoothQuot, if_neg hdiv,
      Int.fract_div_natCast_eq_div_natCast_mod]

/-- Sum-level form of `psi_natCast_div_eq_sawtoothQuot`, with factors ordered
as expected by the generic weighted Fourier lemmas. -/
lemma sum_psi_eq_sum_sawtoothQuot (a n : ℕ) :
    (∑ d ∈ Detector.squareRootInterval n,
        ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((a : ℝ) / (d : ℝ))) =
      ∑ d ∈ Detector.squareRootInterval n,
        Detector.sawtoothQuot a d * ArithmeticFunction.vonMangoldt d := by
  apply Finset.sum_congr rfl
  intro d hdmem
  rw [psi_natCast_div_eq_sawtoothQuot a d (by
    have := Detector.one_lt_of_mem_squareRootInterval hdmem
    omega)]
  ring

/-- Equation (7.1) rewritten with the real sawtooth used by the Fourier
module. -/
theorem sawtooth_mangoldt_detector_psi (n : ℕ)
    (hsq : Squarefree (Nat.choose (n + n) n)) :
    (1 / 2 : ℝ) *
        (∑ d ∈ (Detector.squareRootInterval n).filter fun d =>
          Nat.Coprime d (2 * n), ArithmeticFunction.vonMangoldt d) ≤
      |∑ d ∈ Detector.squareRootInterval n,
          ArithmeticFunction.vonMangoldt d *
            Sawtooth.psi (((2 * n : ℕ) : ℝ) / (d : ℝ))| +
        2 * |∑ d ∈ Detector.squareRootInterval n,
          ArithmeticFunction.vonMangoldt d *
            Sawtooth.psi ((n : ℝ) / (d : ℝ))| := by
  rw [sum_psi_eq_sum_sawtoothQuot (2 * n) n,
    sum_psi_eq_sum_sawtoothQuot n n]
  exact Detector.sawtooth_mangoldt_detector n hsq

/-- The interval defined by square inequalities in the Kummer detector is
exactly the integer interval used by the reciprocal exponential-sum theorem. -/
lemma squareRootInterval_eq_Ioc (n : ℕ) :
    Detector.squareRootInterval n = Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)) := by
  ext d
  rw [Detector.mem_squareRootInterval]
  simp only [mem_Ioc]
  constructor
  · rintro ⟨_hd1, _hdn, hlo, hhi⟩
    exact ⟨(Nat.sqrt_lt').2 hlo, Nat.le_sqrt.mpr (by simpa [pow_two] using hhi)⟩
  · rintro ⟨hlo, hhi⟩
    have hlo' : n < d ^ 2 := by
      exact (Nat.sqrt_lt').1 hlo
    have hhi' : d ^ 2 ≤ 2 * n := by
      simpa [pow_two] using Nat.le_sqrt.mp hhi
    have hd1 : 1 ≤ d := by omega
    have hdn : d ≤ 2 * n := by
      calc
        d ≤ d ^ 2 := by nlinarith
        _ ≤ 2 * n := hhi'
    exact ⟨hd1, hdn, hlo', hhi'⟩

/-- The reciprocal von Mangoldt sum on the interval occurring in the
Kummer detector. -/
noncomputable def reciprocalMangoldtSum (n : ℕ) (x : ℝ) : ℂ :=
  ∑ d ∈ Detector.squareRootInterval n,
    (ArithmeticFunction.vonMangoldt d : ℂ) *
      Sawtooth.e (x / (d : ℝ))

/-- The assembly sum is definitionally the Vaughan-module reciprocal sum,
after identifying the two descriptions of the interval and commuting the
two scalar factors in the complex exponential. -/
lemma reciprocalMangoldtSum_eq_vaughan (n : ℕ) (x : ℝ) :
    reciprocalMangoldtSum n x =
      Vaughan.reciprocalSum (Ioc (Nat.sqrt n) (Nat.sqrt (2 * n))) x
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
  rw [← squareRootInterval_eq_Ioc]
  unfold reciprocalMangoldtSum Vaughan.reciprocalSum Vaughan.finiteWeightedSum
    Vaughan.reciprocalPhase Sawtooth.e
  apply Finset.sum_congr rfl
  intro d _hd
  congr 1
  congr 1
  push_cast
  ring

/-! ## A coarse explicit numerical cutoff

The elementary Chebyshev route under development gives the smaller Section 7
constant `1 / 50`.  The following calculation shows that raising the finite
cutoff to `2 ^ 1728` is sufficient for exactly the same Theorem 9 upper bound.
-/

private noncomputable def coarseCutoffGap (x : ℝ) : ℝ :=
  Real.log x / 48 - Real.log 160 -
    (11 / 4 : ℝ) * Real.log (Real.log (256 * x))

private lemma coarse_endpoint_power_bound :
    (160 : ℝ) ^ 48 * (1204 : ℝ) ^ 132 < (2 : ℝ) ^ 1728 := by
  have hnat : 160 ^ 48 * 1204 ^ 132 < 2 ^ 1728 := by
    rw [show 2 ^ 1728 = (2 ^ 100) ^ 17 * 2 ^ 28 by
      calc
        2 ^ 1728 = 2 ^ (1700 + 28) := by norm_num
        _ = 2 ^ 1700 * 2 ^ 28 := pow_add 2 1700 28
        _ = 2 ^ (100 * 17) * 2 ^ 28 := by norm_num
        _ = (2 ^ 100) ^ 17 * 2 ^ 28 := by rw [pow_mul]]
    norm_num
  exact_mod_cast hnat

private lemma coarseCutoffGap_endpoint_pos :
    0 < coarseCutoffGap ((2 : ℝ) ^ 1728) := by
  have hinnerpos : 0 < 1736 * Real.log 2 := by positivity
  have hinnerUpper : 1736 * Real.log 2 < (1204 : ℝ) := by
    nlinarith [Real.log_two_lt_d9]
  have hlogInnerUpper :
      Real.log (1736 * Real.log 2) < Real.log (1204 : ℝ) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hinnerpos)
      (Set.mem_Ioi.mpr (by norm_num)) hinnerUpper
  have hp := coarse_endpoint_power_bound
  have hp' := Real.strictMonoOn_log (Set.mem_Ioi.mpr (by positivity))
    (Set.mem_Ioi.mpr (by positivity)) hp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_pow, Real.log_pow] at hp'
  have hlogPow : Real.log ((2 : ℝ) ^ 1728) = 1728 * Real.log 2 :=
    Real.log_pow 2 1728
  have harg : 256 * (2 : ℝ) ^ 1728 = (2 : ℝ) ^ 1736 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add]
  have hinner : Real.log (256 * (2 : ℝ) ^ 1728) = 1736 * Real.log 2 := by
    rw [harg, Real.log_pow]
    norm_num
  dsimp [coarseCutoffGap]
  rw [hlogPow, hinner]
  norm_num at hp' ⊢
  linarith

private lemma coarseCutoffGap_hasDerivAt {x : ℝ} (hxpos : 0 < x)
    (hinnerpos : 0 < Real.log (256 * x)) :
    HasDerivAt coarseCutoffGap
      (x⁻¹ / 48 - (11 / 4 : ℝ) * (256 / (256 * x)) /
        Real.log (256 * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ 256 * y) 256 x := by
    simpa [mul_comm] using (hasDerivAt_id x).const_mul (256 : ℝ)
  have hloglin : HasDerivAt (fun y : ℝ ↦ Real.log (256 * y))
      (256 / (256 * x)) x := hlin.log (by positivity)
  have hloglog : HasDerivAt (fun y : ℝ ↦ Real.log (Real.log (256 * y)))
      ((256 / (256 * x)) / Real.log (256 * x)) x :=
    hloglin.log hinnerpos.ne'
  unfold coarseCutoffGap
  have hfull := (((Real.hasDerivAt_log hxpos.ne').div_const 48).sub_const
    (Real.log 160)).sub ((hasDerivAt_const x (11 / 4 : ℝ)).mul hloglog)
  refine (hfull.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  filter_upwards with y
  rfl

private lemma coarseCutoffGap_strictMonoOn :
    StrictMonoOn coarseCutoffGap (Set.Ici ((2 : ℝ) ^ 1728)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _) (by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 1728).trans_le hx
    have hxone : 1 < x := (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (1728 : ℕ) ≠ 0)).trans_le hx
    have hlogpos : 0 < Real.log (256 * x) := Real.log_pos (by nlinarith)
    exact (coarseCutoffGap_hasDerivAt hxpos hlogpos).continuousAt)
  intro x hx
  rw [interior_Ici, Set.mem_Ioi] at hx
  have hxpos : 0 < x := (by positivity : 0 < (2 : ℝ) ^ 1728).trans hx
  have hlogarg : 132 < Real.log (256 * x) := by
    have hmono : Real.log (256 * (2 : ℝ) ^ 1728) < Real.log (256 * x) := by
      exact Real.strictMonoOn_log (Set.mem_Ioi.mpr (by positivity))
        (Set.mem_Ioi.mpr (by positivity))
        (mul_lt_mul_of_pos_left hx (by norm_num))
    have hbase : 132 < Real.log (256 * (2 : ℝ) ^ 1728) := by
      rw [show 256 * (2 : ℝ) ^ 1728 = (2 : ℝ) ^ 1736 by
          rw [show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_add],
        Real.log_pow]
      norm_num
      nlinarith [Real.log_two_gt_d9]
    exact hbase.trans hmono
  have hinnerpos : 0 < Real.log (256 * x) := by linarith
  have hderiv := coarseCutoffGap_hasDerivAt hxpos hinnerpos
  rw [hderiv.deriv]
  have hsimp : 256 / (256 * x) = x⁻¹ := by
    field_simp [hxpos.ne']
  rw [hsimp]
  have hxinv : 0 < x⁻¹ := inv_pos.mpr hxpos
  have hcoef : 0 < (1 / 48 : ℝ) -
      (11 / 4 : ℝ) / Real.log (256 * x) := by
    rw [sub_pos, div_lt_iff₀ hinnerpos]
    nlinarith
  have heq :
      x⁻¹ / 48 - (11 / 4 : ℝ) * x⁻¹ / Real.log (256 * x) =
        x⁻¹ * ((1 / 48 : ℝ) -
          (11 / 4 : ℝ) / Real.log (256 * x)) := by
    ring
  rw [heq]
  exact mul_pos hxinv hcoef

private lemma coarseCutoffGap_pos_of_cutoff {x : ℝ}
    (hx : (2 : ℝ) ^ 1728 ≤ x) : 0 < coarseCutoffGap x := by
  rcases hx.eq_or_lt with rfl | hxlt
  · exact coarseCutoffGap_endpoint_pos
  · exact coarseCutoffGap_endpoint_pos.trans
      (coarseCutoffGap_strictMonoOn (Set.mem_Ici.mpr (le_refl _))
        (Set.mem_Ici.mpr hx) hxlt)

/-- Above `2 ^ 1728`, the specialized Theorem 9 upper bound is already
smaller than `sqrt n / 50`. -/
theorem coarse_numeric_contradiction {n : ℕ} (hn : 2 ^ 1728 ≤ n) :
    (3.2 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ) <
      (1 / 50 : ℝ) * Real.sqrt n := by
  have hnreal : (2 : ℝ) ^ 1728 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) :=
    (by positivity : 0 < (2 : ℝ) ^ 1728).trans_le hnreal
  have hlogpos : 0 < Real.log (256 * (n : ℝ)) := by
    apply Real.log_pos
    have hnNat : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
    exact_mod_cast (show 1 < 256 * n by omega)
  have hgap := coarseCutoffGap_pos_of_cutoff hnreal
  have hcore :
      (160 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
          (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ) < Real.sqrt n := by
    rw [← Real.log_lt_log_iff (by positivity) (Real.sqrt_pos.2 hnpos)]
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_rpow hnpos,
      Real.log_rpow hlogpos, Real.sqrt_eq_rpow, Real.log_rpow hnpos]
    dsimp [coarseCutoffGap] at hgap
    nlinarith
  nlinarith [mul_lt_mul_of_pos_left hcore
    (show (0 : ℝ) < 1 / 50 by norm_num)]

/-- Contradiction form used by `large_case_of_bounds`. -/
theorem not_coarse_lower_le_upper_of_ge_cutoff {n : ℕ}
    (hn : 2 ^ 1728 ≤ n) :
    ¬ ((1 / 50 : ℝ) * Real.sqrt n ≤
      (3.2 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
        (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ)) := by
  exact not_le_of_gt (coarse_numeric_contradiction hn)

/-- A non-squarefree natural has a prime-square divisor.  This is the
classical logical converse to the direction used in the elementary file. -/
lemma exists_prime_sq_dvd_of_not_squarefree {m : ℕ} (hm : ¬ Squarefree m) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ m := by
  by_contra h
  push Not at h
  apply hm
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp
  simpa [pow_two] using h p hp

/-- Cutoff- and constant-parametric assembly of the large-index argument.

`hlower` is the output of the Kummer detector, finite Fourier majorants, and
the explicit Chebyshev interval estimate.  `hupper` is the specialized
Granville--Ramaré Theorem 9 estimate.  `hincompatible` is the purely numerical
cutoff calculation.  Keeping these three independently checkable inputs in
the statement makes it possible to use either the published `(1617, 2/35)`
pair or a coarser elementary Chebyshev estimate with a slightly larger
cutoff. -/
theorem large_case_of_bounds
    (cutoff : ℕ) (C : ℝ) (upper : ℕ → ℝ)
    (hlower : ∀ n : ℕ, cutoff ≤ n →
      Squarefree (Nat.choose (2 * n) n) →
        ∃ x : ℝ,
          (n : ℝ) ≤ x ∧ x ≤ 20 * (n : ℝ) ∧
            C * Real.sqrt n ≤ ‖reciprocalMangoldtSum n x‖)
    (hupper : ∀ n : ℕ, cutoff ≤ n → ∀ x : ℝ,
      (n : ℝ) ≤ x → x ≤ 20 * (n : ℝ) →
        ‖reciprocalMangoldtSum n x‖ ≤ upper n)
    (hincompatible : ∀ n : ℕ, cutoff ≤ n → ¬ C * Real.sqrt n ≤ upper n)
    {n : ℕ} (hn : cutoff ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ Nat.choose (2 * n) n := by
  apply exists_prime_sq_dvd_of_not_squarefree
  intro hsq
  obtain ⟨x, hxlo, hxhi, hlower'⟩ := hlower n hn hsq
  exact hincompatible n hn (hlower'.trans (hupper n hn x hxlo hxhi))

/-- The coarse `(2 ^ 1728, 1 / 50)` specialization, with the numerical
contradiction discharged by `NumericCutoff`.  Its two remaining inputs are
exactly the Section 7 and Theorem 9 analytic estimates. -/
theorem large_case_of_coarse_analytic_bounds
    (hlower : ∀ n : ℕ, 2 ^ 1728 ≤ n →
      Squarefree (Nat.choose (2 * n) n) →
        ∃ x : ℝ,
          (n : ℝ) ≤ x ∧ x ≤ 20 * (n : ℝ) ∧
            (1 / 50 : ℝ) * Real.sqrt n ≤ ‖reciprocalMangoldtSum n x‖)
    (hupper : ∀ n : ℕ, 2 ^ 1728 ≤ n → ∀ x : ℝ,
      (n : ℝ) ≤ x → x ≤ 20 * (n : ℝ) →
        ‖reciprocalMangoldtSum n x‖ ≤
          (3.2 : ℝ) * (n : ℝ) ^ (23 / 48 : ℝ) *
            (Real.log (256 * (n : ℝ))) ^ (11 / 4 : ℝ))
    {n : ℕ} (hn : 2 ^ 1728 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ Nat.choose (2 * n) n := by
  exact large_case_of_bounds (2 ^ 1728) (1 / 50)
    (fun m => (3.2 : ℝ) * (m : ℝ) ^ (23 / 48 : ℝ) *
      (Real.log (256 * (m : ℝ))) ^ (11 / 4 : ℝ))
    hlower hupper (fun m hm => not_coarse_lower_le_upper_of_ge_cutoff hm) hn

/-- Power-of-two specialization of the large bridge.  This is the only form
needed after the elementary binary reduction, and it lets Section 7 exploit
that every prime power non-coprime to `2 * 2 ^ k` is itself a power of two. -/
theorem large_case_of_coarse_analytic_bounds_two_pow
    (hlower : ∀ k : ℕ, 1728 ≤ k →
      Squarefree (Nat.choose (2 * 2 ^ k) (2 ^ k)) →
        ∃ x : ℝ,
          ((2 ^ k : ℕ) : ℝ) ≤ x ∧ x ≤ 20 * ((2 ^ k : ℕ) : ℝ) ∧
            (1 / 50 : ℝ) * Real.sqrt (2 ^ k : ℕ) ≤
              ‖reciprocalMangoldtSum (2 ^ k) x‖)
    (hupper : ∀ k : ℕ, 1728 ≤ k → ∀ x : ℝ,
      ((2 ^ k : ℕ) : ℝ) ≤ x → x ≤ 20 * ((2 ^ k : ℕ) : ℝ) →
        ‖reciprocalMangoldtSum (2 ^ k) x‖ ≤
          (3.2 : ℝ) * ((2 ^ k : ℕ) : ℝ) ^ (23 / 48 : ℝ) *
            (Real.log (256 * ((2 ^ k : ℕ) : ℝ))) ^ (11 / 4 : ℝ))
    {k : ℕ} (hk : 1728 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ Nat.choose (2 * 2 ^ k) (2 ^ k) := by
  apply exists_prime_sq_dvd_of_not_squarefree
  intro hsq
  obtain ⟨x, hxlo, hxhi, hlower'⟩ := hlower k hk hsq
  have hn : 2 ^ 1728 ≤ (2 : ℕ) ^ k :=
    Nat.pow_le_pow_right (by norm_num) hk
  exact not_coarse_lower_le_upper_of_ge_cutoff hn
    (hlower'.trans (hupper k hk x hxlo hxhi))

#print axioms coarse_numeric_contradiction
#print axioms large_case_of_coarse_analytic_bounds
#print axioms large_case_of_coarse_analytic_bounds_two_pow

end Erdos175.Large
