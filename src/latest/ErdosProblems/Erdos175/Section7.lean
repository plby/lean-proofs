/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Granville--Ramaré, Section 7: the concrete lower bound for a reciprocal
von Mangoldt exponential sum.
-/

import ErdosProblems.Erdos175.Detector
import ErdosProblems.Erdos175.Sawtooth
import ErdosProblems.Erdos175.FourierCoefficients
import ErdosProblems.Erdos175.ExplicitChebyshev
import ErdosProblems.Erdos175.VaalerDegreeTen

noncomputable section

namespace Erdos175.Section7

open Nat Finset
open scoped BigOperators ArithmeticFunction.vonMangoldt

alias I := Detector.squareRootInterval

/-- The square-description of the summation interval agrees exactly with
the half-open integer interval used by the analytic estimates. -/
lemma squareRootInterval_eq_Ioc (n : ℕ) :
    I n = Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)) := by
  ext d
  simp only [I, Detector.squareRootInterval, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc, Nat.sqrt_lt', Nat.le_sqrt']
  constructor
  · rintro ⟨⟨hd1, hd2n⟩, hn, h2n⟩
    exact ⟨hn, h2n⟩
  · rintro ⟨hn, h2n⟩
    have hd1 : 1 ≤ d := by
      by_contra h
      have : d = 0 := by omega
      subst d
      simp at hn
    have hd2n : d ≤ 2 * n := by
      calc
        d ≤ d ^ 2 := by nlinarith
        _ ≤ 2 * n := h2n
    exact ⟨⟨hd1, hd2n⟩, hn, h2n⟩

/-- The discrete detector's sawtooth is the value of the real sawtooth at
the corresponding rational number. -/
lemma psi_natCast_div (a d : ℕ) (hd : 0 < d) :
    Sawtooth.psi ((a : ℝ) / d) = Detector.sawtoothQuot a d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hfract : Int.fract ((a : ℝ) / d) = ((a % d : ℕ) : ℝ) / d := by
    exact Int.fract_div_natCast_eq_div_natCast_mod
  by_cases hda : d ∣ a
  · have hmod : a % d = 0 := Nat.mod_eq_zero_of_dvd hda
    have hfrac0 : Int.fract ((a : ℝ) / d) = 0 := by simp [hfract, hmod]
    have hfloor : (a : ℝ) / d = (⌊(a : ℝ) / d⌋ : ℝ) := by
      rw [Int.fract] at hfrac0
      linarith
    rw [Sawtooth.psi, if_pos hfloor, Detector.sawtoothQuot, if_pos hda]
  · have hmod : a % d ≠ 0 := by
      exact fun h => hda (Nat.dvd_of_mod_eq_zero h)
    have hfrac_ne : Int.fract ((a : ℝ) / d) ≠ 0 := by
      rw [hfract]
      exact div_ne_zero (by exact_mod_cast hmod) hdR
    have hfloor : (a : ℝ) / d ≠ (⌊(a : ℝ) / d⌋ : ℝ) := by
      intro h
      apply hfrac_ne
      rw [Int.fract]
      linarith
    rw [Sawtooth.psi, if_neg hfloor, Detector.sawtoothQuot, if_neg hda, hfract]

/-- The reciprocal von Mangoldt exponential sum on the Section 7 interval. -/
def mangoldtSum (n : ℕ) (x : ℝ) : ℂ :=
  ∑ d ∈ Finset.Ioc (Nat.sqrt n) (Nat.sqrt (2 * n)),
    (ArithmeticFunction.vonMangoldt d : ℂ) * Sawtooth.e (x / (d : ℝ))

/-- Two prime powers in the short interval with the same underlying prime
are equal.  The point is that two distinct consecutive powers differ by a
factor at least two, whereas the squared endpoints differ by only a factor
two. -/
lemma minFac_injective_on_interval_primePowers {n d e : ℕ}
    (hd : d ∈ I n) (he : e ∈ I n)
    (hdpp : IsPrimePow d) (hepp : IsPrimePow e)
    (hmin : Nat.minFac d = Nat.minFac e) : d = e := by
  obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff d).mp hdpp
  obtain ⟨q, b, hq, hb, rfl⟩ := (isPrimePow_nat_iff e).mp hepp
  have hpq : p = q := by
    simpa [Nat.pow_minFac ha.ne', Nat.pow_minFac hb.ne', hp.minFac_eq,
      hq.minFac_eq] using hmin
  subst q
  have hdmem := Detector.mem_squareRootInterval.mp hd
  have hemel := Detector.mem_squareRootInterval.mp he
  by_contra hab
  have habexp : a ≠ b := by
    intro h
    exact hab (congrArg (p ^ ·) h)
  rcases lt_or_gt_of_ne habexp with hab | hba
  · have hpow : 2 * p ^ a ≤ p ^ b := by
      calc
        2 * p ^ a ≤ p * p ^ a := Nat.mul_le_mul_right _ hp.two_le
        _ = p ^ (a + 1) := by rw [pow_succ']
        _ ≤ p ^ b := Nat.pow_le_pow_right hp.pos (by omega)
    have hsquare := Nat.pow_le_pow_left hpow 2
    nlinarith [hdmem.2.2.1, hemel.2.2.2]
  · have hpow : 2 * p ^ b ≤ p ^ a := by
      calc
        2 * p ^ b ≤ p * p ^ b := Nat.mul_le_mul_right _ hp.two_le
        _ = p ^ (b + 1) := by rw [pow_succ']
        _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
    have hsquare := Nat.pow_le_pow_left hpow 2
    nlinarith [hemel.2.2.1, hdmem.2.2.2]

/-- The von Mangoldt mass of interval terms sharing a prime factor with
`2n` is at most `log (2n)`.  Each nonzero term is a prime power; the short
interval contains at most one power of each base prime, and those base
primes are distinct divisors of `2n`. -/
lemma bad_mangoldt_mass_le_log_two_mul (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ (I n).filter fun d => ¬Nat.Coprime d (2 * n),
      ArithmeticFunction.vonMangoldt d) ≤ Real.log (2 * n) := by
  let bad := (I n).filter fun d => ¬Nat.Coprime d (2 * n)
  let badPP := bad.filter IsPrimePow
  have hbad_eq :
      (∑ d ∈ bad, ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ badPP, ArithmeticFunction.vonMangoldt d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    simpa [badPP, hd] using hnot
  have hinj : Set.InjOn Nat.minFac (badPP : Set ℕ) := by
    intro d hd e he hde
    have hd' := Finset.mem_filter.mp hd
    have he' := Finset.mem_filter.mp he
    have hdbad := Finset.mem_filter.mp hd'.1
    have hebad := Finset.mem_filter.mp he'.1
    exact minFac_injective_on_interval_primePowers hdbad.1 hebad.1 hd'.2 he'.2 hde
  have hterm (d : ℕ) (hd : d ∈ badPP) :
      ArithmeticFunction.vonMangoldt d =
        ArithmeticFunction.vonMangoldt (Nat.minFac d) := by
    have hdpp := (Finset.mem_filter.mp hd).2
    obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff d).mp hdpp
    rw [ArithmeticFunction.vonMangoldt_apply_pow ha.ne']
    simp [Nat.pow_minFac ha.ne', hp.minFac_eq]
  have hbase_mem : badPP.image Nat.minFac ⊆ (2 * n).divisors := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hp
    have hd' := Finset.mem_filter.mp hd
    have hdbad := Finset.mem_filter.mp hd'.1
    have hdpp := hd'.2
    obtain ⟨q, a, hq, ha, hqa⟩ := (isPrimePow_nat_iff d).mp hdpp
    have hmin : Nat.minFac d = q := by
      rw [← hqa, Nat.pow_minFac ha.ne', hq.minFac_eq]
    rw [hmin]
    have hqdvd : q ∣ 2 * n := by
      by_contra hqnot
      have hcop : Nat.Coprime q (2 * n) := hq.coprime_iff_not_dvd.mpr hqnot
      apply hdbad.2
      rw [← hqa]
      exact hcop.pow_left a
    exact Nat.mem_divisors.mpr ⟨hqdvd, by positivity⟩
  calc
    (∑ d ∈ (I n).filter fun d => ¬Nat.Coprime d (2 * n),
        ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ badPP, ArithmeticFunction.vonMangoldt d := by
          simpa only [bad] using hbad_eq
    _ = ∑ d ∈ badPP, ArithmeticFunction.vonMangoldt (Nat.minFac d) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = ∑ p ∈ badPP.image Nat.minFac, ArithmeticFunction.vonMangoldt p := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ (2 * n).divisors, ArithmeticFunction.vonMangoldt p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hbase_mem fun p _ _ =>
        ArithmeticFunction.vonMangoldt_nonneg
    _ = Real.log (2 * n) := by
      rw [ArithmeticFunction.vonMangoldt_sum]
      norm_num [Nat.cast_mul]

/-- The discrete Kummer detector rewritten with the real sawtooth and the
standard half-open square-root interval. -/
lemma sawtooth_mangoldt_detector_psi (n : ℕ)
    (hsq : Squarefree (Nat.choose (n + n) n)) :
    (1 / 2 : ℝ) *
        (∑ d ∈ (I n).filter fun d => Nat.Coprime d (2 * n),
          ArithmeticFunction.vonMangoldt d) ≤
      |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((2 * n : ℕ) / (d : ℝ))| +
        2 * |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((n : ℝ) / (d : ℝ))| := by
  have h := Detector.sawtooth_mangoldt_detector n hsq
  change (1 / 2 : ℝ) *
      (∑ d ∈ (I n).filter fun d => Nat.Coprime d (2 * n),
        ArithmeticFunction.vonMangoldt d) ≤
    |∑ d ∈ I n, Detector.sawtoothQuot (2 * n) d *
        ArithmeticFunction.vonMangoldt d| +
      2 * |∑ d ∈ I n, Detector.sawtoothQuot n d *
        ArithmeticFunction.vonMangoldt d| at h
  have htwo :
      (∑ d ∈ I n, Detector.sawtoothQuot (2 * n) d *
          ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((2 * n : ℕ) / (d : ℝ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : 0 < d := lt_trans Nat.zero_lt_one
      (Detector.one_lt_of_mem_squareRootInterval hd)
    rw [psi_natCast_div _ _ hd0]
    ring
  have hone :
      (∑ d ∈ I n, Detector.sawtoothQuot n d *
          ArithmeticFunction.vonMangoldt d) =
        ∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((n : ℝ) / (d : ℝ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : 0 < d := lt_trans Nat.zero_lt_one
      (Detector.one_lt_of_mem_squareRootInterval hd)
    rw [psi_natCast_div _ _ hd0]
    ring
  rw [htwo, hone] at h
  simpa only [Nat.mul_comm] using h

/-- The form of (7.1) used by the Fourier step: the coprime restriction is
replaced by subtracting the complementary nonnegative mass. -/
lemma sawtooth_mangoldt_detector_sub_bad (n : ℕ)
    (hsq : Squarefree (Nat.choose (n + n) n)) :
    ((∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) -
        ∑ d ∈ (I n).filter (fun d => ¬Nat.Coprime d (2 * n)),
          ArithmeticFunction.vonMangoldt d) / 2 ≤
      |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((2 * n : ℕ) / (d : ℝ))| +
        2 * |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
          Sawtooth.psi ((n : ℝ) / (d : ℝ))| := by
  have h := sawtooth_mangoldt_detector_psi n hsq
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := I n)
    (p := fun d => Nat.Coprime d (2 * n))
    (f := fun d => ArithmeticFunction.vonMangoldt d)
  have hid :
      (∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) -
          ∑ d ∈ (I n).filter (fun d => ¬Nat.Coprime d (2 * n)),
            ArithmeticFunction.vonMangoldt d =
        ∑ d ∈ (I n).filter (fun d => Nat.Coprime d (2 * n)),
          ArithmeticFunction.vonMangoldt d := by
    linarith
  rw [hid]
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

/-- Negating the phase conjugates the standard additive character. -/
lemma e_neg (x : ℝ) : Sawtooth.e (-x) = (starRingEnd ℂ) (Sawtooth.e x) := by
  rw [Sawtooth.e, Sawtooth.e, ← Complex.exp_conj]
  apply congrArg Complex.exp
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Every signed degree-ten Fourier phase has the norm of the actual
reciprocal Mangoldt sum at the corresponding positive frequency. -/
lemma weightedPhaseSum_norm_eq_mangoldtSum (n c : ℕ) (r : ℤ) :
    ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => ((c * n : ℕ) : ℝ) / d) r‖ =
      ‖mangoldtSum n ((r.natAbs : ℝ) * c * n)‖ := by
  rcases le_total 0 r with hr | hr
  · have hrcast : (r : ℝ) = r.natAbs := by
      simpa using congrArg (fun z : ℤ => (z : ℝ))
        (Int.eq_natAbs_of_nonneg hr)
    apply congrArg norm
    rw [Sawtooth.weightedPhaseSum, mangoldtSum, ← squareRootInterval_eq_Ioc]
    apply Finset.sum_congr rfl
    intro d hd
    congr 1
    apply congrArg Sawtooth.e
    rw [hrcast]
    push_cast
    ring
  · have hrcast : (r : ℝ) = -(r.natAbs : ℝ) := by
      simpa using congrArg (fun z : ℤ => (z : ℝ))
        (Int.eq_neg_natAbs_of_nonpos hr)
    have hsum :
        Sawtooth.weightedPhaseSum (I n)
            (fun d => ArithmeticFunction.vonMangoldt d)
            (fun d => ((c * n : ℕ) : ℝ) / d) r =
          (starRingEnd ℂ) (mangoldtSum n ((r.natAbs : ℝ) * c * n)) := by
      rw [Sawtooth.weightedPhaseSum, mangoldtSum, ← squareRootInterval_eq_Ioc,
        map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [map_mul, Complex.conj_ofReal]
      congr 1
      rw [← e_neg]
      apply congrArg Sawtooth.e
      rw [hrcast]
      push_cast
      ring
    rw [hsum, Complex.norm_conj]

/-- The nonzero order-three Fourier frequencies have absolute value between
one and three. -/
lemma natAbs_bounds_of_mem_frequencies_three {r : ℤ}
    (hr : r ∈ Sawtooth.frequencies 3) : 1 ≤ r.natAbs ∧ r.natAbs ≤ 3 := by
  simp only [Sawtooth.frequencies, Finset.mem_erase, Finset.mem_Icc] at hr
  rcases hr with ⟨hr0, hrlo, hrhi⟩
  interval_cases r <;> norm_num at *

/-- If the reciprocal Mangoldt sum is smaller than `M` throughout
`[n,6n]`, then both families of order-three Fourier phases used by the
detector are bounded by `M`. -/
lemma degreeThree_phase_bounds_of_forall_lt (n : ℕ) (M : ℝ)
    (hsmall : ∀ x : ℝ, (n : ℝ) ≤ x → x ≤ 6 * n → ‖mangoldtSum n x‖ < M) :
    (∀ r ∈ Sawtooth.frequencies 3,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => ((2 * n : ℕ) : ℝ) / d) r‖ ≤ M) ∧
    (∀ r ∈ Sawtooth.frequencies 3,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => (n : ℝ) / d) r‖ ≤ M) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  constructor
  · intro r hr
    obtain ⟨hr1, hr3⟩ := natAbs_bounds_of_mem_frequencies_three hr
    have hr1R : (1 : ℝ) ≤ r.natAbs := by exact_mod_cast hr1
    have hr3R : (r.natAbs : ℝ) ≤ 3 := by exact_mod_cast hr3
    rw [weightedPhaseSum_norm_eq_mangoldtSum n 2 r]
    apply (hsmall ((r.natAbs : ℝ) * 2 * n) (by nlinarith) (by nlinarith)).le
  · intro r hr
    obtain ⟨hr1, hr3⟩ := natAbs_bounds_of_mem_frequencies_three hr
    have hr1R : (1 : ℝ) ≤ r.natAbs := by exact_mod_cast hr1
    have hr3R : (r.natAbs : ℝ) ≤ 3 := by exact_mod_cast hr3
    have hmap := weightedPhaseSum_norm_eq_mangoldtSum n 1 r
    simp only [one_mul, mul_one, Nat.cast_one] at hmap
    rw [hmap]
    exact (hsmall ((r.natAbs : ℝ) * n) (by nlinarith) (by nlinarith)).le

/-- Generic finite-Fourier form of the Section 7 argument.  If `psi` and
`-psi` have trigonometric upper majorants with mean `c` and coefficient
`ℓ¹` norm at most `A`, and every relevant reciprocal phase sum has norm at
most `M`, then the Kummer detector and the discarded-prime estimate give
this inequality.  Keeping `c` and `A` explicit lets us use any fully
verified finite majorant. -/
lemma generic_section7_inequality (n : ℕ) (hn : 0 < n)
    (hsq : Squarefree (Nat.choose (n + n) n))
    (F : Finset ℤ) (c A M : ℝ) (aPlus aMinus : ℤ → ℂ)
    (hplus : Sawtooth.IsUpperMajorant F Sawtooth.psi c aPlus)
    (hminus : Sawtooth.IsUpperMajorant F (fun x => -Sawtooth.psi x) c aMinus)
    (hcoeffPlus : (∑ r ∈ F, ‖aPlus r‖) ≤ A)
    (hcoeffMinus : (∑ r ∈ F, ‖aMinus r‖) ≤ A)
    (hphaseTwo : ∀ r ∈ F,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => ((2 * n : ℕ) : ℝ) / d) r‖ ≤ M)
    (hphaseOne : ∀ r ∈ F,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => (n : ℝ) / d) r‖ ≤ M)
    (hM : 0 ≤ M) :
    (1 / 2 - 3 * c) *
        (∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) ≤
      3 * A * M + (1 / 2) * Real.log (2 * n) := by
  let S : ℝ := ∑ d ∈ I n, ArithmeticFunction.vonMangoldt d
  let bad : ℝ :=
    ∑ d ∈ (I n).filter (fun d => ¬Nat.Coprime d (2 * n)),
      ArithmeticFunction.vonMangoldt d
  let U : ℝ :=
    |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
      Sawtooth.psi ((2 * n : ℕ) / (d : ℝ))|
  let V : ℝ :=
    |∑ d ∈ I n, ArithmeticFunction.vonMangoldt d *
      Sawtooth.psi ((n : ℝ) / (d : ℝ))|
  have hw : ∀ d ∈ I n, 0 ≤ ArithmeticFunction.vonMangoldt d := by
    intro d hd
    exact ArithmeticFunction.vonMangoldt_nonneg
  have hU : U ≤ c * S + A * M := by
    exact Sawtooth.abs_weighted_sum_le_of_majorants
      (I n) (fun d => ArithmeticFunction.vonMangoldt d)
      (fun d => ((2 * n : ℕ) : ℝ) / d) F Sawtooth.psi c A M
      aPlus aMinus hw hplus hminus hphaseTwo hcoeffPlus hcoeffMinus hM
  have hV : V ≤ c * S + A * M := by
    exact Sawtooth.abs_weighted_sum_le_of_majorants
      (I n) (fun d => ArithmeticFunction.vonMangoldt d)
      (fun d => (n : ℝ) / d) F Sawtooth.psi c A M
      aPlus aMinus hw hplus hminus hphaseOne hcoeffPlus hcoeffMinus hM
  have hdetector : (S - bad) / 2 ≤ U + 2 * V := by
    exact sawtooth_mangoldt_detector_sub_bad n hsq
  have hbad : bad ≤ Real.log (2 * n) := bad_mangoldt_mass_le_log_two_mul n hn
  dsimp only [S, bad, U, V] at hU hV hdetector hbad ⊢
  linarith

/-- The generic inequality specialized to the explicit order-three
constants `c = 33/200` and `A = 3/4`. -/
lemma degreeThree_section7_upper_of_data (n : ℕ) (hn : 0 < n)
    (hsq : Squarefree (Nat.choose (n + n) n)) (M : ℝ)
    (aPlus aMinus : ℤ → ℂ)
    (hplus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      Sawtooth.psi (33 / 200) aPlus)
    (hminus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      (fun x => -Sawtooth.psi x) (33 / 200) aMinus)
    (hcoeffPlus : (∑ r ∈ Sawtooth.frequencies 3, ‖aPlus r‖) ≤ 3 / 4)
    (hcoeffMinus : (∑ r ∈ Sawtooth.frequencies 3, ‖aMinus r‖) ≤ 3 / 4)
    (hphaseTwo : ∀ r ∈ Sawtooth.frequencies 3,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => ((2 * n : ℕ) : ℝ) / d) r‖ ≤ M)
    (hphaseOne : ∀ r ∈ Sawtooth.frequencies 3,
      ‖Sawtooth.weightedPhaseSum (I n)
        (fun d => ArithmeticFunction.vonMangoldt d)
        (fun d => (n : ℝ) / d) r‖ ≤ M)
    (hM : 0 ≤ M) :
    (∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) ≤
      450 * M + 100 * Real.log (2 * n) := by
  have h := generic_section7_inequality n hn hsq
    (Sawtooth.frequencies 3) (33 / 200) (3 / 4) M aPlus aMinus
    hplus hminus hcoeffPlus hcoeffMinus hphaseTwo hphaseOne hM
  norm_num at h ⊢
  linarith

/-- Once the explicit order-three majorants are known, any strict numerical
lower bound beyond the Section 7 loss forces a genuinely large reciprocal
Mangoldt sum at one of the finitely many frequencies in `[n,6n]`. -/
lemma exists_large_mangoldtSum_of_degreeThree_data (n : ℕ) (hn : 0 < n)
    (hsq : Squarefree (Nat.choose (n + n) n)) (M : ℝ)
    (aPlus aMinus : ℤ → ℂ)
    (hplus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      Sawtooth.psi (33 / 200) aPlus)
    (hminus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      (fun x => -Sawtooth.psi x) (33 / 200) aMinus)
    (hcoeffPlus : (∑ r ∈ Sawtooth.frequencies 3, ‖aPlus r‖) ≤ 3 / 4)
    (hcoeffMinus : (∑ r ∈ Sawtooth.frequencies 3, ‖aMinus r‖) ≤ 3 / 4)
    (hM : 0 ≤ M)
    (hnumeric : M <
      ((∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) -
        100 * Real.log (2 * n)) / 450) :
    ∃ x : ℝ, (n : ℝ) ≤ x ∧ x ≤ 6 * n ∧ M ≤ ‖mangoldtSum n x‖ := by
  by_contra hlarge
  push Not at hlarge
  have hsmall : ∀ x : ℝ, (n : ℝ) ≤ x → x ≤ 6 * n →
      ‖mangoldtSum n x‖ < M := by
    intro x hnx hx6
    exact hlarge x hnx hx6
  obtain ⟨hphaseTwo, hphaseOne⟩ :=
    degreeThree_phase_bounds_of_forall_lt n M hsmall
  have hupper := degreeThree_section7_upper_of_data n hn hsq M aPlus aMinus
    hplus hminus hcoeffPlus hcoeffMinus hphaseTwo hphaseOne hM
  linarith

/-- The fully numerical Section 7 conclusion at the global analytic cutoff,
conditional only on the four finite order-three majorant certificates. -/
lemma exists_large_mangoldtSum_at_cutoff_of_degreeThree_data
    (n : ℕ) (hn : 2 ^ 1728 ≤ n)
    (hsq : Squarefree (Nat.choose (n + n) n))
    (aPlus aMinus : ℤ → ℂ)
    (hplus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      Sawtooth.psi (33 / 200) aPlus)
    (hminus : Sawtooth.IsUpperMajorant (Sawtooth.frequencies 3)
      (fun x => -Sawtooth.psi x) (33 / 200) aMinus)
    (hcoeffPlus : (∑ r ∈ Sawtooth.frequencies 3, ‖aPlus r‖) ≤ 3 / 4)
    (hcoeffMinus : (∑ r ∈ Sawtooth.frequencies 3, ‖aMinus r‖) ≤ 3 / 4) :
    ∃ x : ℝ, (n : ℝ) ≤ x ∧ x ≤ 6 * n ∧
      (1 / 5000 : ℝ) * Real.sqrt n ≤ ‖mangoldtSum n x‖ := by
  have hnpos : 0 < n := (by positivity : 0 < 2 ^ 1728).trans_le hn
  have hnumeric := ExplicitChebyshev.sqrtInterval_mangoldt_degree_three_450 n hn
  rw [← squareRootInterval_eq_Ioc] at hnumeric
  have hnumeric' :
      (1 / 5000 : ℝ) * Real.sqrt n <
        ((∑ d ∈ I n, ArithmeticFunction.vonMangoldt d) -
          100 * Real.log (2 * n)) / 450 := by
    convert hnumeric using 1
    ring
  apply exists_large_mangoldtSum_of_degreeThree_data n hnpos hsq
    ((1 / 5000 : ℝ) * Real.sqrt n) aPlus aMinus
    hplus hminus hcoeffPlus hcoeffMinus
  · positivity
  · exact hnumeric'

/-- Unconditional Section 7 lower bound.  Under squarefreeness of the
central binomial coefficient, one of the six reciprocal frequencies in
`[n,6n]` has von Mangoldt exponential sum at least `sqrt n / 5000`. -/
theorem exists_large_reciprocal_mangoldt_sum (n : ℕ)
    (hn : 2 ^ 1728 ≤ n)
    (hsq : Squarefree (Nat.choose (2 * n) n)) :
    ∃ x : ℝ, (n : ℝ) ≤ x ∧ x ≤ 6 * n ∧
      (1 / 5000 : ℝ) * Real.sqrt n ≤ ‖mangoldtSum n x‖ := by
  have hsq' : Squarefree (Nat.choose (n + n) n) := by
    simpa [two_mul] using hsq
  exact exists_large_mangoldtSum_at_cutoff_of_degreeThree_data n hn hsq'
    VaalerDegreeTen.degreeThreePlusCoefficient
    VaalerDegreeTen.degreeThreeMinusCoefficient
    VaalerDegreeTen.degreeThreePlus_majorant
    VaalerDegreeTen.degreeThreeMinus_majorant
    VaalerDegreeTen.sum_norm_degreeThreePlusCoefficient_le
    VaalerDegreeTen.sum_norm_degreeThreeMinusCoefficient_le

end Erdos175.Section7
