import ErdosProblems.Erdos1002.RamanujanSums
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact identities for Ramanujan sums

The main results of this file are the divisor--Möbius formula and complete
period orthogonality.  All sums remain finite.  The analytic estimates later
in the proof can therefore use these identities without importing any
convergence assertion.
-/

open scoped ArithmeticFunction.Moebius BigOperators ComplexConjugate FourierTransform

namespace Erdos1002

noncomputable section

/-- The complete additive-character sum modulo `q`, without the coprimality
restriction. -/
def completeCharacterSum (q n : ℕ) : ℂ :=
  ∑ a ∈ Finset.range q, ramanujanPhase q a (n : ℤ)

private theorem phase_nat_eq_pow {q n : ℕ} (a : ℕ) :
    ramanujanPhase q a (n : ℤ) =
      (Real.fourierChar ((n : ℝ) / (q : ℝ)) : ℂ) ^ a := by
  rw [ramanujanPhase]
  push_cast
  change (Real.fourierChar (((a : ℝ) * n) / q) : ℂ) = _
  rw [show ((a : ℝ) * n) / q = a • ((n : ℝ) / q) by simp [nsmul_eq_mul]; ring]
  rw [AddChar.map_nsmul_eq_pow]
  rfl

private theorem fourierChar_nat_div_pow {q n : ℕ} (hq : q ≠ 0) :
    (Real.fourierChar ((n : ℝ) / (q : ℝ)) : ℂ) ^ q = 1 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [← phase_nat_eq_pow (q := q) (n := n) q, ramanujanPhase]
  have harg :
      (((((q : ℤ) * (n : ℤ) : ℤ) : ℝ) / (q : ℝ))) = (n : ℝ) := by
    push_cast
    field_simp
  rw [harg]
  exact fourierChar_int (n : ℤ)

private theorem fourierChar_nat_div_eq_one_iff {q n : ℕ} (hq : q ≠ 0) :
    Real.fourierChar ((n : ℝ) / (q : ℝ)) = 1 ↔ q ∣ n := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  constructor
  · rintro ⟨z, hz⟩
    have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hratio : (n : ℝ) / (q : ℝ) = (z : ℝ) := by
      apply mul_left_cancel₀ htwoPi
      simpa [mul_assoc, mul_left_comm, mul_comm] using! hz
    have hzReal : (0 : ℝ) ≤ (z : ℝ) := by
      rw [← hratio]
      positivity
    have hzInt : (0 : ℤ) ≤ z := by exact_mod_cast hzReal
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hzInt
    have hratio' : (n : ℝ) / (q : ℝ) = (k : ℝ) := by simpa using! hratio
    refine ⟨k, ?_⟩
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    have : (n : ℝ) = (q : ℝ) * k := by
      calc
        (n : ℝ) = (q : ℝ) * ((n : ℝ) / (q : ℝ)) := by field_simp
        _ = (q : ℝ) * k := by rw [hratio']
    exact_mod_cast this
  · rintro ⟨k, rfl⟩
    refine ⟨(k : ℤ), ?_⟩
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    push_cast
    field_simp

/-- Orthogonality of a complete additive character modulo a positive
integer. -/
theorem completeCharacterSum_eq (q n : ℕ) (hq : q ≠ 0) :
    completeCharacterSum q n = if q ∣ n then (q : ℂ) else 0 := by
  let ζ : ℂ := (Real.fourierChar ((n : ℝ) / (q : ℝ)) : ℂ)
  have hpow : ζ ^ q = 1 := fourierChar_nat_div_pow hq
  have hrewrite : completeCharacterSum q n = ∑ a ∈ Finset.range q, ζ ^ a := by
    simp_rw [completeCharacterSum, ζ, phase_nat_eq_pow]
  rw [hrewrite]
  split_ifs with hdvd
  · have hζ : ζ = 1 := by
      dsimp [ζ]
      exact congrArg (fun z : Circle ↦ (z : ℂ))
        ((fourierChar_nat_div_eq_one_iff hq).2 hdvd)
    simp [hζ]
  · have hζ : ζ ≠ 1 := by
      intro h
      apply hdvd
      apply (fourierChar_nat_div_eq_one_iff hq).1
      apply Subtype.ext
      exact h
    apply (mul_right_cancel₀ (sub_ne_zero.mpr hζ))
    rw [zero_mul, geom_sum_mul, hpow, sub_self]

/-- The sum of the Möbius function over the divisors of a positive integer
is the Kronecker delta at one. -/
theorem sum_moebius_divisors (m : ℕ) :
    (∑ d ∈ m.divisors, ArithmeticFunction.moebius d) = if m = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  rw [ArithmeticFunction.coe_zeta_mul_moebius]
  rfl

/-- Möbius inversion detects coprimality through the gcd. -/
theorem sum_moebius_gcd (a q : ℕ) :
    (∑ d ∈ (Nat.gcd a q).divisors, ArithmeticFunction.moebius d) =
      if Nat.Coprime a q then 1 else 0 := by
  rw [sum_moebius_divisors]

private theorem gcd_divisors_eq_filter (a : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (Nat.gcd a q).divisors = {d ∈ q.divisors | d ∣ a} := by
  ext d
  have hgcd : Nat.gcd a q ≠ 0 :=
    (Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hq)).ne'
  simp [Nat.mem_divisors, hq, hgcd, Nat.dvd_gcd_iff, and_comm]

private theorem phase_mul_divisor {q d b n : ℕ} (hq : q ≠ 0) (hd : d ∣ q) :
    ramanujanPhase q (d * b) (n : ℤ) = ramanujanPhase (q / d) b (n : ℤ) := by
  have hd0 : d ≠ 0 := by
    intro hdZero
    subst d
    simp at hd
    exact hq hd
  have hfac : d * (q / d) = q := Nat.mul_div_cancel' hd
  have hquot0 : q / d ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfac
    exact hq hfac.symm
  have hfacR : (q : ℝ) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by exact_mod_cast hfac.symm
  have harg :
      (((((d * b : ℕ) : ℤ) * (n : ℤ) : ℤ) : ℝ) / (q : ℝ)) =
        (((((b : ℕ) : ℤ) * (n : ℤ) : ℤ) : ℝ) /
          ((q / d : ℕ) : ℝ)) := by
    push_cast
    rw [hfacR]
    field_simp
  rw [ramanujanPhase, ramanujanPhase, harg]

private theorem sum_phase_multiples_eq_complete {q d n : ℕ} (hq : q ≠ 0)
    (hd : d ∈ q.divisors) :
    (∑ a ∈ (Finset.range q).filter (fun a ↦ d ∣ a), ramanujanPhase q a (n : ℤ)) =
      completeCharacterSum (q / d) n := by
  have hdDvd : d ∣ q := Nat.dvd_of_mem_divisors hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  unfold completeCharacterSum
  refine Finset.sum_bij (fun a _ ↦ a / d) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_range]
    exact (Nat.div_lt_div_right hd0 ha.2 hdDvd).2 (Finset.mem_range.mp ha.1)
  · intro a₁ ha₁ a₂ ha₂ heq
    have hd₁ : d ∣ a₁ := (Finset.mem_filter.mp ha₁).2
    have hd₂ : d ∣ a₂ := (Finset.mem_filter.mp ha₂).2
    calc
      a₁ = d * (a₁ / d) := (Nat.mul_div_cancel' hd₁).symm
      _ = d * (a₂ / d) := by
        simpa using! congrArg (fun x ↦ d * x) heq
      _ = a₂ := Nat.mul_div_cancel' hd₂
  · intro b hb
    have hbLt : b < q / d := Finset.mem_range.mp hb
    refine ⟨d * b, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_range.2 ?_, dvd_mul_right d b⟩
      calc
        d * b < d * (q / d) := (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hd0)).2 hbLt
        _ = q := Nat.mul_div_cancel' hdDvd
    · simp [hd0]
  · intro a ha
    have hdA : d ∣ a := (Finset.mem_filter.mp ha).2
    simpa [Nat.mul_div_cancel' hdA] using!
      (phase_mul_divisor (q := q) (d := d) (b := a / d) (n := n) hq hdDvd)

private theorem sum_moebius_dvd_indicator (a : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (∑ d ∈ q.divisors, if d ∣ a then ArithmeticFunction.moebius d else 0) =
      if Nat.Coprime a q then 1 else 0 := by
  rw [← Finset.sum_filter]
  rw [← gcd_divisors_eq_filter a hq]
  exact sum_moebius_gcd a q

private theorem sum_moebius_dvd_indicator_complex (a : ℕ) {q : ℕ} (hq : q ≠ 0) :
    (∑ d ∈ q.divisors,
      if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if Nat.Coprime a q then 1 else 0 := by
  exact_mod_cast sum_moebius_dvd_indicator a hq

private theorem weighted_phase_sum_eq {q d n : ℕ} (hq : q ≠ 0)
    (hd : d ∈ q.divisors) :
    (∑ a ∈ Finset.range q,
      (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
        ramanujanPhase q a (n : ℤ)) =
      (ArithmeticFunction.moebius d : ℂ) * completeCharacterSum (q / d) n := by
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [← Finset.mul_sum]
  rw [sum_phase_multiples_eq_complete hq hd]

/-- First form of the divisor formula, before applying the divisor involution
`d ↦ q / d`. -/
theorem ramanujanSum_nat_eq_sum_divisors (q n : ℕ) (hq : q ≠ 0) :
    ramanujanSum q (n : ℤ) =
      ∑ d ∈ q.divisors,
        (ArithmeticFunction.moebius d : ℂ) *
          (if q / d ∣ n then (q / d : ℕ) else 0) := by
  calc
    ramanujanSum q (n : ℤ) =
        ∑ a ∈ Finset.range q,
          if Nat.Coprime a q then ramanujanPhase q a (n : ℤ) else 0 := by
      simp [ramanujanSum, reducedResidues, Finset.sum_filter]
    _ = ∑ a ∈ Finset.range q,
          (if Nat.Coprime a q then (1 : ℂ) else 0) * ramanujanPhase q a (n : ℤ) := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = ∑ a ∈ Finset.range q,
          (∑ d ∈ q.divisors,
            if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
              ramanujanPhase q a (n : ℤ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sum_moebius_dvd_indicator_complex a hq]
    _ = ∑ a ∈ Finset.range q, ∑ d ∈ q.divisors,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
            ramanujanPhase q a (n : ℤ) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_mul]
    _ = ∑ d ∈ q.divisors, ∑ a ∈ Finset.range q,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) *
            ramanujanPhase q a (n : ℤ) := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ q.divisors,
          (ArithmeticFunction.moebius d : ℂ) * completeCharacterSum (q / d) n := by
      apply Finset.sum_congr rfl
      intro d hd
      exact weighted_phase_sum_eq hq hd
    _ = ∑ d ∈ q.divisors,
          (ArithmeticFunction.moebius d : ℂ) *
            (if q / d ∣ n then (q / d : ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hquot : q / d ≠ 0 := by
        intro hzero
        have hfac : d * (q / d) = q := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
        rw [hzero, mul_zero] at hfac
        exact hq hfac.symm
      rw [completeCharacterSum_eq (q / d) n hquot]
      split_ifs <;> simp

/-- The standard divisor--Möbius formula at a nonnegative frequency. -/
theorem ramanujanSum_nat_divisor_moebius (q n : ℕ) (hq : q ≠ 0) :
    ramanujanSum q (n : ℤ) =
      ∑ d ∈ (Nat.gcd q n).divisors,
        (d : ℂ) * (ArithmeticFunction.moebius (q / d) : ℂ) := by
  rw [ramanujanSum_nat_eq_sum_divisors q n hq]
  calc
    (∑ d ∈ q.divisors,
        (ArithmeticFunction.moebius d : ℂ) *
          (if q / d ∣ n then (q / d : ℕ) else 0)) =
        ∑ e ∈ q.divisors,
          (ArithmeticFunction.moebius (q / e) : ℂ) *
            (if e ∣ n then e else 0) := by
      rw [← Nat.sum_divisorsAntidiagonal
        (fun d e ↦ (ArithmeticFunction.moebius d : ℂ) *
          (if e ∣ n then (e : ℕ) else 0))]
      simpa using! (Nat.sum_divisorsAntidiagonal'
        (fun d e ↦ (ArithmeticFunction.moebius d : ℂ) *
          ((if e ∣ n then e else 0 : ℕ) : ℂ)) (n := q))
    _ = ∑ e ∈ (Finset.filter (fun e ↦ e ∣ n) q.divisors),
          (ArithmeticFunction.moebius (q / e) : ℂ) * (e : ℂ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    _ = ∑ e ∈ (Nat.gcd q n).divisors,
          (ArithmeticFunction.moebius (q / e) : ℂ) * (e : ℂ) := by
      rw [← gcd_divisors_eq_filter n hq, Nat.gcd_comm n q]
    _ = ∑ e ∈ (Nat.gcd q n).divisors,
          (e : ℂ) * (ArithmeticFunction.moebius (q / e) : ℂ) := by
      apply Finset.sum_congr rfl
      intro e _
      ring

/-- The exact divisor--Möbius formula for an arbitrary integer frequency and
a positive modulus.  The `natAbs` is precisely the natural-number meaning of
`d ∣ (q,n)` when the frequency may be negative. -/
theorem ramanujanSum_divisor_moebius {q : ℕ} (n : ℤ) (hq : q ≠ 0) :
    ramanujanSum q n =
      ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
        (d : ℂ) * (ArithmeticFunction.moebius (q / d) : ℂ) := by
  cases n with
  | ofNat n =>
      simpa using! ramanujanSum_nat_divisor_moebius q n hq
  | negSucc n =>
      calc
        ramanujanSum q (Int.negSucc n) = ramanujanSum q ((n + 1 : ℕ) : ℤ) := by
          rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega]
          exact ramanujanSum_even q ((n + 1 : ℕ) : ℤ)
        _ = ∑ d ∈ (Nat.gcd q (n + 1)).divisors,
              (d : ℂ) * (ArithmeticFunction.moebius (q / d) : ℂ) :=
          ramanujanSum_nat_divisor_moebius q (n + 1) hq
        _ = ∑ d ∈ (Nat.gcd q (Int.negSucc n).natAbs).divisors,
              (d : ℂ) * (ArithmeticFunction.moebius (q / d) : ℂ) := by simp

/-- With this development's explicit empty-sum convention at modulus zero,
the same displayed divisor formula also remains true for `q = 0`.  The paper
only invokes the positive-modulus specialization above. -/
theorem ramanujanSum_divisor_moebius_all (q : ℕ) (n : ℤ) :
    ramanujanSum q n =
      ∑ d ∈ (Nat.gcd q n.natAbs).divisors,
        (d : ℂ) * (ArithmeticFunction.moebius (q / d) : ℂ) := by
  by_cases hq : q = 0
  · subst q
    simp
  · exact ramanujanSum_divisor_moebius n hq

/-- Complete additive-character sum with an integer, rather than natural,
frequency. -/
def completeCharacterSumInt (q : ℕ) (r : ℤ) : ℂ :=
  ∑ a ∈ Finset.range q, ramanujanPhase q a r

/-- Integer-frequency form of complete character orthogonality. -/
theorem completeCharacterSumInt_eq {q : ℕ} (r : ℤ) (hq : q ≠ 0) :
    completeCharacterSumInt q r =
      if q ∣ r.natAbs then (q : ℂ) else 0 := by
  cases r with
  | ofNat n =>
      simpa [completeCharacterSumInt, completeCharacterSum] using!
        completeCharacterSum_eq q n hq
  | negSucc n =>
      have hneg : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
      rw [completeCharacterSumInt, hneg]
      simp_rw [ramanujanPhase_neg]
      rw [← map_sum]
      rw [show (∑ a ∈ Finset.range q, ramanujanPhase q a ((n + 1 : ℕ) : ℤ)) =
          completeCharacterSum q (n + 1) by rfl]
      rw [completeCharacterSum_eq q (n + 1) hq]
      simp only [Int.natAbs_neg, Int.natAbs_natCast]
      split_ifs <;> simp

/-- Integer numerator of the difference between two reduced rational
frequencies, expressed over their least common multiple. -/
def crossNumerator (p p' a b : ℕ) : ℤ :=
  (a * (Nat.lcm p p' / p) : ℕ) - (b * (Nat.lcm p p' / p') : ℕ)

private theorem phase_mul_conj_eq_phase_lcm {p p' a b n : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) :
    ramanujanPhase p a (n : ℤ) * conj (ramanujanPhase p' b (n : ℤ)) =
      ramanujanPhase (Nat.lcm p p') n (crossNumerator p p' a b) := by
  let L := Nat.lcm p p'
  have hL : L ≠ 0 := Nat.lcm_ne_zero hp hp'
  have hpDvd : p ∣ L := Nat.dvd_lcm_left p p'
  have hp'Dvd : p' ∣ L := Nat.dvd_lcm_right p p'
  have hfacP : p * (L / p) = L := Nat.mul_div_cancel' hpDvd
  have hfacP' : p' * (L / p') = L := Nat.mul_div_cancel' hp'Dvd
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hp'R : (p' : ℝ) ≠ 0 := by exact_mod_cast hp'
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have hratioP : (((L / p : ℕ) : ℝ) / (L : ℝ)) = 1 / (p : ℝ) := by
    field_simp
    exact_mod_cast (by simpa [mul_comm] using! hfacP)
  have hratioP' : (((L / p' : ℕ) : ℝ) / (L : ℝ)) = 1 / (p' : ℝ) := by
    field_simp
    exact_mod_cast (by simpa [mul_comm] using! hfacP')
  have harg :
      (((((a : ℕ) : ℤ) * (n : ℤ) : ℤ) : ℝ) / (p : ℝ)) +
        (((((b : ℕ) : ℤ) * (-(n : ℤ)) : ℤ) : ℝ) / (p' : ℝ)) =
      (((((n : ℕ) : ℤ) * crossNumerator p p' a b : ℤ) : ℝ) / (L : ℝ)) := by
    dsimp [crossNumerator, L]
    push_cast
    calc
      (a : ℝ) * n / p + (b : ℝ) * -n / p' =
          (a : ℝ) * n * (1 / p) - (b : ℝ) * n * (1 / p') := by ring
      _ = (a : ℝ) * n * (((L / p : ℕ) : ℝ) / L) -
          (b : ℝ) * n * (((L / p' : ℕ) : ℝ) / L) := by
            rw [hratioP, hratioP']
      _ = (n : ℝ) * ((a : ℝ) * (L / p : ℕ) - (b : ℝ) * (L / p' : ℕ)) / L := by
            ring
  rw [← ramanujanPhase_neg p' b (n : ℤ)]
  rw [ramanujanPhase, ramanujanPhase, ramanujanPhase]
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, harg]

private theorem lcm_dvd_crossNumerator_iff {p p' a b : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0)
    (ha : a ∈ reducedResidues p) (hb : b ∈ reducedResidues p') :
    Nat.lcm p p' ∣ (crossNumerator p p' a b).natAbs ↔ p = p' ∧ a = b := by
  let L := Nat.lcm p p'
  have hL : L ≠ 0 := Nat.lcm_ne_zero hp hp'
  have hpDvd : p ∣ L := Nat.dvd_lcm_left p p'
  have hp'Dvd : p' ∣ L := Nat.dvd_lcm_right p p'
  have hfacP : p * (L / p) = L := Nat.mul_div_cancel' hpDvd
  have hfacP' : p' * (L / p') = L := Nat.mul_div_cancel' hp'Dvd
  have hquotP : 0 < L / p := by
    by_contra h
    have hz : L / p = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at hfacP
    exact hL hfacP.symm
  have hquotP' : 0 < L / p' := by
    by_contra h
    have hz : L / p' = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at hfacP'
    exact hL hfacP'.symm
  have haData := Finset.mem_filter.mp ha
  have hbData := Finset.mem_filter.mp hb
  have haLt : a < p := Finset.mem_range.mp haData.1
  have hbLt : b < p' := Finset.mem_range.mp hbData.1
  have haCoprime : Nat.Coprime a p := haData.2
  have hbCoprime : Nat.Coprime b p' := hbData.2
  have hALt : a * (L / p) < L := by
    calc
      a * (L / p) < p * (L / p) := (Nat.mul_lt_mul_right hquotP).2 haLt
      _ = L := hfacP
  have hBLt : b * (L / p') < L := by
    calc
      b * (L / p') < p' * (L / p') := (Nat.mul_lt_mul_right hquotP').2 hbLt
      _ = L := hfacP'
  constructor
  · intro hdiv
    have habsLt : (crossNumerator p p' a b).natAbs < L := by
      simpa [crossNumerator, L] using!
        (Int.natAbs_coe_sub_coe_lt_of_lt hALt hBLt)
    have habsZero : (crossNumerator p p' a b).natAbs = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdiv habsLt
    have hnumZero : crossNumerator p p' a b = 0 := Int.natAbs_eq_zero.mp habsZero
    have hABInt :
        ((a * (L / p) : ℕ) : ℤ) = ((b * (L / p') : ℕ) : ℤ) := by
      apply sub_eq_zero.mp
      simpa [crossNumerator, L] using! hnumZero
    have hAB : a * (L / p) = b * (L / p') := by exact_mod_cast hABInt
    have hscaled := congrArg (fun x : ℕ ↦ x * p * p') hAB
    have hleft : (a * (L / p)) * p * p' = (a * p') * L := by
      calc
        (a * (L / p)) * p * p' = (a * p') * (p * (L / p)) := by ring
        _ = (a * p') * L := by rw [hfacP]
    have hright : (b * (L / p')) * p * p' = (b * p) * L := by
      calc
        (b * (L / p')) * p * p' = (b * p) * (p' * (L / p')) := by ring
        _ = (b * p) * L := by rw [hfacP']
    change (a * (L / p)) * p * p' = (b * (L / p')) * p * p' at hscaled
    rw [hleft, hright] at hscaled
    have hcross : a * p' = b * p :=
      Nat.mul_right_cancel (Nat.pos_of_ne_zero hL) hscaled
    have hpDivP' : p ∣ p' := by
      apply haCoprime.symm.dvd_of_dvd_mul_left
      refine ⟨b, ?_⟩
      simpa [mul_comm] using! hcross
    have hp'DivP : p' ∣ p := by
      apply hbCoprime.symm.dvd_of_dvd_mul_left
      refine ⟨a, ?_⟩
      simpa [mul_comm] using! hcross.symm
    have hpp' : p = p' := Nat.dvd_antisymm hpDivP' hp'DivP
    subst p'
    exact ⟨rfl, Nat.mul_right_cancel (Nat.pos_of_ne_zero hp) hcross⟩
  · rintro ⟨rfl, rfl⟩
    simp [crossNumerator, hp]

/-- Complete-period Hermitian orthogonality.  Since Ramanujan sums are real,
the conjugate can subsequently be removed. -/
theorem ramanujan_complete_period_inner_product (p p' : ℕ)
    (hp : p ≠ 0) (hp' : p' ≠ 0) :
    (∑ n ∈ Finset.range (Nat.lcm p p'),
      ramanujanSum p (n : ℤ) * conj (ramanujanSum p' (n : ℤ))) =
      if p = p' then ((p * Nat.totient p : ℕ) : ℂ) else 0 := by
  let L := Nat.lcm p p'
  have hL : L ≠ 0 := Nat.lcm_ne_zero hp hp'
  calc
    (∑ n ∈ Finset.range L,
        ramanujanSum p (n : ℤ) * conj (ramanujanSum p' (n : ℤ))) =
        ∑ n ∈ Finset.range L, ∑ a ∈ reducedResidues p, ∑ b ∈ reducedResidues p',
          ramanujanPhase p a (n : ℤ) * conj (ramanujanPhase p' b (n : ℤ)) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [ramanujanSum, ramanujanSum, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    _ = ∑ a ∈ reducedResidues p, ∑ b ∈ reducedResidues p', ∑ n ∈ Finset.range L,
          ramanujanPhase p a (n : ℤ) * conj (ramanujanPhase p' b (n : ℤ)) := by
      rw [Finset.sum_comm (s := Finset.range L) (t := reducedResidues p)]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm (s := Finset.range L) (t := reducedResidues p')]
    _ = ∑ a ∈ reducedResidues p, ∑ b ∈ reducedResidues p',
          completeCharacterSumInt L (crossNumerator p p' a b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      unfold completeCharacterSumInt
      apply Finset.sum_congr rfl
      intro n _
      exact phase_mul_conj_eq_phase_lcm hp hp'
    _ = ∑ a ∈ reducedResidues p, ∑ b ∈ reducedResidues p',
          (if L ∣ (crossNumerator p p' a b).natAbs then (L : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact completeCharacterSumInt_eq (crossNumerator p p' a b) hL
    _ = ∑ a ∈ reducedResidues p, ∑ b ∈ reducedResidues p',
          (if p = p' ∧ a = b then (L : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hiff : L ∣ (crossNumerator p p' a b).natAbs ↔ p = p' ∧ a = b := by
        exact lcm_dvd_crossNumerator_iff hp hp' ha hb
      by_cases hsame : p = p' ∧ a = b
      · have hdvd := hiff.2 hsame
        rw [if_pos hdvd, if_pos hsame]
      · have hnotdvd : ¬L ∣ (crossNumerator p p' a b).natAbs := fun h ↦ hsame (hiff.1 h)
        rw [if_neg hnotdvd, if_neg hsame]
    _ = if p = p' then ((p * Nat.totient p : ℕ) : ℂ) else 0 := by
      by_cases hpp : p = p'
      · subst p'
        simp [L, card_reducedResidues]
        ring
      · simp [hpp]

/-- Off-diagonal complete-period orthogonality, in the real product form used
in the manuscript. -/
theorem ramanujan_complete_period_orthogonality {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    (∑ n ∈ Finset.range (Nat.lcm p p'),
      ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) = 0 := by
  calc
    (∑ n ∈ Finset.range (Nat.lcm p p'),
        ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) =
      ∑ n ∈ Finset.range (Nat.lcm p p'),
        ramanujanSum p (n : ℤ) * conj (ramanujanSum p' (n : ℤ)) := by
      apply Finset.sum_congr rfl
      intro n _
      rw [conj_ramanujanSum]
    _ = 0 := by
      rw [ramanujan_complete_period_inner_product p p' hp hp']
      simp [hpp']

/-- Diagonal complete-period identity
`∑_{n mod p} c_p(n)^2 = p φ(p)`. -/
theorem ramanujan_complete_period_square (p : ℕ) (hp : p ≠ 0) :
    (∑ n ∈ Finset.range p, (ramanujanSum p (n : ℤ)) ^ 2) =
      ((p * Nat.totient p : ℕ) : ℂ) := by
  calc
    (∑ n ∈ Finset.range p, (ramanujanSum p (n : ℤ)) ^ 2) =
      ∑ n ∈ Finset.range (Nat.lcm p p),
        ramanujanSum p (n : ℤ) * conj (ramanujanSum p (n : ℤ)) := by
      simp only [Nat.lcm_self, pow_two, conj_ramanujanSum]
    _ = ((p * Nat.totient p : ℕ) : ℂ) := by
      rw [ramanujan_complete_period_inner_product p p hp hp]
      simp

end

end Erdos1002
