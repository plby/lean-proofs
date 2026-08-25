/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-5.4 Pro
-/
import BoundedGaps.BombieriVinogradov.Analytic.SiegelZeroFreeRegion
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaConvolutionSquare
import ErdosProblems.Erdos587.NVDevelopment
import ErdosProblems.Erdos1141
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Erdős Problem 1140: elementary and Siegel-theorem foundations

For a positive natural number `n`, put `Good n` when every number
`n - 2 * x^2` occurring before the first nonpositive value is prime.  The
problem asks whether infinitely many such `n` exist.  The answer is no.

This foundation module contains the elementary reduction and the axiom-clean
Siegel lower bound.  The Burgess/hyperbola argument is developed in
`ErdosProblems.Erdos1140.Erdos1140Analytic`; no conditional theorem from
`ErdosProblems.Erdos1141` is used.
-/

namespace Erdos1140

/-- The exact prime-value property in Erdős Problem 1140.  Positivity is
included because the problem and its cited sources concern positive
integers; without it, `0` would satisfy the universal clause vacuously. -/
def Good (n : ℕ) : Prop :=
  0 < n ∧ ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

/-- The congruence needed to turn a modulus into a divisor of one of the
values in the problem. -/
def Solvable2X2EqNMod (n p : ℕ) : Prop :=
  ∃ x : ℕ, Nat.ModEq p (2 * x ^ 2) n

/-- Taking `x = 0` shows that every good number is itself prime. -/
lemma prime_of_good {n : ℕ} (hn : Good n) : Nat.Prime n := by
  simpa using hn.2 0 (by simpa using hn.1)

/-- A proper prime divisor of one of the required values contradicts
`Good`. -/
lemma not_good_of_prime_dvd_value {n x p : ℕ}
    (hx : 2 * x ^ 2 < n) (hp : Nat.Prime p)
    (hpdvd : p ∣ n - 2 * x ^ 2) (hlt : p < n - 2 * x ^ 2) :
    ¬ Good n := by
  intro hn
  have hvalue := hn.2 x hx
  rcases (Nat.dvd_prime hvalue).mp hpdvd with hpone | hpeq
  · exact hp.ne_one hpone
  · omega

/-- A sufficiently small prime modulus on which `2*x^2 ≡ n` is solvable
contradicts `Good n`.  Reducing the root modulo `p` supplies an admissible
index, and the corresponding prime value has `p` as a proper divisor. -/
lemma not_solvable2X2EqNMod_of_good {n p : ℕ} (hn : Good n)
    (hp : Nat.Prime p) (hpsmall : 2 * p ^ 2 + p < n) :
    ¬ Solvable2X2EqNMod n p := by
  rintro ⟨x, hx⟩
  let y := x % p
  have hpPos : 0 < p := hp.pos
  have hylt : y < p := by
    dsimp [y]
    exact Nat.mod_lt x hpPos
  have hyx : Nat.ModEq p y x := Nat.mod_modEq x p
  have hmod : Nat.ModEq p (2 * y ^ 2) n := by
    exact ((hyx.pow 2).mul_left 2).trans hx
  have hysq : y ^ 2 < p ^ 2 := Nat.pow_lt_pow_left hylt (by decide)
  have hybound : 2 * y ^ 2 < n := by nlinarith
  have hpvalue : p < n - 2 * y ^ 2 := by
    have : 2 * y ^ 2 + p < n := by nlinarith
    omega
  have hpdvd : p ∣ n - 2 * y ^ 2 := by
    exact (Nat.modEq_iff_dvd' hybound.le).mp hmod
  exact not_good_of_prime_dvd_value hybound hp hpdvd hpvalue hn

/-- Once the analytic argument supplies an eventually small prime solution
to `2*x^2 ≡ n`, the desired finiteness is purely elementary. -/
theorem finite_good_of_eventually_small_solvable_prime
    (hsmall : ∀ᶠ n : ℕ in Filter.atTop,
      Nat.Prime n → ∃ p : ℕ, Nat.Prime p ∧ 2 * p ^ 2 + p < n ∧
        Solvable2X2EqNMod n p) :
    Set.Finite {n : ℕ | Good n} := by
  rw [Filter.eventually_atTop] at hsmall
  obtain ⟨N, hN⟩ := hsmall
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  change Good n at hn
  change n < N
  by_contra hnlt
  obtain ⟨p, hp, hpbound, hsolvable⟩ :=
    hN n (le_of_not_gt hnlt) (prime_of_good hn)
  exact not_solvable2X2EqNMod_of_good hn hp hpbound hsolvable

/-- The eight values recorded on the Erdős Problems page really do have the
required property.  This finite verification is independent of the
finiteness argument. -/
theorem known_examples :
    ∀ n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Finset ℕ), Good n := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · norm_num
    · intro x hx
      have hxsmall : x < 10 := by nlinarith
      interval_cases x <;> norm_num at hx
      all_goals norm_num

/-! ## An elementary normal form for every good number -/

/-- Write `n` just beyond the last value `2*m^2`.  The remainder of a
good number cannot lie in the first half of the resulting interval: reflecting
`m` modulo that remainder would make another required prime value factor. -/
lemma twice_lt_last_remainder {n m r : ℕ} (hn : Good n)
    (hdecomp : n = 2 * m ^ 2 + r) (hrpos : 0 < r) :
    2 * m < r := by
  have hmlt : 2 * m ^ 2 < n := by
    rw [hdecomp]
    omega
  have hrprime : Nat.Prime r := by
    have hp := hn.2 m hmlt
    have hvalue : n - 2 * m ^ 2 = r := by
      rw [hdecomp, Nat.add_sub_cancel_left]
    simpa [hvalue] using hp
  by_contra hnot
  have hrhalf : r ≤ 2 * m := by omega
  obtain ⟨x, hxm, hxsq⟩ :
      ∃ x : ℕ, x ≤ m ∧
        (x : ℤ) ^ 2 = ((m : ℤ) - (r : ℤ)) ^ 2 := by
    by_cases hrm : r ≤ m
    · refine ⟨m - r, by omega, ?_⟩
      rw [Nat.cast_sub hrm]
    · refine ⟨r - m, by omega, ?_⟩
      rw [Nat.cast_sub (by omega : m ≤ r)]
      ring
  have hfactor :
      n - 2 * x ^ 2 = r * (4 * m - 2 * r + 1) := by
    have hsub : 2 * x ^ 2 ≤ n := by
      rw [hdecomp]
      by_contra h
      have hcast : (n : ℤ) < (2 * x ^ 2 : ℕ) := by exact_mod_cast (by omega)
      push_cast at hcast
      rw [hxsq] at hcast
      nlinarith
    apply Nat.cast_injective (R := ℤ)
    rw [Nat.cast_sub hsub, hdecomp]
    push_cast
    rw [hxsq, Nat.cast_sub (by omega : 2 * r ≤ 4 * m)]
    push_cast
    ring
  have hsecondpos : 0 < 4 * m - 2 * r + 1 := by omega
  have hxlt : 2 * x ^ 2 < n := by
    rw [← Nat.sub_pos_iff_lt, hfactor]
    positivity
  have hp := hn.2 x hxlt
  rw [hfactor, Nat.prime_mul_iff] at hp
  rcases hp with ⟨_, hsecondOne⟩ | ⟨_, hrone⟩
  · have hremainder : r = 2 * m := by omega
    have hnprime := prime_of_good hn
    have hneven : Even n := by
      refine ⟨m ^ 2 + m, ?_⟩
      rw [hdecomp, hremainder]
      ring
    have hnTwo : n = 2 := (hnprime.even_iff.mp hneven)
    rw [hnTwo, hremainder] at hdecomp
    have hmpos : 0 < m := by omega
    nlinarith
  · exact hrprime.ne_one hrone

/-- If `n = 2*m^2 + 2*m + s` lies in the interval determined by the last
admissible square, then primality at the index reflected across `m` forces
`s` to be one of the two endpoints.  This is the elementary reduction to
the two quadratic families occurring in the classical class-number proof. -/
lemma offset_eq_one_or_top {n m s : ℕ} (hn : Good n)
    (hdecomp : n = 2 * m ^ 2 + 2 * m + s)
    (hspos : 0 < s) (hstop : s ≤ 2 * m + 1) :
    s = 1 ∨ s = 2 * m + 1 := by
  by_cases hsone : s = 1
  · exact Or.inl hsone
  right
  have hsTwo : 2 ≤ s := by omega
  by_contra hstopEq
  have hsTop : s ≤ 2 * m := by omega
  by_cases hsMid : s ≤ m + 1
  · let x := m + 1 - s
    have hxs : x + s = m + 1 := by
      dsimp [x]
      omega
    have hx : x ≤ m := by
      dsimp [x]
      omega
    have hfactor :
        n - 2 * x ^ 2 = (2 * s - 1) * (2 * m - s + 2) := by
      have hsub : 2 * x ^ 2 ≤ n := by
        rw [hdecomp]
        nlinarith [sq_nonneg (m - x)]
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hsub, hdecomp]
      push_cast
      have hxZ : (x : ℤ) = (m : ℤ) + 1 - (s : ℤ) := by
        omega
      have hleftZ : ((2 * s - 1 : ℕ) : ℤ) = 2 * (s : ℤ) - 1 := by
        omega
      rw [hxZ, hleftZ, Nat.cast_sub hsTop]
      push_cast
      ring
    have hxlt : 2 * x ^ 2 < n := by
      rw [hdecomp]
      dsimp [x]
      nlinarith
    have hp := hn.2 x hxlt
    rw [hfactor] at hp
    have hleft : 1 < 2 * s - 1 := by omega
    have hright : 1 < 2 * m - s + 2 := by omega
    rw [Nat.prime_mul_iff] at hp
    rcases hp with ⟨_, hrightOne⟩ | ⟨_, hleftOne⟩ <;> omega
  · let x := s - (m + 1)
    have hxs : x + (m + 1) = s := by
      dsimp [x]
      omega
    have hx : x ≤ m := by
      dsimp [x]
      omega
    have hfactor :
        n - 2 * x ^ 2 = (2 * s - 1) * (2 * m - s + 2) := by
      have hsub : 2 * x ^ 2 ≤ n := by
        rw [hdecomp]
        nlinarith [sq_nonneg (m - x)]
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_sub hsub, hdecomp]
      push_cast
      have hxZ : (x : ℤ) = (s : ℤ) - ((m : ℤ) + 1) := by
        omega
      have hleftZ : ((2 * s - 1 : ℕ) : ℤ) = 2 * (s : ℤ) - 1 := by
        omega
      rw [hxZ, hleftZ, Nat.cast_sub hsTop]
      push_cast
      ring
    have hxlt : 2 * x ^ 2 < n := by
      rw [hdecomp]
      dsimp [x]
      nlinarith
    have hp := hn.2 x hxlt
    rw [hfactor] at hp
    have hleft : 1 < 2 * s - 1 := by omega
    have hright : 1 < 2 * m - s + 2 := by omega
    rw [Nat.prime_mul_iff] at hp
    rcases hp with ⟨_, hrightOne⟩ | ⟨_, hleftOne⟩ <;> omega

/-- Combining the reflected-remainder argument with `offset_eq_one_or_top`
puts a good number in one of the two quadratic families, provided `m` is
the last admissible square index. -/
lemma normal_form_of_last_remainder {n m r : ℕ} (hn : Good n)
    (hdecomp : n = 2 * m ^ 2 + r) (hrpos : 0 < r)
    (hrtop : r ≤ 4 * m + 1) :
    n = 2 * m ^ 2 + 2 * m + 1 ∨
      n = 2 * (m + 1) ^ 2 - 1 := by
  have hrbottom : 2 * m < r :=
    twice_lt_last_remainder hn hdecomp hrpos
  let s := r - 2 * m
  have hrs : r = 2 * m + s := by
    dsimp [s]
    omega
  have hspos : 0 < s := by
    dsimp [s]
    omega
  have hstop : s ≤ 2 * m + 1 := by
    dsimp [s]
    omega
  have hdecomp' : n = 2 * m ^ 2 + 2 * m + s := by
    rw [hdecomp, hrs]
    omega
  rcases offset_eq_one_or_top hn hdecomp' hspos hstop with hs | hs
  · left
    simpa [hs] using hdecomp'
  · right
    rw [hdecomp', hs]
    have hid : 2 * (m + 1) ^ 2 = 2 * m ^ 2 + 4 * m + 2 := by ring
    rw [hid]
    omega

/-- Every good number other than `2` belongs to one of the two classical
quadratic families. -/
theorem good_eq_two_or_quadratic_family {n : ℕ} (hn : Good n) :
    n = 2 ∨ ∃ m : ℕ,
      n = 2 * m ^ 2 + 2 * m + 1 ∨
        n = 2 * (m + 1) ^ 2 - 1 := by
  by_cases hnTwo : n = 2
  · exact Or.inl hnTwo
  right
  have hnprime := prime_of_good hn
  obtain ⟨k, hk⟩ := hnprime.odd_of_ne_two hnTwo
  let m := Nat.sqrt k
  let r := n - 2 * m ^ 2
  have hmSq : m * m ≤ k := by
    simpa [m] using Nat.sqrt_le k
  have hkTop : k < (m + 1) * (m + 1) := by
    simpa [m] using Nat.lt_succ_sqrt k
  have hmBelow : 2 * m ^ 2 < n := by
    rw [hk]
    nlinarith
  have hrpos : 0 < r := by
    dsimp [r]
    omega
  have hdecomp : n = 2 * m ^ 2 + r := by
    dsimp [r]
    omega
  have hrtop : r ≤ 4 * m + 1 := by
    have hnTop : n ≤ 2 * m ^ 2 + (4 * m + 1) := by
      rw [hk]
      nlinarith
    omega
  exact ⟨m, normal_form_of_last_remainder hn hdecomp hrpos hrtop⟩


noncomputable section

open Complex MeasureTheory Metric Set Filter
open ArithmeticFunction
open scoped BigOperators ComplexOrder Real Topology

open BoundedGaps.Maynard

private lemma three_le_modulus_of_character_ne_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    3 ≤ q := by
  by_contra hq
  have hqPos : 0 < q := NeZero.pos q
  have hqNeOne : q ≠ 1 := fun h ↦ hchi (chi.level_one' h)
  have hqTwo : q = 2 := by omega
  subst q
  have hcard : Nat.card (DirichletCharacter ℂ 2) = 1 := by
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    norm_num
  exact hchi ((Nat.card_eq_one_iff_unique.mp hcard).1.elim chi 1)

private lemma one_lt_log_modulus
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    1 < Real.log (q : ℝ) := by
  have hqThree : (3 : ℝ) ≤ q := by
    exact_mod_cast three_le_modulus_of_character_ne_one chi hchi
  exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
    (Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) hqThree))

private lemma norm_first_order_remainder_right_le
    {f f' f'' : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b,
      HasDerivWithinAt f (f' t) (Icc a b) t)
    (hf' : ∀ t ∈ Icc a b,
      HasDerivWithinAt f' (f'' t) (Icc a b) t)
    (hbound : ∀ t ∈ Ico a b, ‖f'' t‖ ≤ M) :
    ‖f b - f a - ((b - a : ℝ) : ℂ) * f' a‖ ≤
      M * (b - a) ^ 2 := by
  have hvar : ∀ t ∈ Icc a b, ‖f' t - f' a‖ ≤ M * (t - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hf' hbound
  let g : ℝ → ℂ := fun t ↦ f t - ((t - a : ℝ) : ℂ) * f' a
  have hg : ∀ t ∈ Icc a b,
      HasDerivWithinAt g (f' t - f' a) (Icc a b) t := by
    intro t ht
    have hlinear : HasDerivAt
        (fun u : ℝ ↦ ((u - a : ℝ) : ℂ) * f' a) (f' a) t := by
      simpa only [id_eq, Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
        ((((hasDerivAt_id t).sub_const a).ofReal_comp).mul_const (f' a))
    change HasDerivWithinAt
      (fun u : ℝ ↦ f u - ((u - a : ℝ) : ℂ) * f' a)
        (f' t - f' a) (Icc a b) t
    exact (hf t ht).sub hlinear.hasDerivWithinAt
  have hgbound : ∀ t ∈ Ico a b,
      ‖f' t - f' a‖ ≤ M * (b - a) := by
    intro t ht
    exact (hvar t ⟨ht.1, ht.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) hM)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
    hg hgbound b (right_mem_Icc.mpr hab)
  dsimp [g] at hmean
  simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at hmean
  have heq :
      f b - ((b - a : ℝ) : ℂ) * f' a - f a =
        f b - f a - ((b - a : ℝ) : ℂ) * f' a := by ring
  rw [heq] at hmean
  simpa [g, pow_two, mul_assoc] using hmean

private lemma norm_first_order_remainder_left_le
    {f f' f'' : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b,
      HasDerivWithinAt f (f' t) (Icc a b) t)
    (hf' : ∀ t ∈ Icc a b,
      HasDerivWithinAt f' (f'' t) (Icc a b) t)
    (hbound : ∀ t ∈ Ico a b, ‖f'' t‖ ≤ M) :
    ‖f a - f b - ((a - b : ℝ) : ℂ) * f' b‖ ≤
      M * (b - a) ^ 2 := by
  have hvar : ∀ t ∈ Icc a b, ‖f' t - f' b‖ ≤ M * (b - t) := by
    intro t ht
    have hsub : Icc t b ⊆ Icc a b := by
      intro u hu
      exact ⟨ht.1.trans hu.1, hu.2⟩
    have hderiv : ∀ u ∈ Icc t b,
        HasDerivWithinAt f' (f'' u) (Icc t b) u := by
      intro u hu
      exact (hf' u (hsub hu)).mono hsub
    have hbd : ∀ u ∈ Ico t b, ‖f'' u‖ ≤ M := by
      intro u hu
      exact hbound u ⟨ht.1.trans hu.1, hu.2⟩
    have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
      hderiv hbd b (right_mem_Icc.mpr ht.2)
    simpa [norm_sub_rev] using hmean
  let g : ℝ → ℂ := fun t ↦ f t - ((t - b : ℝ) : ℂ) * f' b
  have hg : ∀ t ∈ Icc a b,
      HasDerivWithinAt g (f' t - f' b) (Icc a b) t := by
    intro t ht
    have hlinear : HasDerivAt
        (fun u : ℝ ↦ ((u - b : ℝ) : ℂ) * f' b) (f' b) t := by
      simpa only [id_eq, Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
        ((((hasDerivAt_id t).sub_const b).ofReal_comp).mul_const (f' b))
    change HasDerivWithinAt
      (fun u : ℝ ↦ f u - ((u - b : ℝ) : ℂ) * f' b)
        (f' t - f' b) (Icc a b) t
    exact (hf t ht).sub hlinear.hasDerivWithinAt
  have hgbound : ∀ t ∈ Ico a b,
      ‖f' t - f' b‖ ≤ M * (b - a) := by
    intro t ht
    exact (hvar t ⟨ht.1, ht.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 b) hM)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
    hg hgbound b (right_mem_Icc.mpr hab)
  rw [norm_sub_rev] at hmean
  dsimp [g] at hmean
  simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at hmean
  have heq :
      f a - ((a - b : ℝ) : ℂ) * f' b - f b =
        f a - f b - ((a - b : ℝ) : ℂ) * f' b := by ring
  rw [heq] at hmean
  simpa [g, pow_two, mul_assoc] using hmean

private lemma hasDerivAt_deriv_LFunction_ofReal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (sigma : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ deriv (DirichletCharacter.LFunction chi) (t : ℂ))
      (iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ))
      sigma := by
  have hdiff : Differentiable ℂ
      (deriv (DirichletCharacter.LFunction chi)) :=
    (DirichletCharacter.differentiable_LFunction hchi).deriv
  have h := (hdiff (sigma : ℂ)).hasDerivAt.comp_ofReal
  simpa [iteratedDeriv_succ'] using h

/-- A second-derivative version of the near-one Cauchy estimate. -/
theorem norm_iteratedDeriv_two_LFunction_ofReal_near_one_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma : ℝ}
    (hsigmaNear :
      1 - 1 / (4 * Real.log (q : ℝ)) ≤ sigma)
    (hsigmaUpper : sigma ≤ 3 / 2) :
    ‖iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      16384 * (Real.log (q : ℝ)) ^ 3 := by
  let L := Real.log (q : ℝ)
  let r := 1 / (16 * L)
  have hLone : 1 < L := one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hrPos : 0 < r := by positivity
  have hrLe : r ≤ 1 / 16 := by
    dsimp [r]
    rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
    nlinarith
  have hsigmaPos : 0 < sigma := by
    have hquarter : 1 / (4 * L) < 1 := by
      rw [div_lt_one (by positivity : 0 < 4 * L)]
      nlinarith
    change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
    linarith
  have hsphere : ∀ z ∈ sphere (sigma : ℂ) r,
      ‖DirichletCharacter.LFunction chi z‖ ≤ 32 * L := by
    intro z hz
    have hdist : ‖z - (sigma : ℂ)‖ = r := by
      simpa [dist_eq_norm] using mem_sphere.mp hz
    have hreDiff : |z.re - sigma| ≤ r := by
      calc
        |z.re - sigma| = |(z - (sigma : ℂ)).re| := by simp
        _ ≤ ‖z - (sigma : ℂ)‖ := Complex.abs_re_le_norm _
        _ = r := hdist
    have hzRe : 1 - 5 / (16 * L) ≤ z.re := by
      have hrad : r = 1 / (16 * L) := rfl
      rw [hrad] at hreDiff
      have hlower := (abs_le.mp hreDiff).1
      change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
      have hratio : 1 / (4 * L) = 4 * (1 / (16 * L)) := by
        field_simp [hLpos.ne']
        ring
      rw [hratio] at hsigmaNear
      have hfive : 5 / (16 * L) = 5 * (1 / (16 * L)) := by ring
      rw [hfive]
      linarith
    have hzNorm : ‖z‖ ≤ 2 := by
      calc
        ‖z‖ ≤ ‖(sigma : ℂ)‖ + ‖z - (sigma : ℂ)‖ := by
          simpa [add_comm] using norm_add_le (z - (sigma : ℂ)) (sigma : ℂ)
        _ = sigma + r := by simp [abs_of_pos hsigmaPos, hdist]
        _ ≤ 2 := by linarith
    simpa [L] using norm_LFunction_near_one_le hq chi hchi hzRe hzNorm
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 hrPos (DirichletCharacter.differentiable_LFunction hchi).diffContOnCl hsphere
  calc
    ‖iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
        Nat.factorial 2 * (32 * L) / r ^ 2 := hCauchy
    _ = 16384 * (Real.log (q : ℝ)) ^ 3 := by
      change 2 * (32 * L) / (1 / (16 * L)) ^ 2 = 16384 * L ^ 3
      field_simp [hLpos.ne']
      ring

/-- Positivity of the zeta convolution gives the elementary Euler-product
lower bound needed just to the right of one. -/
theorem one_le_riemannZeta_mul_LFunction_ofReal
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    (1 : ℂ) ≤ riemannZeta (sigma : ℂ) *
      DirichletCharacter.LFunction chi (sigma : ℂ) := by
  have hsum : LSeriesSummable chi.zetaMul (sigma : ℂ) :=
    chi.LSeriesSummable_zetaMul (by simpa using hsigma)
  have hterm : (1 : ℂ) ≤ LSeries chi.zetaMul (sigma : ℂ) := by
    have hnonneg (n : ℕ) :
        0 ≤ LSeries.term (chi.zetaMul ·) (sigma : ℂ) n :=
      LSeries.term_nonneg (DirichletCharacter.zetaMul_nonneg hsquare n) sigma
    have hone :
        LSeries.term (chi.zetaMul ·) (sigma : ℂ) 1 = (1 : ℂ) := by
      rw [LSeries.term_of_ne_zero one_ne_zero]
      simp [chi.isMultiplicative_zetaMul.map_one]
    calc
      (1 : ℂ) = ∑ n ∈ ({1} : Finset ℕ),
          LSeries.term (chi.zetaMul ·) (sigma : ℂ) n := by
        simp only [Finset.sum_singleton]
        exact hone.symm
      _ ≤ ∑' n : ℕ, LSeries.term (chi.zetaMul ·) (sigma : ℂ) n :=
        hsum.sum_le_tsum ({1} : Finset ℕ) (fun n _ ↦ hnonneg n)
      _ = LSeries chi.zetaMul (sigma : ℂ) := rfl
  calc
    (1 : ℂ) ≤ LSeries chi.zetaMul (sigma : ℂ) := hterm
    _ = riemannZeta (sigma : ℂ) *
        DirichletCharacter.LFunction chi (sigma : ℂ) := by
      rw [DirichletCharacter.zetaMul, ← ArithmeticFunction.coe_mul,
        LSeries_convolution']
      · have hs : 1 < ((sigma : ℂ)).re := by simpa using hsigma
        congr 1
        · simpa only [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
        · rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
          exact (LSeries_congr chi.apply_eq_toArithmeticFunction_apply (sigma : ℂ)).symm
      · exact LSeriesSummable_zeta_iff.mpr (by simpa using hsigma)
      · exact (LSeriesSummable_congr _ fun h ↦
          (chi.apply_eq_toArithmeticFunction_apply h).symm).mpr
            (ZMod.LSeriesSummable_of_one_lt_re chi (by simpa using hsigma))

/-- On the real half-line to the right of one, the continued zeta function
is the usual real Dirichlet series. -/
theorem riemannZeta_ofReal_eq_tsum_rpow
    {sigma : ℝ} (hsigma : 1 < sigma) :
    riemannZeta (sigma : ℂ) =
      ((∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
  calc
    riemannZeta (sigma : ℂ) =
        ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (sigma : ℂ) :=
      zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hsigma)
    _ = ∑' n : ℕ, (((n + 1 : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
      apply tsum_congr
      intro n
      have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have hcpow :
          ((((n : ℝ) + 1) ^ sigma : ℝ) : ℂ) =
            (((n : ℝ) + 1 : ℝ) : ℂ) ^ (sigma : ℂ) :=
        @Complex.ofReal_cpow ((n : ℝ) + 1) hn sigma
      rw [@Real.rpow_neg ((n : ℝ) + 1) hn sigma]
      calc
        1 / ((n : ℂ) + 1) ^ (sigma : ℂ) =
            ((((n : ℝ) + 1) ^ sigma : ℝ) : ℂ)⁻¹ := by
          rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num,
            ← hcpow, one_div]
        _ = (((((n : ℝ) + 1) ^ sigma)⁻¹ : ℝ) : ℂ) :=
          (Complex.ofReal_inv _).symm
    _ = ((∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma) : ℝ) : ℂ) :=
      (Complex.ofReal_tsum _).symm

/-- The elementary integral-test bound `zeta(sigma) ≤ 1 + 1/(sigma-1)`. -/
theorem riemannZeta_ofReal_le_one_add_inv_sub_one
    {sigma : ℝ} (hsigma : 1 < sigma) :
    riemannZeta (sigma : ℂ) ≤
      (((1 + 1 / (sigma - 1) : ℝ) : ℂ)) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-sigma)
  have hanti : AntitoneOn f (Ici (1 : ℝ)) := by
    intro a ha b hb hab
    change 1 ≤ a at ha
    change 1 ≤ b at hb
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by linarith)
  have hint : IntegrableOn f (Ioi (1 : ℝ)) := by
    dsimp [f]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hnonneg : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ f x := by
    intro x hx
    change 1 < x at hx
    dsimp [f]
    exact Real.rpow_nonneg (by linarith) _
  have hanti' : AntitoneOn f (Ici ((1 : ℕ) : ℝ)) := by
    simpa using hanti
  have hint' : IntegrableOn f (Ioi ((1 : ℕ) : ℝ)) := by
    simpa using hint
  have hnonneg' : ∀ x ∈ Ioi ((1 : ℕ) : ℝ), 0 ≤ f x := by
    simpa using hnonneg
  have htail := AntitoneOn.tsum_comp_add_le_integral
    (f := f) 1 hanti' hint' hnonneg'
  norm_num at htail
  have hintegral : ∫ x in Ioi (1 : ℝ), f x = 1 / (sigma - 1) := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    rw [Real.one_rpow]
    have hleft : -sigma + 1 ≠ 0 := by linarith
    have hright : sigma - 1 ≠ 0 := by linarith
    field_simp [hleft, hright]
    ring
  rw [hintegral] at htail
  have hsummable : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ (-sigma)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((_root_.summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (by linarith : -sigma < -1)))
  have hreal :
      (∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma)) ≤
        1 + 1 / (sigma - 1) := by
    rw [hsummable.tsum_eq_zero_add]
    simpa [f, add_assoc, Nat.cast_add, Nat.cast_one,
      Real.rpow_neg, one_div] using add_le_add_left htail 1
  rw [riemannZeta_ofReal_eq_tsum_rpow hsigma]
  exact_mod_cast hreal

/-- The same Dirichlet series is at least its first term. -/
theorem one_le_riemannZeta_ofReal
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (1 : ℂ) ≤ riemannZeta (sigma : ℂ) := by
  have hsummable : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ (-sigma)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((_root_.summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (by linarith : -sigma < -1)))
  have htail : 0 ≤ ∑' n : ℕ, (((n : ℝ) + 1) + 1) ^ (-sigma) :=
    tsum_nonneg fun _ ↦ Real.rpow_nonneg (by positivity) _
  rw [riemannZeta_ofReal_eq_tsum_rpow hsigma]
  apply Complex.le_def.mpr
  constructor
  · change (1 : ℝ) ≤ ∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma)
    rw [hsummable.tsum_eq_zero_add]
    norm_num
    exact htail
  · simp

/-- Positivity of the quadratic zeta convolution and the elementary zeta
upper bound imply the useful lower bound `L(sigma, chi) ≥ (sigma-1)/sigma`. -/
theorem sub_one_div_self_le_LFunction_ofReal
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    ((((sigma - 1) / sigma : ℝ) : ℂ)) ≤
      DirichletCharacter.LFunction chi (sigma : ℂ) := by
  let Z := riemannZeta (sigma : ℂ)
  let V := DirichletCharacter.LFunction chi (sigma : ℂ)
  have hprod : (1 : ℂ) ≤ Z * V := by
    simpa [Z, V] using
      one_le_riemannZeta_mul_LFunction_ofReal chi hchi hsquare hsigma
  have hZupper : Z ≤ (((1 + 1 / (sigma - 1) : ℝ) : ℂ)) := by
    simpa [Z] using riemannZeta_ofReal_le_one_add_inv_sub_one hsigma
  have hZlower : (1 : ℂ) ≤ Z := by
    simpa [Z] using one_le_riemannZeta_ofReal hsigma
  have hZim : Z.im = 0 := by
    simpa using (Complex.le_def.mp hZlower).2.symm
  have hVim : V.im = 0 := by
    have hconj := LFunction_conj_of_sq_eq_one chi hchi hsquare (sigma : ℂ)
    apply Complex.conj_eq_iff_im.mp
    simpa [V] using hconj.symm
  have hprodRe : 1 ≤ Z.re * V.re := by
    have h := (Complex.le_def.mp hprod).1
    simpa [Complex.mul_re, hZim, hVim] using h
  have hZupperRe : Z.re ≤ 1 + 1 / (sigma - 1) := by
    have h := (Complex.le_def.mp hZupper).1
    change Z.re ≤ 1 + 1 / (sigma - 1) at h
    exact h
  have hZlowerRe : 1 ≤ Z.re := by
    simpa using (Complex.le_def.mp hZlower).1
  have hZpos : 0 < Z.re := zero_lt_one.trans_le hZlowerRe
  have hrecipZ : 1 / Z.re ≤ V.re := by
    apply (div_le_iff₀ hZpos).mpr
    simpa [one_div, mul_comm] using hprodRe
  have hrecipUpper :
      1 / (1 + 1 / (sigma - 1)) ≤ 1 / Z.re :=
    one_div_le_one_div_of_le hZpos hZupperRe
  have hsigmaPos : 0 < sigma := by linarith
  have hsubPos : 0 < sigma - 1 := by linarith
  have hid : 1 / (1 + 1 / (sigma - 1)) = (sigma - 1) / sigma := by
    field_simp [hsigmaPos.ne', hsubPos.ne']
    ring
  apply Complex.le_def.mpr
  constructor
  · change (sigma - 1) / sigma ≤ V.re
    rw [← hid]
    exact hrecipUpper.trans hrecipZ
  · simpa [V] using hVim.symm

/-- If a real quadratic `L`-value at one were smaller than a fixed negative
power of its logarithmic conductor, Taylor's theorem would force a real zero
in a very short interval immediately to the left of one. -/
theorem exists_real_zero_of_LFunction_one_re_lt
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1)
    (hsmall :
      (DirichletCharacter.LFunction chi (1 : ℂ)).re <
        1 / ((2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3)) :
    ∃ beta : ℝ,
      1 - 8 * (DirichletCharacter.LFunction chi (1 : ℂ)).re ≤ beta ∧
      beta ≤ 1 ∧
      DirichletCharacter.LFunction chi (beta : ℂ) = 0 := by
  let L := Real.log (q : ℝ)
  let ell := (DirichletCharacter.LFunction chi (1 : ℂ)).re
  let delta := 8 * ell
  let M := 16384 * L ^ 3
  let F : ℝ → ℂ := fun sigma ↦
    DirichletCharacter.LFunction chi (sigma : ℂ)
  let F' : ℝ → ℂ := fun sigma ↦
    deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)
  let F'' : ℝ → ℂ := fun sigma ↦
    iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ)
  have hLone : 1 < L := one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hellPos : 0 < ell := by
    have heff := effectiveQuadraticLValueLowerBound hq chi hchi hsquare
    have heffRe := (Complex.le_def.mp heff).1
    have hbasePos : 0 <
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) := by
      positivity
    change 1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤ ell at heffRe
    exact hbasePos.trans_le heffRe
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hdenomPos : 0 < (2 ^ 24 : ℝ) * L ^ 3 := by positivity
  have hscaled : (2 ^ 24 : ℝ) * L ^ 3 * ell < 1 := by
    have hs : ell * ((2 ^ 24 : ℝ) * L ^ 3) < 1 := by
      apply (lt_div_iff₀ hdenomPos).mp
      simpa [L, ell] using hsmall
    simpa [mul_comm] using hs
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hdeltaNear : delta ≤ 1 / (4 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * L)).mpr
    have hbase : 0 ≤ L * ell := mul_nonneg hLpos.le hellPos.le
    have hcomparison :
        32 * L * ell ≤ (2 ^ 24 : ℝ) * L ^ 3 * ell := by
      calc
        32 * L * ell ≤ (2 ^ 24 : ℝ) * (L * ell) := by
          nlinarith
        _ ≤ (2 ^ 24 : ℝ) * (L ^ 2 * (L * ell)) := by
          gcongr <;> nlinarith
        _ = (2 ^ 24 : ℝ) * L ^ 3 * ell := by ring
    dsimp [delta]
    convert hcomparison.trans hscaled.le using 1 <;> ring
  have hdeltaHalf : delta ≤ 1 / 2 := by
    have hquarter : 1 / (4 * L) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity : 0 < 4 * L)]
      nlinarith
    exact hdeltaNear.trans hquarter.le
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have herror : 2 * M * delta ^ 2 < ell := by
    dsimp [M, delta]
    nlinarith
  have hrightRem :
      ‖F (1 + delta) - F 1 - (delta : ℂ) * F' 1‖ ≤
        M * delta ^ 2 := by
    have hraw := norm_first_order_remainder_right_le
        (a := (1 : ℝ)) (b := 1 + delta) (M := M)
        (f := F) (f' := F') (f'' := F'')
        (by linarith) hMnonneg
        (by
          intro sigma _
          dsimp [F, F']
          exact ((DirichletCharacter.differentiable_LFunction hchi
            (sigma : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
        (by
          intro sigma _
          dsimp [F', F'']
          exact (hasDerivAt_deriv_LFunction_ofReal chi hchi sigma).hasDerivWithinAt)
        (by
          intro sigma hsigma
          dsimp [F'']
          apply norm_iteratedDeriv_two_LFunction_ofReal_near_one_le
            hq chi hchi
          · have hfrac : 0 < 1 / (4 * L) := by positivity
            have : 1 - 1 / (4 * L) < 1 := by linarith
            change 1 - 1 / (4 * L) ≤ sigma
            exact this.le.trans hsigma.1
          · change sigma ≤ 3 / 2
            linarith [hsigma.2, hdeltaHalf])
    simpa using hraw
  have hleftRem :
      ‖F (1 - delta) - F 1 - ((-delta : ℝ) : ℂ) * F' 1‖ ≤
        M * delta ^ 2 := by
    have hraw := norm_first_order_remainder_left_le
      (a := 1 - delta) (b := (1 : ℝ)) (M := M)
      (f := F) (f' := F') (f'' := F'')
      (by linarith : 1 - delta ≤ (1 : ℝ)) hMnonneg
      (by
        intro sigma _
        dsimp [F, F']
        exact ((DirichletCharacter.differentiable_LFunction hchi
          (sigma : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
      (by
        intro sigma _
        dsimp [F', F'']
        exact (hasDerivAt_deriv_LFunction_ofReal chi hchi sigma).hasDerivWithinAt)
      (by
        intro sigma hsigma
        dsimp [F'']
        apply norm_iteratedDeriv_two_LFunction_ofReal_near_one_le
          hq chi hchi
        · change 1 - 1 / (4 * L) ≤ sigma
          linarith [hsigma.1, hdeltaNear]
        · change sigma ≤ 3 / 2
          linarith [hsigma.2])
    simpa using hraw
  have hrightLower : 4 * ell ≤ (F (1 + delta)).re := by
    have hcomplex := sub_one_div_self_le_LFunction_ofReal
      chi hchi hsquare (sigma := 1 + delta) (by linarith)
    have hre := (Complex.le_def.mp hcomplex).1
    have hratio : 4 * ell ≤ delta / (1 + delta) := by
      apply (le_div_iff₀ (by linarith : 0 < 1 + delta)).mpr
      dsimp [delta]
      nlinarith [hdeltaHalf]
    norm_num only [Complex.ofReal_re] at hre
    change ((1 + delta - 1) / (1 + delta) : ℝ) ≤
      (F (1 + delta)).re at hre
    have hre' : (delta / (1 + delta) : ℝ) ≤
        (F (1 + delta)).re := by
      convert hre using 1 <;> ring
    exact hratio.trans hre'
  have hrightError :
      (F (1 + delta)).re - ell - delta * (F' 1).re ≤
        M * delta ^ 2 := by
    have h := (Complex.abs_re_le_norm
      (F (1 + delta) - F 1 - (delta : ℂ) * F' 1)).trans hrightRem
    have hupper := (abs_le.mp h).2
    simpa [F, ell] using hupper
  have hleftError :
      (F (1 - delta)).re - ell + delta * (F' 1).re ≤
        M * delta ^ 2 := by
    have h := (Complex.abs_re_le_norm
      (F (1 - delta) - F 1 - ((-delta : ℝ) : ℂ) * F' 1)).trans hleftRem
    have hupper := (abs_le.mp h).2
    calc
      (F (1 - delta)).re - ell + delta * (F' 1).re =
          (F (1 - delta) - F 1 - ((-delta : ℝ) : ℂ) * F' 1).re := by
        simp [F, ell]
      _ ≤ M * delta ^ 2 := hupper
  have hleftNeg : (F (1 - delta)).re < 0 := by
    nlinarith
  let g : ℝ → ℝ := fun sigma ↦ (F sigma).re
  have hgContinuous : Continuous g := by
    dsimp [g, F]
    exact Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hchi).continuous.comp
        Complex.continuous_ofReal)
  have hzeroMem : (0 : ℝ) ∈ Icc (g (1 - delta)) (g 1) := by
    constructor
    · simpa [g] using hleftNeg.le
    · change 0 ≤ ell
      exact hellPos.le
  obtain ⟨beta, hbetaMem, hbetaZero⟩ :=
    intermediate_value_Icc (by linarith : 1 - delta ≤ (1 : ℝ))
      hgContinuous.continuousOn hzeroMem
  refine ⟨beta, ?_, hbetaMem.2, ?_⟩
  · simpa [delta, ell] using hbetaMem.1
  · have hreal : (F beta).re = 0 := by
      simpa [g] using hbetaZero
    have himag : (F beta).im = 0 := by
      have hconj := LFunction_conj_of_sq_eq_one chi hchi hsquare (beta : ℂ)
      apply Complex.conj_eq_iff_im.mp
      simpa [F] using hconj.symm
    apply Complex.ext
    · simpa [F] using hreal
    · simpa [F] using himag

private theorem eventually_rpow_neg_one_div_1024_le_log_threshold :
    ∀ᶠ q : ℕ in Filter.atTop,
      (q : ℝ) ^ (-(1 / 1024 : ℝ)) ≤
        1 / ((2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3) := by
  have hlittle := (isLittleO_log_rpow_rpow_atTop
    (3 : ℝ) (show (0 : ℝ) < 1 / 1024 by norm_num)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlittle.bound
    (show (0 : ℝ) < 1 / (2 ^ 24 : ℝ) by positivity)
  filter_upwards [hbound, Filter.eventually_ge_atTop 3] with q hqbound hq
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < q := by positivity
  have hlogPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by linarith)
  have hpowPos : 0 < (q : ℝ) ^ (1 / 1024 : ℝ) :=
    Real.rpow_pos_of_pos hqPos _
  simp only [Function.comp_apply, Real.norm_eq_abs] at hqbound
  rw [abs_of_pos (Real.rpow_pos_of_pos hlogPos _),
    abs_of_pos hpowPos] at hqbound
  have hdom :
      (2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3 ≤
        (q : ℝ) ^ (1 / 1024 : ℝ) := by
    have hlogpow :
        Real.log (q : ℝ) ^ (3 : ℝ) =
          (Real.log (q : ℝ)) ^ (3 : ℕ) := by
      norm_num [Real.rpow_natCast]
    rw [hlogpow] at hqbound
    nlinarith
  have hdenomPos : 0 <
      (2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3 := by positivity
  have hrecip := one_div_le_one_div_of_le hdenomPos hdom
  rw [@Real.rpow_neg (q : ℝ) hqPos.le (1 / 1024 : ℝ), one_div]
  simpa [one_div] using hrecip

/-- A fixed, fully uniform Siegel lower bound adequate for the later
hyperbola argument.  The exponent is deliberately very small; no effective
constant is required. -/
theorem eventually_quadratic_LFunction_one_re_ge_rpow :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ [NeZero q] (chi : DirichletCharacter ℂ q),
        chi ≠ 1 → chi ^ 2 = 1 →
          (q : ℝ) ^ (-(1 / 1024 : ℝ)) ≤
            (DirichletCharacter.LFunction chi (1 : ℂ)).re := by
  obtain ⟨c, hc, hzeroFree⟩ := exists_siegelRealCharacterZeroFree
    (1 / 2048 : ℝ) (by norm_num)
  have hpowTendsto : Tendsto
      (fun q : ℕ ↦ (q : ℝ) ^ (-(1 / 2048 : ℝ)))
      Filter.atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2048 by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpowSmall : ∀ᶠ q : ℕ in Filter.atTop,
      (q : ℝ) ^ (-(1 / 2048 : ℝ)) < c / 8 :=
    hpowTendsto.eventually (eventually_lt_nhds (by positivity))
  filter_upwards [eventually_rpow_neg_one_div_1024_le_log_threshold,
    hpowSmall, Filter.eventually_gt_atTop 1] with q hlogThreshold hpowSmallq hq
  intro _ chi hchi hsquare
  by_contra hnot
  have hvalueSmall :
      (DirichletCharacter.LFunction chi (1 : ℂ)).re <
        (q : ℝ) ^ (-(1 / 1024 : ℝ)) := by
    exact lt_of_not_ge hnot
  have hlogSmall :
      (DirichletCharacter.LFunction chi (1 : ℂ)).re <
        1 / ((2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3) :=
    hvalueSmall.trans_le hlogThreshold
  obtain ⟨beta, hbetaLower, hbetaUpper, hbetaZero⟩ :=
    exists_real_zero_of_LFunction_one_re_lt hq chi hchi hsquare hlogSmall
  have hqPos : (0 : ℝ) < q := by positivity
  have hsq :
      (q : ℝ) ^ (-(1 / 1024 : ℝ)) =
        ((q : ℝ) ^ (-(1 / 2048 : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hqPos.le]
    congr 1
    ring
  have haPos : 0 < (q : ℝ) ^ (-(1 / 2048 : ℝ)) :=
    Real.rpow_pos_of_pos hqPos _
  have hgap :
      8 * (DirichletCharacter.LFunction chi (1 : ℂ)).re <
        c * (q : ℝ) ^ (-(1 / 2048 : ℝ)) := by
    rw [hsq] at hvalueSmall
    nlinarith
  have hbetaStrict :
      1 - c * (q : ℝ) ^ (-(1 / 2048 : ℝ)) < beta := by
    linarith
  exact (hzeroFree q chi hchi hsquare beta hbetaStrict) hbetaZero


end

end Erdos1140
