/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.ReductionCore

/-!
# Divisor-weighted tails over squarefull numbers

This file supplies the convergent squarefull sums used in Ford's reduction.
The elementary input is the representation of every squarefull integer as
`a ^ 2 * b ^ 3`.  We keep the representation theorem public since it is also
useful for other squarefull error terms.
-/

namespace Erdos896.Ford

open scoped BigOperators

private def squarePartExponent (e : ℕ) : ℕ :=
  (e - 3 * (e % 2)) / 2

private def cubePartExponent (e : ℕ) : ℕ :=
  e % 2

private lemma exponent_decomposition {e : ℕ} (he : e = 0 ∨ 2 ≤ e) :
    2 * squarePartExponent e + 3 * cubePartExponent e = e := by
  rcases Nat.even_or_odd e with heven | hodd
  · have hmod : e % 2 = 0 := (Nat.even_iff.mp heven)
    simp only [squarePartExponent, cubePartExponent, hmod, mul_zero, Nat.sub_zero,
      add_zero]
    omega
  · have hmod : e % 2 = 1 := (Nat.odd_iff.mp hodd)
    rcases he with rfl | he
    · simp at hmod
    simp only [squarePartExponent, cubePartExponent, hmod, mul_one]
    omega

/-- Every positive squarefull number is the product of a square and a cube.

The construction is canonical at the level of prime exponents: an even
exponent goes entirely into the square, while an odd exponent contributes
three to the cube and the remaining even part to the square. -/
theorem Squarefull.exists_sq_mul_cube {q : ℕ} (hq : Squarefull q) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ q = a ^ 2 * b ^ 3 := by
  classical
  let A : ℕ →₀ ℕ := q.factorization.mapRange squarePartExponent (by simp [squarePartExponent])
  let B : ℕ →₀ ℕ := q.factorization.mapRange cubePartExponent (by simp [cubePartExponent])
  let a : ℕ := A.prod (fun p e ↦ p ^ e)
  let b : ℕ := B.prod (fun p e ↦ p ^ e)
  have hAprime : ∀ p ∈ A.support, p.Prime := by
    intro p hp
    apply Nat.prime_of_mem_primeFactors
    exact Finsupp.support_mapRange hp
  have hBprime : ∀ p ∈ B.support, p.Prime := by
    intro p hp
    apply Nat.prime_of_mem_primeFactors
    exact Finsupp.support_mapRange hp
  have haFac : a.factorization = A := Nat.prod_pow_factorization_eq_self hAprime
  have hbFac : b.factorization = B := Nat.prod_pow_factorization_eq_self hBprime
  have ha : 0 < a := by
    apply Nat.pos_of_ne_zero
    exact Finsupp.prod_ne_zero_iff.mpr fun p hp ↦ pow_ne_zero _ (hAprime p hp).ne_zero
  have hb : 0 < b := by
    apply Nat.pos_of_ne_zero
    exact Finsupp.prod_ne_zero_iff.mpr fun p hp ↦ pow_ne_zero _ (hBprime p hp).ne_zero
  refine ⟨a, b, ha, hb, ?_⟩
  symm
  apply Nat.eq_of_factorization_eq (mul_ne_zero (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne'))
    hq.1.ne'
  intro p
  rw [Nat.factorization_mul (pow_ne_zero _ ha.ne') (pow_ne_zero _ hb.ne'),
    Nat.factorization_pow, Nat.factorization_pow, haFac, hbFac]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, A, B, Finsupp.mapRange_apply]
  apply exponent_decomposition
  by_cases hp : p ∈ q.primeFactors
  · right
    have hp2dvd : p ^ 2 ∣ q := hq.2 p hp
    exact (Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hq.1.ne' |>.mp hp2dvd
  · left
    exact Finsupp.notMem_support_iff.mp (by simpa using hp)

/-! ## A fixed power bound for the divisor function -/

private lemma cube_succ_le_twentySeven_mul_two_pow {e : ℕ} (he : 2 ≤ e) :
    (e + 1) ^ 3 ≤ 27 * 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
      by_cases heq : e = 2
      · subst e
        norm_num
      · have he3 : 3 ≤ e := by omega
        have hsq : 3 * e ≤ e ^ 2 := by
          calc
            3 * e ≤ e * e := Nat.mul_le_mul_right e he3
            _ = e ^ 2 := by ring
        have hcub : 3 * e ^ 2 ≤ e ^ 3 := by
          calc
            3 * e ^ 2 ≤ e * e ^ 2 := Nat.mul_le_mul_right (e ^ 2) he3
            _ = e ^ 3 := by ring
        have hlin : 6 * e + 6 ≤ 3 * e ^ 2 := by nlinarith
        calc
          (e + 1 + 1) ^ 3 ≤ 2 * (e + 1) ^ 3 := by nlinarith
          _ ≤ 2 * (27 * 2 ^ e) := Nat.mul_le_mul_left 2 ih
          _ = 27 * 2 ^ (e + 1) := by ring

private lemma cube_succ_le_prime_pow {p e : ℕ} (hp : 11 ≤ p) (he : 2 ≤ e) :
    (e + 1) ^ 3 ≤ p ^ e := by
  induction e, he using Nat.le_induction with
  | base => nlinarith
  | succ e he ih =>
      calc
        (e + 1 + 1) ^ 3 ≤ (2 * (e + 1)) ^ 3 :=
          Nat.pow_le_pow_left (by omega) 3
        _ = 8 * (e + 1) ^ 3 := by ring
        _ ≤ 8 * p ^ e := Nat.mul_le_mul_left 8 ih
        _ ≤ p * p ^ e := Nat.mul_le_mul_right (p ^ e) (by omega)
        _ = p ^ (e + 1) := by ring

private lemma cube_succ_le_local_factor {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    (e + 1) ^ 3 ≤ (if p < 11 then 27 else 1) * p ^ e := by
  split_ifs with hsmall
  · calc
      (e + 1) ^ 3 ≤ 27 * 2 ^ e := cube_succ_le_twentySeven_mul_two_pow he
      _ ≤ 27 * p ^ e := Nat.mul_le_mul_left 27
        (Nat.pow_le_pow_left hp.two_le e)
  · simpa using cube_succ_le_prime_pow (by omega) he

/-- A convenient absolute constant in the squarefull divisor bound. -/
def squarefullDivisorConstant : ℕ := 27 ^ 11

private lemma smallPrimeFactorProduct_le :
    ∀ S : Finset ℕ, (∏ p ∈ S, if p < 11 then 27 else 1) ≤ squarefullDivisorConstant := by
  intro S
  let U := S.filter (fun p ↦ p < 11)
  have hU : U ⊆ Finset.range 11 := by
    intro p hp
    have hp' : p ∈ S ∧ p < 11 := by simpa [U] using hp
    exact Finset.mem_range.mpr hp'.2
  have hcard : U.card ≤ 11 := by
    simpa using Finset.card_le_card hU
  calc
    (∏ p ∈ S, if p < 11 then 27 else 1) = 27 ^ U.card := by
      simp [U, Finset.prod_ite]
    _ ≤ 27 ^ 11 := Nat.pow_le_pow_right (by norm_num) hcard
    _ = squarefullDivisorConstant := rfl

/-- On squarefull numbers the divisor function is bounded by a fixed
multiple of the cube root, in a cubed form which avoids choosing a root. -/
theorem Squarefull.card_divisors_cube_le {q : ℕ} (hq : Squarefull q) :
    q.divisors.card ^ 3 ≤ squarefullDivisorConstant * q := by
  rw [Nat.card_divisors hq.1.ne', ← Finset.prod_pow]
  calc
    (∏ p ∈ q.primeFactors, (q.factorization p + 1) ^ 3) ≤
        ∏ p ∈ q.primeFactors,
          ((if p < 11 then 27 else 1) * p ^ q.factorization p) := by
      apply Finset.prod_le_prod'
      intro p hp
      apply cube_succ_le_local_factor (Nat.prime_of_mem_primeFactors hp)
      exact ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hq.1.ne').mp
        (hq.2 p hp)
    _ = (∏ p ∈ q.primeFactors, if p < 11 then 27 else 1) *
        ∏ p ∈ q.primeFactors, p ^ q.factorization p := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ p ∈ q.primeFactors, if p < 11 then 27 else 1) * q := by
      exact congrArg (fun z ↦
        (∏ p ∈ q.primeFactors, if p < 11 then 27 else 1) * z)
        (Nat.prod_primeFactors_pow_factorization hq.1.ne').symm
    _ ≤ squarefullDivisorConstant * q := Nat.mul_le_mul_right q
      (smallPrimeFactorProduct_le q.primeFactors)

/-! ## Real-power majorants -/

/-- The canonical square/cube pair used below to reindex squarefull sums. -/
noncomputable def squarefullRepresentation (q : ℕ) : ℕ × ℕ :=
  if hq : Squarefull q then
    (hq.exists_sq_mul_cube.choose, hq.exists_sq_mul_cube.choose_spec.choose)
  else (1, 1)

theorem squarefullRepresentation_spec {q : ℕ} (hq : Squarefull q) :
    0 < (squarefullRepresentation q).1 ∧
      0 < (squarefullRepresentation q).2 ∧
      q = (squarefullRepresentation q).1 ^ 2 * (squarefullRepresentation q).2 ^ 3 := by
  classical
  simp only [squarefullRepresentation, dif_pos hq]
  exact hq.exists_sq_mul_cube.choose_spec.choose_spec

theorem squarefullRepresentation_injOn :
    Set.InjOn squarefullRepresentation {q : ℕ | Squarefull q} := by
  intro q hq r hr hqr
  have hqspec := squarefullRepresentation_spec hq
  have hrspec := squarefullRepresentation_spec hr
  have hfst := congrArg Prod.fst hqr
  have hsnd := congrArg Prod.snd hqr
  rw [hqspec.2.2, hrspec.2.2, hfst, hsnd]

private theorem Squarefull.card_divisors_real_le {q : ℕ} (hq : Squarefull q) :
    (q.divisors.card : ℝ) ≤
      squarefullDivisorConstant * (q : ℝ) ^ (1 / 3 : ℝ) := by
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 3 ≠ 0)).mp
  calc
    (q.divisors.card : ℝ) ^ 3 = (q.divisors.card ^ 3 : ℕ) := by norm_num
    _ ≤ (squarefullDivisorConstant * q : ℕ) := by
      exact_mod_cast hq.card_divisors_cube_le
    _ ≤ ((squarefullDivisorConstant : ℝ) * (q : ℝ)) := by norm_num
    _ ≤ ((squarefullDivisorConstant : ℝ) ^ 3 * (q : ℝ)) := by
      gcongr
      norm_num [squarefullDivisorConstant]
    _ = ((squarefullDivisorConstant : ℝ) * (q : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
      norm_num

private lemma squarefullRepresentation_rpow {q : ℕ} (hq : Squarefull q) (s : ℝ) :
    (q : ℝ) ^ (-s) =
      ((squarefullRepresentation q).1 : ℝ) ^ (-2 * s) *
        ((squarefullRepresentation q).2 : ℝ) ^ (-3 * s) := by
  have hspec := squarefullRepresentation_spec hq
  have hcast : (q : ℝ) =
      ((squarefullRepresentation q).1 : ℝ) ^ 2 *
        ((squarefullRepresentation q).2 : ℝ) ^ 3 := by
    exact_mod_cast hspec.2.2
  conv_lhs => rw [hcast]
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
  ring_nf

private lemma squarefull_moment_term_le {q : ℕ} (hq : Squarefull q) :
    (q.divisors.card : ℝ) * (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ) ≤
      squarefullDivisorConstant * (q : ℝ) ^ (-13 / 24 : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.1
  calc
    (q.divisors.card : ℝ) * (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ) ≤
        (squarefullDivisorConstant * (q : ℝ) ^ (1 / 3 : ℝ)) *
          (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ) := by
      gcongr
      exact hq.card_divisors_real_le
    _ = squarefullDivisorConstant * (q : ℝ) ^ (-13 / 24 : ℝ) := by
      rw [← Real.rpow_neg_one]
      calc
        squarefullDivisorConstant * (q : ℝ) ^ (1 / 3 : ℝ) * (q : ℝ) ^ (-1 : ℝ) *
            (q : ℝ) ^ (1 / 8 : ℝ) =
            squarefullDivisorConstant *
              ((q : ℝ) ^ (1 / 3 : ℝ) * (q : ℝ) ^ (-1 : ℝ) *
                (q : ℝ) ^ (1 / 8 : ℝ)) := by ring
        _ = squarefullDivisorConstant * (q : ℝ) ^ (-13 / 24 : ℝ) := by
          rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
          norm_num

private noncomputable def squarefullPairMajorant (ab : ℕ × ℕ) : ℝ :=
  (ab.1 : ℝ) ^ (-13 / 12 : ℝ) * (ab.2 : ℝ) ^ (-13 / 8 : ℝ)

private lemma summable_squarefullPairMajorant : Summable squarefullPairMajorant := by
  apply (Real.summable_nat_rpow.mpr (by norm_num : (-13 / 12 : ℝ) < -1)).mul_of_nonneg
    (Real.summable_nat_rpow.mpr (by norm_num : (-13 / 8 : ℝ) < -1))
  · intro n
    positivity
  · intro n
    positivity

private lemma squarefull_rpow_sum_le_pair_tsum (R : ℕ) :
    (∑ q ∈ squarefullSet R, (q : ℝ) ^ (-13 / 24 : ℝ)) ≤
      ∑' ab : ℕ × ℕ, squarefullPairMajorant ab := by
  classical
  let S := squarefullSet R
  have hinj : Set.InjOn squarefullRepresentation (S : Set ℕ) := by
    apply squarefullRepresentation_injOn.mono
    intro q hq
    exact (mem_squarefullSet.mp (by simpa [S] using hq)).2.2
  calc
    (∑ q ∈ squarefullSet R, (q : ℝ) ^ (-13 / 24 : ℝ)) =
        ∑ ab ∈ S.image squarefullRepresentation, squarefullPairMajorant ab := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr (by simp [S])
      intro q hq
      have hqfull : Squarefull q := (mem_squarefullSet.mp hq).2.2
      rw [show (-13 / 24 : ℝ) = -(13 / 24 : ℝ) by norm_num]
      rw [squarefullRepresentation_rpow hqfull (13 / 24 : ℝ)]
      simp only [squarefullPairMajorant]
      norm_num
    _ ≤ ∑' ab : ℕ × ℕ, squarefullPairMajorant ab :=
      summable_squarefullPairMajorant.sum_le_tsum _ (fun _ _ ↦ by
        simp only [squarefullPairMajorant]
        positivity)

/-- Uniform convergence of the divisor-weighted squarefull `1/8`-moment.

The inner sum is deliberately written in the form used by the reduction:
there is one identical term for every divisor `f ∣ q`.  This stronger moment
simultaneously controls large squarefull parts and large divisor fibers. -/
theorem exists_uniform_squarefull_divisor_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ,
      (∑ q ∈ squarefullSet R, ∑ _f ∈ q.divisors,
        (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ)) ≤ C := by
  let Z : ℝ := ∑' ab : ℕ × ℕ, squarefullPairMajorant ab
  let C : ℝ := squarefullDivisorConstant * Z + 1
  have hZ : 0 ≤ Z := tsum_nonneg fun ab ↦ by
    simp only [squarefullPairMajorant]
    positivity
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, fun R ↦ ?_⟩
  calc
    (∑ q ∈ squarefullSet R, ∑ _f ∈ q.divisors,
        (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ)) =
        ∑ q ∈ squarefullSet R,
          (q.divisors.card : ℝ) * (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [mul_assoc]
    _ ≤ ∑ q ∈ squarefullSet R,
        squarefullDivisorConstant * (q : ℝ) ^ (-13 / 24 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact squarefull_moment_term_le (mem_squarefullSet.mp hq).2.2
    _ = squarefullDivisorConstant *
        ∑ q ∈ squarefullSet R, (q : ℝ) ^ (-13 / 24 : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ squarefullDivisorConstant * Z := by
      gcongr
      exact squarefull_rpow_sum_le_pair_tsum R
    _ ≤ C := by
      dsimp only [C]
      linarith

/-- The exact `max (f,q/f)` moment used after Ford's squarefull reduction.
It is bounded by the outer moment because both complementary divisors are at
most `q`. -/
theorem exists_uniform_squarefull_max_divisor_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ,
      (∑ q ∈ squarefullSet R, ∑ f ∈ q.divisors,
        (q : ℝ)⁻¹ * ((max f (q / f) : ℕ) : ℝ) ^ (1 / 8 : ℝ)) ≤ C := by
  obtain ⟨C, hC, hmoment⟩ := exists_uniform_squarefull_divisor_moment
  refine ⟨C, hC, fun R ↦ (Finset.sum_le_sum fun q hq ↦ ?_).trans (hmoment R)⟩
  apply Finset.sum_le_sum
  intro f hf
  have hqpos : 0 < q := (mem_squarefullSet.mp hq).1
  have hfdata := Nat.mem_divisors.mp hf
  have hmax : max f (q / f) ≤ q := max_le
    (Nat.le_of_dvd hqpos hfdata.1) (Nat.div_le_self q f)
  have hpow : (((max f (q / f) : ℕ) : ℝ) ^ (1 / 8 : ℝ)) ≤
      (q : ℝ) ^ (1 / 8 : ℝ) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hmax
    · norm_num
  gcongr

/-- Uniform convergence of `∑ τ(q)/q` over squarefull `q`. -/
theorem exists_uniform_squarefull_divisor_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ,
      (∑ q ∈ squarefullSet R, (q.divisors.card : ℝ) * (q : ℝ)⁻¹) ≤ C := by
  obtain ⟨C, hC, hmoment⟩ := exists_uniform_squarefull_divisor_moment
  refine ⟨C, hC, fun R ↦ ?_⟩
  calc
    (∑ q ∈ squarefullSet R, (q.divisors.card : ℝ) * (q : ℝ)⁻¹) ≤
        ∑ q ∈ squarefullSet R,
          (q.divisors.card : ℝ) * (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqone : (1 : ℝ) ≤ q := by
        exact_mod_cast (mem_squarefullSet.mp hq).1
      have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) :=
        Real.one_le_rpow hqone (by norm_num)
      calc
        (q.divisors.card : ℝ) * (q : ℝ)⁻¹ =
            ((q.divisors.card : ℝ) * (q : ℝ)⁻¹) * 1 := by ring
        _ ≤ ((q.divisors.card : ℝ) * (q : ℝ)⁻¹) *
            (q : ℝ) ^ (1 / 8 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ∑ q ∈ squarefullSet R, ∑ _f ∈ q.divisors,
        (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [mul_assoc]
    _ ≤ C := hmoment R

/-- Quantitative tail for the divisor-weighted squarefull reciprocal sum.
The exponent `1/8` is the same spare moment supplied above. -/
theorem exists_squarefull_divisor_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R T : ℕ, 0 < T →
      (∑ q ∈ squarefullTailSet R T, ∑ _f ∈ q.divisors, (q : ℝ)⁻¹) ≤
        C / (T : ℝ) ^ (1 / 8 : ℝ) := by
  obtain ⟨C, hC, hmoment⟩ := exists_uniform_squarefull_divisor_moment
  refine ⟨C, hC, fun R T hT ↦ ?_⟩
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hTpow : 0 < (T : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hTr _
  calc
    (∑ q ∈ squarefullTailSet R T, ∑ _f ∈ q.divisors, (q : ℝ)⁻¹) ≤
        ∑ q ∈ squarefullTailSet R T,
          ((T : ℝ) ^ (1 / 8 : ℝ))⁻¹ *
            (∑ _f ∈ q.divisors, (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro f hf
      have hTq : T ≤ q := (mem_squarefullTailSet.mp hq).2.2.2.le
      have hpow : (T : ℝ) ^ (1 / 8 : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := by
        apply Real.rpow_le_rpow
        · positivity
        · exact_mod_cast hTq
        · norm_num
      have hone : (1 : ℝ) ≤ ((T : ℝ) ^ (1 / 8 : ℝ))⁻¹ *
          (q : ℝ) ^ (1 / 8 : ℝ) := by
        rw [inv_mul_eq_div]
        exact (le_div_iff₀ hTpow).mpr (by simpa using hpow)
      calc
        (q : ℝ)⁻¹ = (q : ℝ)⁻¹ * 1 := by ring
        _ ≤ (q : ℝ)⁻¹ * (((T : ℝ) ^ (1 / 8 : ℝ))⁻¹ *
            (q : ℝ) ^ (1 / 8 : ℝ)) := mul_le_mul_of_nonneg_left hone (by positivity)
        _ = ((T : ℝ) ^ (1 / 8 : ℝ))⁻¹ *
            ((q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ)) := by ring
    _ = ((T : ℝ) ^ (1 / 8 : ℝ))⁻¹ *
        (∑ q ∈ squarefullTailSet R T,
          ∑ _f ∈ q.divisors, (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ ((T : ℝ) ^ (1 / 8 : ℝ))⁻¹ *
        (∑ q ∈ squarefullSet R,
          ∑ _f ∈ q.divisors, (q : ℝ)⁻¹ * (q : ℝ) ^ (1 / 8 : ℝ)) := by
      gcongr
      simpa only [squarefullTailSet] using
        (Finset.filter_subset (fun q ↦ T < q) (squarefullSet R))
    _ ≤ ((T : ℝ) ^ (1 / 8 : ℝ))⁻¹ * C := by
      gcongr
      exact hmoment R
    _ = C / (T : ℝ) ^ (1 / 8 : ℝ) := by ring

/-- Card-form restatement of `exists_squarefull_divisor_tail_bound`. -/
theorem exists_squarefull_card_divisors_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ R T : ℕ, 0 < T →
      (∑ q ∈ squarefullTailSet R T,
        (q.divisors.card : ℝ) * (q : ℝ)⁻¹) ≤
          C / (T : ℝ) ^ (1 / 8 : ℝ) := by
  obtain ⟨C, hC, htail⟩ := exists_squarefull_divisor_tail_bound
  refine ⟨C, hC, fun R T hT ↦ ?_⟩
  simpa using htail R T hT

end Erdos896.Ford
