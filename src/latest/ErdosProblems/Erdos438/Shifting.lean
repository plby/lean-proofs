/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026.
Released under Apache 2.0 license.
-/

import ErdosProblems.Erdos438.Basic
import ErdosProblems.Erdos438.Fourier
import ErdosProblems.Erdos438.QuadraticWeyl
import Mathlib.NumberTheory.Chebyshev

/-!
# Erdős Problem 438: the KLS shifting count

This file isolates the count used in the harmonic-analytic shifting lemma
of Khalfalah--Lodha--Szemerédi.  The count is deliberately expressed using
ordered pairs of elements of the original set.  Thus diagonal pairs are
retained, exactly as required by the literal sumset `A + A` formulation of
Problem 438.
-/

namespace Erdos438

open Filter
open scoped BigOperators

/-- The translation modulus in the KLS shifting argument.  Every positive
integer at most `P` divides its second factor. -/
def shiftModulus (C P : ℕ) : ℕ := C * Nat.lcmUpto P

theorem shiftModulus_pos {C P : ℕ} (hC : 0 < C) :
    0 < shiftModulus C P := by
  exact Nat.mul_pos hC (Nat.lcmUpto_pos P)

theorem dvd_shiftModulus {C P b : ℕ} (hb : b ∈ Finset.Icc 1 P) :
    b ∣ shiftModulus C P := by
  exact dvd_mul_of_dvd_right (Finset.dvd_lcm (f := id) hb) C

/-- Number of ordered pairs `(x,y) ∈ A × A` for which
`x + (y + d)` is a square.  A square has a unique natural square root, so
this is also the number of triples `(x,y,z)` occurring in the KLS paper. -/
def shiftedSquarePairCount (A : Finset ℕ) (d : ℕ) : ℕ :=
  ((A.product A).filter fun p => IsSquare (p.1 + p.2 + d)).card

@[simp] theorem mem_shiftedSquarePairs {A : Finset ℕ} {d : ℕ}
    {p : ℕ × ℕ} :
    p ∈ ((A.product A).filter fun q => IsSquare (q.1 + q.2 + d)) ↔
      p.1 ∈ A ∧ p.2 ∈ A ∧ IsSquare (p.1 + p.2 + d) := by
  rcases p with ⟨x, y⟩
  simp only [Finset.mem_filter]
  rw [show (x, y) ∈ A.product A ↔ x ∈ A ∧ y ∈ A from
    Finset.mem_product]
  tauto

theorem shiftedSquarePairCount_le (A : Finset ℕ) (d : ℕ) :
    shiftedSquarePairCount A d ≤ A.card ^ 2 := by
  calc
    shiftedSquarePairCount A d ≤ (A.product A).card :=
      Finset.card_filter_le _ _
    _ = A.card ^ 2 := by simp [pow_two]

@[simp] theorem shiftedSquarePairCount_zero_of_squareSumFree
    {A : Finset ℕ} (hA : SquareSumFree A) :
    shiftedSquarePairCount A 0 = 0 := by
  rw [shiftedSquarePairCount, Finset.card_eq_zero]
  simp only [Finset.filter_eq_empty_iff]
  rintro ⟨x, y⟩ hp hsq
  have hp' := Finset.mem_product.mp hp
  exact hA x hp'.1 y hp'.2 (by simpa using hsq)

theorem squareSumFree_iff_shiftedSquarePairCount_zero {A : Finset ℕ} :
    SquareSumFree A ↔ shiftedSquarePairCount A 0 = 0 := by
  constructor
  · exact shiftedSquarePairCount_zero_of_squareSumFree
  · intro hzero a ha b hb hs
    rw [shiftedSquarePairCount, Finset.card_eq_zero] at hzero
    have hp : (a, b) ∈
        ((A.product A).filter fun p => IsSquare (p.1 + p.2 + 0)) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨ha, hb⟩, by simpa using hs⟩
    rw [hzero] at hp
    simp at hp

/-- The sum of the shifted square-pair counts over `0 ≤ j ≤ h`. -/
def totalShiftedSquarePairCount (A : Finset ℕ) (M h : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (h + 1), shiftedSquarePairCount A (j * M)

theorem totalShiftedSquarePairCount_le_of_pointwise
    {A : Finset ℕ} {M h B : ℕ}
    (hB : ∀ j ≤ h, shiftedSquarePairCount A (j * M) ≤ B) :
    totalShiftedSquarePairCount A M h ≤ (h + 1) * B := by
  rw [totalShiftedSquarePairCount]
  calc
    (∑ j ∈ Finset.range (h + 1), shiftedSquarePairCount A (j * M)) ≤
        ∑ _j ∈ Finset.range (h + 1), B := by
      apply Finset.sum_le_sum
      intro j hj
      exact hB j (by simpa using Finset.mem_range.mp hj)
    _ = (h + 1) * B := by simp

theorem totalShiftedSquarePairCount_cast_le_of_pointwise
    {A : Finset ℕ} {M h : ℕ} {B : ℝ}
    (hB : ∀ j ≤ h, (shiftedSquarePairCount A (j * M) : ℝ) ≤ B) :
    (totalShiftedSquarePairCount A M h : ℝ) ≤ (h + 1 : ℕ) * B := by
  rw [totalShiftedSquarePairCount, Nat.cast_sum]
  calc
    (∑ j ∈ Finset.range (h + 1), (shiftedSquarePairCount A (j * M) : ℝ)) ≤
        ∑ _j ∈ Finset.range (h + 1), B := by
      apply Finset.sum_le_sum
      intro j hj
      exact hB j (by simpa using Finset.mem_range.mp hj)
    _ = (h + 1 : ℕ) * B := by simp

/-- A KLS-sized translation is eventually smaller than the ambient
interval.  This is the no-wrap estimate behind the choice of Fourier modulus
`4N`. -/
theorem eventually_shift_lt (η : ℝ) (hη : 0 < η) (M : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ j : ℕ, (j : ℝ) ≤ (N : ℝ) ^ (1 - 2 * η) → j * M < N := by
  have hpow : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (2 * η))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (mul_pos (by norm_num) hη)).comp
      tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop,
      (M : ℝ) < (N : ℝ) ^ (2 * η) :=
    hpow.eventually (eventually_gt_atTop (M : ℝ))
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℕ)] with N hNM hN
  intro j hj
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hbase : 0 < (N : ℝ) ^ (1 - 2 * η) :=
    Real.rpow_pos_of_pos hNreal _
  have hcast : (j * M : ℕ) < (N : ℝ) := by
    calc
      (j * M : ℕ) = (j : ℝ) * (M : ℝ) := by norm_num
      _ ≤ (N : ℝ) ^ (1 - 2 * η) * (M : ℝ) :=
        mul_le_mul_of_nonneg_right hj (Nat.cast_nonneg M)
      _ < (N : ℝ) ^ (1 - 2 * η) * (N : ℝ) ^ (2 * η) :=
        mul_lt_mul_of_pos_left hNM hbase
      _ = (N : ℝ) := by
        rw [← Real.rpow_add hNreal]
        convert Real.rpow_one (N : ℝ) using 2 <;> ring
  exact_mod_cast hcast

/-- A fixed constant times `N⁻η` is eventually smaller than the minor-arc
scale `P⁻¹/²`. -/
theorem eventually_const_mul_rpow_neg_le_inv_sqrt
    (η C : ℝ) (hη : 0 < η) (hC : 0 ≤ C) (P : ℕ) (hP : 0 < P) :
    ∀ᶠ N : ℕ in Filter.atTop,
      C * (N : ℝ) ^ (-η) ≤ 1 / Real.sqrt (P : ℝ) := by
  have hpow : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ η)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop,
      C * Real.sqrt (P : ℝ) < (N : ℝ) ^ η :=
    hpow.eventually (eventually_gt_atTop (C * Real.sqrt (P : ℝ)))
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℕ)] with N hlargeN hN
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hpowPos : 0 < (N : ℝ) ^ η := Real.rpow_pos_of_pos hNreal _
  have hsqrtPos : 0 < Real.sqrt (P : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hP)
  rw [Real.rpow_neg hNreal.le, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ hpowPos hsqrtPos).2 (by simpa using hlargeN.le)

theorem eventually_half_rpow_le_dirichletCutoff :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 2 : ℝ) * (N : ℝ) ^ ((15 : ℝ) / 16) ≤
        QuadraticWeyl.dirichletCutoff N := by
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop,
      (2 : ℝ) ≤ (N : ℝ) ^ ((15 : ℝ) / 16) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (15 : ℝ) / 16)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge] with N hN
  have hfloor := Nat.sub_one_lt_floor
    ((N : ℝ) ^ ((15 : ℝ) / 16))
  change (1 / 2 : ℝ) * (N : ℝ) ^ ((15 : ℝ) / 16) ≤
    (QuadraticWeyl.dirichletCutoff N : ℝ)
  rw [QuadraticWeyl.dirichletCutoff]
  exact le_of_lt (lt_of_le_of_lt (by nlinarith) hfloor)

/-- Fully quantified statement of the analytic KLS shifting lemma.  The
constant `K` is absolute: it is chosen before `η`, the fixed translation
modulus, and the denominator threshold. -/
def KLSShiftingStatement : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ η : ℝ, 0 < η → η < (1 : ℝ) / 10 →
    ∀ C P : ℕ, 0 < C → 0 < P →
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → SquareSumFree A →
          ∀ j : ℕ, (j : ℝ) ≤ (N : ℝ) ^ (1 - 2 * η) →
            (shiftedSquarePairCount A (j * shiftModulus C P) : ℝ) ≤
              K * (N : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (P : ℝ)

/-- The shorter shift range used in the final residue-class assembly. -/
def klsShortShiftCutoff (M N : ℕ) : ℕ :=
  4 * Nat.sqrt (2 * N) + 2 * M + 4

/-- Number of square roots used in the no-wrap DFT. -/
def squareRootCutoff (N : ℕ) : ℕ := 2 * Nat.sqrt N + 2

theorem squareRootCutoff_cast_le_four_sqrt {N : ℕ} (hN : 1 ≤ N) :
    (squareRootCutoff N : ℝ) ≤ 4 * Real.sqrt (N : ℝ) := by
  have hsqrtNat : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN
  simp only [squareRootCutoff, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  linarith

/-- A square Fourier modulus strictly larger than `3N`. -/
def shiftingFourierModulus (N : ℕ) : ℕ := squareRootCutoff N ^ 2

/-- Squares represented by roots below `squareRootCutoff N`. -/
def shiftingSquares (N : ℕ) : Finset ℕ :=
  (Finset.range (squareRootCutoff N)).image fun z => z ^ 2

theorem three_mul_lt_shiftingFourierModulus (N : ℕ) :
    3 * N < shiftingFourierModulus N := by
  have hsqrt := Nat.lt_succ_sqrt' N
  simp only [shiftingFourierModulus, squareRootCutoff]
  nlinarith [sq_nonneg (Nat.sqrt N + 1)]

theorem shifting_noWrap {N d : ℕ} (hN : 0 < N) (hd : d < N)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) :
    ∀ x ∈ A, ∀ y ∈ A, x + y + d < shiftingFourierModulus N := by
  intro x hx y hy
  have hxN := (Finset.mem_Icc.mp (hA hx)).2
  have hyN := (Finset.mem_Icc.mp (hA hy)).2
  have hsum : x + y + d < 3 * N := by omega
  exact hsum.trans (three_mul_lt_shiftingFourierModulus N)

/-- The roots chosen for the DFT enumerate exactly the squares below its
square modulus. -/
theorem shiftingSquares_eq_squaresBelow (N : ℕ) :
    shiftingSquares N = Fourier.squaresBelow (shiftingFourierModulus N) := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨z, hz, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, ⟨z, by simp [pow_two]⟩⟩
    have hzlt := Finset.mem_range.mp hz
    simp only [shiftingFourierModulus]
    exact Nat.pow_lt_pow_left hzlt (by norm_num)
  · intro hn
    have hn' := Finset.mem_filter.mp hn
    rcases hn'.2 with ⟨z, hz⟩
    have hzpow : n = z ^ 2 := by simpa [pow_two] using hz
    have hzlt : z < squareRootCutoff N := by
      by_contra hnot
      have hle : squareRootCutoff N ≤ z := Nat.le_of_not_gt hnot
      have hp : squareRootCutoff N ^ 2 ≤ z ^ 2 :=
        Nat.pow_le_pow_left hle 2
      rw [← hzpow] at hp
      exact (Nat.not_lt_of_ge hp) (by
        simpa [shiftingFourierModulus] using Finset.mem_range.mp hn'.1)
    apply Finset.mem_image.mpr
    exact ⟨z, Finset.mem_range.mpr hzlt, hzpow.symm⟩

@[simp] theorem card_shiftingSquares (N : ℕ) :
    (shiftingSquares N).card = squareRootCutoff N := by
  calc
    (shiftingSquares N).card =
        (Finset.range (squareRootCutoff N)).card := by
      apply Finset.card_image_of_injective
      intro z w hzw
      nlinarith
    _ = squareRootCutoff N := Finset.card_range _

/-- The square-set Fourier coefficient is the quadratic exponential sum
estimated by `QuadraticWeyl`. -/
theorem coefficient_shiftingSquares_neg (N t : ℕ) :
    Fourier.coefficient (shiftingFourierModulus N) (shiftingSquares N)
        (-(t : ℤ)) =
      QuadraticWeyl.squareExpSum
        (-((t : ℝ) / shiftingFourierModulus N)) (squareRootCutoff N) := by
  classical
  rw [Fourier.coefficient, shiftingSquares, Finset.sum_image,
    QuadraticWeyl.squareExpSum, Erdos587.quadraticSum]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [Fourier.phase, Erdos587.phase, Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  · intro z _hz w _hw hzw
    nlinarith

theorem norm_squareExpSum_neg (θ : ℝ) (L : ℕ) :
    ‖QuadraticWeyl.squareExpSum (-θ) L‖ =
      ‖QuadraticWeyl.squareExpSum θ L‖ := by
  have heq : QuadraticWeyl.squareExpSum (-θ) L =
      starRingEnd ℂ (QuadraticWeyl.squareExpSum θ L) := by
    rw [QuadraticWeyl.squareExpSum, QuadraticWeyl.squareExpSum,
      Erdos587.quadraticSum, Erdos587.quadraticSum, map_sum]
    apply Finset.sum_congr rfl
    intro z hz
    simp only [zero_mul, add_zero]
    convert Erdos587.phase_neg (θ * (z : ℝ) ^ 2) using 1 <;> ring_nf
  rw [heq, Complex.norm_conj]

theorem fourier_phase_nat_eq_phase (T t x : ℕ) :
    Fourier.phase T (t : ℤ) (x : ℤ) =
      Erdos587.phase (((t : ℝ) / T) * x) := by
  rw [Fourier.phase, Erdos587.phase, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- A translation divisible by the approximating denominator has almost
trivial phase; only the Dirichlet approximation error remains. -/
theorem norm_phase_mul_sub_one_le_of_approx
    (θ : ℝ) (a : ℤ) (b Q d : ℕ) (hb : 0 < b) (hQ : 0 < Q)
    (hbd : b ∣ d)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    ‖Erdos587.phase (θ * d) - 1‖ ≤
      2 * Real.pi * d / ((b : ℝ) * Q) := by
  obtain ⟨k, rfl⟩ := hbd
  have hsplit : θ * (b * k : ℕ) =
      ((a * k : ℤ) : ℝ) + (θ - (a : ℝ) / b) * (b * k : ℕ) := by
    have hbR : (b : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hbR]
    ring
  rw [hsplit, Erdos587.phase_add, Erdos587.phase]
  rw [Erdos587.fourierChar_intCast, one_mul, Erdos587.phase,
    Real.fourierChar_apply]
  calc
    ‖Complex.exp
          (↑(2 * Real.pi *
            ((θ - (a : ℝ) / b) * (b * k : ℕ))) * Complex.I) - 1‖ ≤
        ‖2 * Real.pi * ((θ - (a : ℝ) / b) * (b * k : ℕ))‖ := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le
          (x := 2 * Real.pi *
            ((θ - (a : ℝ) / b) * (b * k : ℕ))))
    _ = 2 * Real.pi * (b * k : ℕ) * |θ - (a : ℝ) / b| := by
      have h2 : |(2 : ℝ)| = 2 := abs_of_nonneg (by norm_num)
      have hpi : |Real.pi| = Real.pi := abs_of_pos Real.pi_pos
      have hbk : |((b * k : ℕ) : ℝ)| = (b * k : ℕ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, h2, hpi, hbk]
      ring
    _ ≤ 2 * Real.pi * (b * k : ℕ) *
        (1 / ((b : ℝ) * Q)) := by
      gcongr
    _ = 2 * Real.pi * (b * k : ℕ) / ((b : ℝ) * Q) := by ring

theorem eventually_klsShortShiftCutoff_le_rpow (M : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (klsShortShiftCutoff M N : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) := by
  let D : ℝ := 4 * Real.sqrt 2 + 2 * M + 4
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hpow : Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ ((3 : ℝ) / 8))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 8)).comp
      tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop,
      D < (N : ℝ) ^ ((3 : ℝ) / 8) :=
    hpow.eventually (eventually_gt_atTop D)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hlargeN hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hhalfPos : 0 < (N : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hNreal) _
  have honeHalf : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.one_le_rpow hNreal (by norm_num)
  have hsqrtNat : (Nat.sqrt (2 * N) : ℝ) ≤
      Real.sqrt (2 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
    calc
      (Nat.sqrt (2 * N) : ℝ) ≤ Real.sqrt ((2 * N : ℕ) : ℝ) :=
        Real.nat_sqrt_le_real_sqrt
      _ = Real.sqrt (2 : ℝ) * Real.sqrt (N : ℝ) := by
        rw [Nat.cast_mul]
        exact Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
      _ = Real.sqrt (2 : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow (N : ℝ)]
  calc
    (klsShortShiftCutoff M N : ℝ) =
        4 * (Nat.sqrt (2 * N) : ℝ) + 2 * (M : ℝ) + 4 := by
      norm_num [klsShortShiftCutoff]
    _ ≤ 4 * (Real.sqrt 2 * (N : ℝ) ^ ((1 : ℝ) / 2)) +
        2 * (M : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) +
        4 * (N : ℝ) ^ ((1 : ℝ) / 2) := by
      have hroot := mul_le_mul_of_nonneg_left hsqrtNat (by norm_num : (0 : ℝ) ≤ 4)
      have hMterm : 2 * (M : ℝ) ≤
          2 * (M : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * M by positivity)
          (sub_nonneg.mpr honeHalf)]
      have h4term : (4 : ℝ) ≤ 4 * (N : ℝ) ^ ((1 : ℝ) / 2) := by
        nlinarith
      linarith
    _ = D * (N : ℝ) ^ ((1 : ℝ) / 2) := by
      dsimp [D]
      ring
    _ ≤ (N : ℝ) ^ ((3 : ℝ) / 8) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hlargeN.le hhalfPos.le
    _ = (N : ℝ) ^ ((7 : ℝ) / 8) := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hNreal)]
      congr 1
      norm_num

/-- The form of the shifting estimate consumed by the final KLS assembly. -/
def KLSShortShiftingStatement : Prop :=
  ∃ K : ℝ, 0 < K ∧
    ∀ C P : ℕ, 0 < C → 0 < P →
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → SquareSumFree A →
          ∀ j ≤ klsShortShiftCutoff (shiftModulus C P) N,
            (shiftedSquarePairCount A (j * shiftModulus C P) : ℝ) ≤
              K * (N : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (P : ℝ)

theorem KLSShiftingStatement.short (h : KLSShiftingStatement) :
    KLSShortShiftingStatement := by
  rcases h with ⟨K, hK, hshift⟩
  refine ⟨K, hK, ?_⟩
  intro C P hC hP
  have hpoint := hshift ((1 : ℝ) / 16) (by norm_num) (by norm_num) C P hC hP
  filter_upwards [hpoint,
    eventually_klsShortShiftCutoff_le_rpow (shiftModulus C P)] with N hpointN hcut
  intro A hA hfree j hj
  apply hpointN A hA hfree j
  have hj' : (j : ℝ) ≤
      (klsShortShiftCutoff (shiftModulus C P) N : ℝ) := by
    exact_mod_cast hj
  have hexp : (1 : ℝ) - 2 * ((1 : ℝ) / 16) = (7 : ℝ) / 8 := by
    norm_num
  rw [hexp]
  exact hj'.trans hcut

/-- The translated second copy of a finite set. -/
def translate (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  A.image fun y => y + d

/-- The square numbers in the no-wrap Fourier interval `[0,T)`. -/
def squareValuesBelow (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter IsSquare

@[simp] theorem mem_squareValuesBelow {T n : ℕ} :
    n ∈ squareValuesBelow T ↔ n < T ∧ IsSquare n := by
  simp [squareValuesBelow]

@[simp] theorem mem_translate {A : Finset ℕ} {d y : ℕ} :
    y ∈ translate A d ↔ ∃ x ∈ A, x + d = y := by
  simp [translate]

theorem card_translate (A : Finset ℕ) (d : ℕ) :
    (translate A d).card = A.card := by
  rw [translate, Finset.card_image_iff.mpr]
  exact fun _ _ _ _ h => Nat.add_right_cancel h

/-- Fourier translation is multiplication by the corresponding character.
This exact identity is the algebraic heart of the major-arc comparison. -/
theorem coefficient_translate (T : ℕ) (A : Finset ℕ) (d : ℕ) (t : ℤ) :
    Fourier.coefficient T (translate A d) t =
      Fourier.coefficient T A t * Fourier.phase T t d := by
  classical
  rw [Fourier.coefficient, translate, Finset.sum_image]
  · push_cast
    simp_rw [Fourier.phase_add_right]
    rw [Fourier.coefficient, Finset.sum_mul]
  · intro x _hx y _hy hxy
    exact Nat.add_right_cancel hxy

theorem norm_coefficient_le_card (T : ℕ) (S : Finset ℕ) (t : ℤ) :
    ‖Fourier.coefficient T S t‖ ≤ S.card := by
  calc
    ‖Fourier.coefficient T S t‖ ≤
        ∑ x ∈ S, ‖Fourier.phase T t (x : ℤ)‖ := by
      exact norm_sum_le _ _
    _ = S.card := by simp [Fourier.norm_phase]

/-- Counting with the translated set is equivalent to the ordered-pair
count above.  This is the finite-set version of the notation `A + jM` in
the source paper. -/
theorem shiftedSquarePairCount_eq_translated
    (A : Finset ℕ) (d : ℕ) :
    shiftedSquarePairCount A d =
      ((A.product (translate A d)).filter fun p => IsSquare (p.1 + p.2)).card := by
  classical
  rw [shiftedSquarePairCount]
  apply Finset.card_bij (fun p _hp => (p.1, p.2 + d))
  · rintro ⟨x, y⟩ hp
    have hp' := Finset.mem_filter.mp hp
    have hpProd := Finset.mem_product.mp hp'.1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hpProd.1, ?_⟩, ?_⟩
    · exact mem_translate.mpr ⟨y, hpProd.2, rfl⟩
    · simpa [Nat.add_assoc] using hp'.2
  · rintro ⟨x₁, y₁⟩ _ ⟨x₂, y₂⟩ _ h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨h.1, Nat.add_right_cancel h.2⟩
  · rintro ⟨x, y⟩ hp
    have hp' := Finset.mem_filter.mp hp
    have hpProd := Finset.mem_product.mp hp'.1
    rcases mem_translate.mp hpProd.2 with ⟨y₀, hy₀, hy⟩
    refine ⟨(x, y₀), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hpProd.1, hy₀⟩, ?_⟩
      simpa [hy, Nat.add_assoc] using hp'.2
    · exact Prod.ext rfl hy

theorem shiftedSquarePairCount_eq_squareValuesBelow
    {A : Finset ℕ} {d T : ℕ}
    (hnoWrap : ∀ x ∈ A, ∀ y ∈ A, x + y + d < T) :
    shiftedSquarePairCount A d =
      ((A.product (translate A d)).filter fun p =>
        p.1 + p.2 ∈ squareValuesBelow T).card := by
  rw [shiftedSquarePairCount_eq_translated]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · intro hp
    refine ⟨hp.1, ?_⟩
    rcases Finset.mem_product.mp hp.1 with ⟨hx, hy⟩
    rcases mem_translate.mp hy with ⟨y, hyA, hyEq⟩
    apply mem_squareValuesBelow.mpr
    refine ⟨?_, hp.2⟩
    rw [← hyEq]
    simpa [Nat.add_assoc] using hnoWrap p.1 hx y hyA
  · intro hp
    exact ⟨hp.1, (mem_squareValuesBelow.mp hp.2).2⟩

theorem squarePairCount_eq_shiftedSquarePairCount
    {A : Finset ℕ} {d T : ℕ}
    (hnoWrap : ∀ x ∈ A, ∀ y ∈ A, x + y + d < T) :
    Fourier.squarePairCount T A (translate A d) =
      (shiftedSquarePairCount A d : ℂ) := by
  classical
  rw [Fourier.squarePairCount, Fourier.pairSumCount]
  have hrewrite :
      (∑ x ∈ A, ∑ y ∈ translate A d,
          if x + y ∈ Fourier.squaresBelow T then (1 : ℂ) else 0) =
        ∑ p ∈ A.product (translate A d),
          if p.1 + p.2 ∈ Fourier.squaresBelow T then (1 : ℂ) else 0 := by
    exact (Finset.sum_product A (translate A d)
      (fun p => if p.1 + p.2 ∈ Fourier.squaresBelow T then (1 : ℂ) else 0)).symm
  rw [hrewrite, Finset.sum_boole]
  change (((A.product (translate A d)).filter fun p =>
      p.1 + p.2 ∈ squareValuesBelow T).card : ℂ) = _
  rw [← shiftedSquarePairCount_eq_squareValuesBelow hnoWrap]

/-- A finite, quantitative major/minor-arc splitting lemma.  It contains no
asymptotics: callers supply a pointwise square-coefficient bound on `U` and
a translation-phase bound on its complement. -/
theorem shiftedSquarePairCount_le_of_fourier_partition
    {N d : ℕ} (hN : 0 < N) (hd : d < N)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N) (hfree : SquareSumFree A)
    (U : Finset ℕ)
    (hU : U ⊆ Finset.range (shiftingFourierModulus N))
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hminor : ∀ t ∈ U,
      ‖Fourier.coefficient (shiftingFourierModulus N) (shiftingSquares N)
        (-(t : ℤ))‖ ≤ B)
    (hmajor : ∀ t ∈ Finset.range (shiftingFourierModulus N), t ∉ U →
      ‖Fourier.phase (shiftingFourierModulus N) (t : ℤ) (d : ℤ) - 1‖ ≤ ε) :
    (shiftedSquarePairCount A d : ℝ) ≤
      2 * B * A.card + ε * squareRootCutoff N * A.card := by
  classical
  let T := shiftingFourierModulus N
  let L := squareRootCutoff N
  have hTpos : 0 < T := by
    dsimp [T]
    exact lt_of_le_of_lt (Nat.zero_le _) (three_mul_lt_shiftingFourierModulus N)
  let : NeZero T := ⟨Nat.ne_of_gt hTpos⟩
  have hno := shifting_noWrap hN hd hA
  have hXY : ∀ x ∈ A, ∀ y ∈ translate A d, x + y < T := by
    intro x hx y hy
    rcases mem_translate.mp hy with ⟨y₀, hy₀, rfl⟩
    simpa [T, Nat.add_assoc] using hno x hx y₀ hy₀
  have htwoN : 2 * N < T := by
    have hthree := three_mul_lt_shiftingFourierModulus N
    dsimp [T]
    omega
  have hA_range : A ⊆ Finset.range T := by
    intro x hx
    have hxN := (Finset.mem_Icc.mp (hA hx)).2
    exact Finset.mem_range.mpr (by omega)
  have htranslate_range : translate A d ⊆ Finset.range T := by
    intro y hy
    rcases mem_translate.mp hy with ⟨x, hx, rfl⟩
    have hxN := (Finset.mem_Icc.mp (hA hx)).2
    exact Finset.mem_range.mpr (by omega)
  let F : ℕ → ℂ := fun t => Fourier.coefficient T A (t : ℤ)
  let G : ℕ → ℂ := fun t =>
    Fourier.coefficient T (translate A d) (t : ℤ)
  let H : ℕ → ℂ := fun t =>
    Fourier.coefficient T (Fourier.squaresBelow T) (-(t : ℤ))
  let D : ℕ → ℂ := fun t => F t * G t * H t
  let D₀ : ℕ → ℂ := fun t => F t * F t * H t
  have hdft : (T : ℂ) * (shiftedSquarePairCount A d : ℂ) =
      ∑ t ∈ Finset.range T, D t := by
    have h := Fourier.squarePairCount_eq_fourier T A (translate A d) hXY
    rw [squarePairCount_eq_shiftedSquarePairCount hno] at h
    simpa [F, G, H, D] using h
  have hno0 : ∀ x ∈ A, ∀ y ∈ A, x + y + 0 < T := by
    intro x hx y hy
    have hxN := (Finset.mem_Icc.mp (hA hx)).2
    have hyN := (Finset.mem_Icc.mp (hA hy)).2
    omega
  have hdft0 : (∑ t ∈ Finset.range T, D₀ t) = 0 := by
    have h := Fourier.squarePairCount_eq_fourier T A A
      (fun x hx y hy => by simpa using hno0 x hx y hy)
    have htranslate0 : translate A 0 = A := by
      ext x
      simp [translate]
    have hsquare0 := squarePairCount_eq_shiftedSquarePairCount hno0
    rw [htranslate0] at hsquare0
    rw [hsquare0,
      shiftedSquarePairCount_zero_of_squareSumFree hfree, Nat.cast_zero,
      mul_zero] at h
    simpa [F, H, D₀] using h.symm
  have hparsevalF : (∑ t ∈ Finset.range T, ‖F t‖ ^ 2) =
      (T : ℝ) * A.card := by
    simpa [F] using Fourier.parseval_coefficient T A hA_range
  have hparsevalG : (∑ t ∈ Finset.range T, ‖G t‖ ^ 2) =
      (T : ℝ) * A.card := by
    simpa [G, card_translate] using
      Fourier.parseval_coefficient T (translate A d) htranslate_range
  have hminorD : ‖∑ t ∈ U, D t‖ ≤ B * (T : ℝ) * A.card := by
    have hraw := Fourier.minorArc_cauchy_bound U F G H B hB
      (fun t ht => by
        simpa [H, T, shiftingSquares_eq_squaresBelow] using hminor t ht)
    refine hraw.trans ?_
    have hFU : (∑ t ∈ U, ‖F t‖ ^ 2) ≤ (T : ℝ) * A.card := by
      rw [← hparsevalF]
      exact Finset.sum_le_sum_of_subset_of_nonneg hU
        (fun _ _ _ => sq_nonneg _)
    have hGU : (∑ t ∈ U, ‖G t‖ ^ 2) ≤ (T : ℝ) * A.card := by
      rw [← hparsevalG]
      exact Finset.sum_le_sum_of_subset_of_nonneg hU
        (fun _ _ _ => sq_nonneg _)
    have hTC : 0 ≤ (T : ℝ) * A.card := by positivity
    calc
      B * Real.sqrt (∑ t ∈ U, ‖F t‖ ^ 2) *
          Real.sqrt (∑ t ∈ U, ‖G t‖ ^ 2) ≤
          B * Real.sqrt ((T : ℝ) * A.card) *
            Real.sqrt ((T : ℝ) * A.card) := by gcongr
      _ = B * ((T : ℝ) * A.card) := by
        rw [mul_assoc, Real.mul_self_sqrt hTC]
      _ = B * (T : ℝ) * A.card := by ring
  have hminorD₀ : ‖∑ t ∈ U, D₀ t‖ ≤ B * (T : ℝ) * A.card := by
    have hraw := Fourier.minorArc_cauchy_bound U F F H B hB
      (fun t ht => by
        simpa [H, T, shiftingSquares_eq_squaresBelow] using hminor t ht)
    refine hraw.trans ?_
    have hFU : (∑ t ∈ U, ‖F t‖ ^ 2) ≤ (T : ℝ) * A.card := by
      rw [← hparsevalF]
      exact Finset.sum_le_sum_of_subset_of_nonneg hU
        (fun _ _ _ => sq_nonneg _)
    have hTC : 0 ≤ (T : ℝ) * A.card := by positivity
    calc
      B * Real.sqrt (∑ t ∈ U, ‖F t‖ ^ 2) *
          Real.sqrt (∑ t ∈ U, ‖F t‖ ^ 2) ≤
          B * Real.sqrt ((T : ℝ) * A.card) *
            Real.sqrt ((T : ℝ) * A.card) := by gcongr
      _ = B * ((T : ℝ) * A.card) := by
        rw [mul_assoc, Real.mul_self_sqrt hTC]
      _ = B * (T : ℝ) * A.card := by ring
  have hmajorDiff :
      ‖∑ t ∈ Finset.range T \ U, (D t - D₀ t)‖ ≤
        ε * L * ((T : ℝ) * A.card) := by
    calc
      ‖∑ t ∈ Finset.range T \ U, (D t - D₀ t)‖ ≤
          ∑ t ∈ Finset.range T \ U, ‖D t - D₀ t‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ Finset.range T \ U, ε * L * ‖F t‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro t ht
        have htRange := (Finset.mem_sdiff.mp ht).1
        have htNot := (Finset.mem_sdiff.mp ht).2
        have hphase := hmajor t (by simpa [T] using htRange) htNot
        have hHbound : ‖H t‖ ≤ L := by
          have hh := norm_coefficient_le_card T (shiftingSquares N) (-(t : ℤ))
          rw [card_shiftingSquares] at hh
          simpa [H, T, L, shiftingSquares_eq_squaresBelow] using hh
        dsimp [D, D₀, G]
        rw [coefficient_translate]
        have halg :
            F t * (F t * Fourier.phase T (t : ℤ) (d : ℤ)) * H t -
                F t * F t * H t =
              F t * F t * H t *
                (Fourier.phase T (t : ℤ) (d : ℤ) - 1) := by ring
        rw [halg, norm_mul, norm_mul, norm_mul]
        calc
          ‖F t‖ * ‖F t‖ * ‖H t‖ *
              ‖Fourier.phase T (t : ℤ) (d : ℤ) - 1‖ ≤
              ‖F t‖ * ‖F t‖ * L * ε := by gcongr
          _ = ε * L * ‖F t‖ ^ 2 := by ring
      _ ≤ ∑ t ∈ Finset.range T, ε * L * ‖F t‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
        intro t ht _
        positivity
      _ = ε * L * ((T : ℝ) * A.card) := by
        rw [← Finset.mul_sum, hparsevalF]
  have htotal :
      ‖∑ t ∈ Finset.range T, D t - ∑ t ∈ Finset.range T, D₀ t‖ ≤
        2 * B * (T : ℝ) * A.card + ε * L * ((T : ℝ) * A.card) := by
    have hsplitD := Finset.sum_sdiff hU (f := D)
    have hsplitD₀ := Finset.sum_sdiff hU (f := D₀)
    calc
      ‖∑ t ∈ Finset.range T, D t - ∑ t ∈ Finset.range T, D₀ t‖ =
          ‖((∑ t ∈ U, D t) - ∑ t ∈ U, D₀ t) +
            ∑ t ∈ Finset.range T \ U, (D t - D₀ t)‖ := by
        rw [Finset.sum_sub_distrib]
        congr 1
        rw [← hsplitD, ← hsplitD₀]
        ring
      _ ≤ ‖(∑ t ∈ U, D t) - ∑ t ∈ U, D₀ t‖ +
          ‖∑ t ∈ Finset.range T \ U, (D t - D₀ t)‖ := norm_add_le _ _
      _ ≤ (B * (T : ℝ) * A.card + B * (T : ℝ) * A.card) +
          ε * L * ((T : ℝ) * A.card) :=
        add_le_add (norm_sub_le _ _ |>.trans (add_le_add hminorD hminorD₀))
          hmajorDiff
      _ = 2 * B * (T : ℝ) * A.card +
          ε * L * ((T : ℝ) * A.card) := by ring
  have hcount : (T : ℝ) * shiftedSquarePairCount A d ≤
      2 * B * (T : ℝ) * A.card + ε * L * ((T : ℝ) * A.card) := by
    have hnorm := htotal
    rw [hdft0, sub_zero, ← hdft, norm_mul, Complex.norm_natCast,
      Complex.norm_natCast] at hnorm
    simpa using hnorm
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
  dsimp [L] at hcount ⊢
  nlinarith

/-- The unconditional short-range KLS shifting estimate.  The constant is
absolute; the dependence on the fixed modulus and denominator threshold is
confined to how far out the eventual statement starts. -/
theorem klsShortShiftingStatement : KLSShortShiftingStatement := by
  refine ⟨16, by norm_num, ?_⟩
  intro C P hC hP
  let M := shiftModulus C P
  have hMinor := QuadraticWeyl.eventually_norm_squareExpSum_le_minor_int P hP
  have hCut := eventually_klsShortShiftCutoff_le_rpow M
  have hShift := eventually_shift_lt ((1 : ℝ) / 16) (by norm_num) M
  have hQlower := eventually_half_rpow_le_dirichletCutoff
  have hPhase := eventually_const_mul_rpow_neg_le_inv_sqrt
    ((1 : ℝ) / 16) (4 * Real.pi * M) (by norm_num) (by positivity) P hP
  filter_upwards [hMinor, hCut, hShift, hQlower, hPhase,
      eventually_ge_atTop (1 : ℕ)] with N hMinorN hCutN hShiftN hQlowerN
        hPhaseN hN
  intro A hA hfree j hj
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hjReal : (j : ℝ) ≤
      (klsShortShiftCutoff M N : ℝ) := by exact_mod_cast hj
  have hjPow : (j : ℝ) ≤ (N : ℝ) ^ ((7 : ℝ) / 8) :=
    hjReal.trans hCutN
  have hExponent : (1 : ℝ) - 2 * ((1 : ℝ) / 16) = (7 : ℝ) / 8 := by
    norm_num
  have hd : j * M < N := by
    apply hShiftN j
    simpa only [hExponent] using hjPow
  let T := shiftingFourierModulus N
  let Q := QuadraticWeyl.dirichletCutoff N
  have hQposR : (0 : ℝ) < Q := by
    have hpowpos : 0 < (1 / 2 : ℝ) *
        (N : ℝ) ^ ((15 : ℝ) / 16) := by positivity
    exact hpowpos.trans_le (by simpa [Q] using hQlowerN)
  have hQone : 1 ≤ Q := by
    exact_mod_cast (show (1 : ℝ) ≤ Q by
      have hQnat : (0 : ℕ) < Q := by exact_mod_cast hQposR
      exact_mod_cast hQnat)
  choose a b hb1 hbQ hcop happrox using fun t : ℕ =>
    QuadraticWeyl.dirichletApproximationReduced ((t : ℝ) / T) Q hQone
  let U := (Finset.range T).filter fun t => P ≤ b t
  have hU : U ⊆ Finset.range T := Finset.filter_subset _ _
  have hminorCoeff : ∀ t ∈ U,
      ‖Fourier.coefficient T (shiftingSquares N) (-(t : ℤ))‖ ≤
        6 * Real.sqrt ((N : ℝ) / P) := by
    intro t ht
    have hPt : P ≤ b t := (Finset.mem_filter.mp ht).2
    rw [show T = shiftingFourierModulus N by rfl,
      coefficient_shiftingSquares_neg, norm_squareExpSum_neg]
    simpa [Q, QuadraticWeyl.squareRootLength, squareRootCutoff] using
      hMinorN ((t : ℝ) / T) (a t) (b t) hPt (hbQ t) (hcop t) (happrox t)
  have hmajorPhase : ∀ t ∈ Finset.range T, t ∉ U →
      ‖Fourier.phase T (t : ℤ) ((j * M : ℕ) : ℤ) - 1‖ ≤
        1 / Real.sqrt (P : ℝ) := by
    intro t htRange htNot
    have hnotP : ¬P ≤ b t := by
      intro hPt
      exact htNot (Finset.mem_filter.mpr ⟨htRange, hPt⟩)
    have hbP : b t ≤ P := by omega
    have hbdM : b t ∣ M := by
      dsimp [M]
      apply dvd_shiftModulus
      exact Finset.mem_Icc.mpr ⟨hb1 t, hbP⟩
    have hbD : b t ∣ j * M := dvd_mul_of_dvd_right hbdM j
    have hphase0 := norm_phase_mul_sub_one_le_of_approx
      ((t : ℝ) / T) (a t) (b t) Q (j * M)
        (lt_of_lt_of_le Nat.zero_lt_one (hb1 t))
        (lt_of_lt_of_le Nat.zero_lt_one hQone) hbD (happrox t)
    rw [fourier_phase_nat_eq_phase]
    refine (hphase0.trans ?_).trans hPhaseN
    have hjM : ((j * M : ℕ) : ℝ) ≤
        (N : ℝ) ^ ((7 : ℝ) / 8) * M := by
      push_cast
      exact mul_le_mul_of_nonneg_right hjPow (Nat.cast_nonneg M)
    have hbReal : (1 : ℝ) ≤ b t := by exact_mod_cast hb1 t
    have hQhalf : (1 / 2 : ℝ) *
        (N : ℝ) ^ ((15 : ℝ) / 16) ≤ (Q : ℝ) := by
      simpa [Q] using hQlowerN
    have hden : (1 / 2 : ℝ) *
        (N : ℝ) ^ ((15 : ℝ) / 16) ≤ (b t : ℝ) * Q := by
      calc
        (1 / 2 : ℝ) * (N : ℝ) ^ ((15 : ℝ) / 16) ≤ Q := hQhalf
        _ ≤ (b t : ℝ) * Q := by
          nlinarith [hQposR.le, mul_nonneg (sub_nonneg.mpr hbReal) hQposR.le]
    have hsmallDen : 0 < (1 / 2 : ℝ) *
        (N : ℝ) ^ ((15 : ℝ) / 16) := by positivity
    have hnum : 2 * Real.pi * (j * M : ℕ) ≤
        2 * Real.pi * ((N : ℝ) ^ ((7 : ℝ) / 8) * M) := by
      gcongr
    have hratio : (N : ℝ) ^ ((7 : ℝ) / 8) /
        (N : ℝ) ^ ((15 : ℝ) / 16) =
          (N : ℝ) ^ (-((1 : ℝ) / 16)) := by
      rw [← Real.rpow_sub hNreal]
      congr 1
      norm_num
    calc
      2 * Real.pi * (j * M : ℕ) / ((b t : ℝ) * Q) ≤
          (2 * Real.pi * ((N : ℝ) ^ ((7 : ℝ) / 8) * M)) /
            ((1 / 2 : ℝ) * (N : ℝ) ^ ((15 : ℝ) / 16)) := by
        exact div_le_div₀ (by positivity) hnum hsmallDen hden
      _ = 4 * Real.pi * M *
          ((N : ℝ) ^ ((7 : ℝ) / 8) /
            (N : ℝ) ^ ((15 : ℝ) / 16)) := by
        have hpowne : (N : ℝ) ^ ((15 : ℝ) / 16) ≠ 0 :=
          (Real.rpow_pos_of_pos hNreal _).ne'
        field_simp [hpowne]
        ring
      _ = 4 * Real.pi * M * (N : ℝ) ^ (-((1 : ℝ) / 16)) := by
        rw [hratio]
  have hfinite := shiftedSquarePairCount_le_of_fourier_partition
    hNpos hd hA hfree U hU
      (B := 6 * Real.sqrt ((N : ℝ) / P))
      (ε := 1 / Real.sqrt (P : ℝ)) (by positivity) (by positivity)
      hminorCoeff hmajorPhase
  have hcardNat : A.card ≤ N := by
    calc
      A.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hA
      _ = N := by rw [Nat.card_Icc]; omega
  have hcard : (A.card : ℝ) ≤ N := by exact_mod_cast hcardNat
  have hL := squareRootCutoff_cast_le_four_sqrt hN
  have hsqrtP : 0 < Real.sqrt (P : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.mpr hP)
  have hsqrtDiv : Real.sqrt ((N : ℝ) / P) =
      Real.sqrt (N : ℝ) / Real.sqrt (P : ℝ) := by
    rw [Real.sqrt_div (Nat.cast_nonneg N)]
  have hpow : (N : ℝ) ^ ((3 : ℝ) / 2) =
      (N : ℝ) * Real.sqrt (N : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + (1 : ℝ) / 2 by norm_num,
      Real.rpow_add hNreal, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hminorTerm :
      2 * (6 * Real.sqrt ((N : ℝ) / P)) * A.card ≤
        12 * Real.sqrt ((N : ℝ) / P) * N := by
    calc
      2 * (6 * Real.sqrt ((N : ℝ) / P)) * A.card =
          (12 * Real.sqrt ((N : ℝ) / P)) * A.card := by ring
      _ ≤ (12 * Real.sqrt ((N : ℝ) / P)) * N :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ = 12 * Real.sqrt ((N : ℝ) / P) * N := by ring
  have hmajorTerm :
      (1 / Real.sqrt (P : ℝ)) * squareRootCutoff N * A.card ≤
        (1 / Real.sqrt (P : ℝ)) *
          (4 * Real.sqrt (N : ℝ)) * N := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hL (by positivity)) hcard
      (by positivity) (by positivity)
  calc
    (shiftedSquarePairCount A (j * M) : ℝ) ≤
        2 * (6 * Real.sqrt ((N : ℝ) / P)) * A.card +
          (1 / Real.sqrt (P : ℝ)) * squareRootCutoff N * A.card := hfinite
    _ ≤ 12 * Real.sqrt ((N : ℝ) / P) * N +
          (1 / Real.sqrt (P : ℝ)) *
            (4 * Real.sqrt (N : ℝ)) * N :=
      add_le_add hminorTerm hmajorTerm
    _ = 16 * (N : ℝ) ^ ((3 : ℝ) / 2) /
        Real.sqrt (P : ℝ) := by
      rw [hsqrtDiv, hpow]
      field_simp [ne_of_gt hsqrtP]
      ring
    _ = 16 * (N : ℝ) ^ ((3 : ℝ) / 2) /
        Real.sqrt (P : ℝ) := rfl

end Erdos438
