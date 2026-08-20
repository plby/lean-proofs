import Mathlib
import ErdosProblems.Erdos438.Fourier
import ErdosProblems.Erdos387.FiniteWeylInequality
import ErdosProblems.Erdos443
import ErdosProblems.Erdos444.Moment

/-!
# Erdős Problem 439

Khalfalah and Szemerédi proved that every finite colouring of the positive
integers contains two **distinct** equally coloured integers whose sum is a
square.  More generally, they proved the same conclusion with the squares
replaced by the values of any nonconstant integer polynomial which assumes an
even value.

The predicates in this file deliberately include positivity and distinctness:
without distinctness, the parity hypothesis in the polynomial theorem would
make the assertion vacuous.
-/

open scoped Polynomial

namespace Erdos439

open Filter
open scoped BigOperators ComplexConjugate

/-- A colouring contains a non-diagonal monochromatic representation of a
`k`th power as a sum of two positive natural numbers. -/
def HasMonochromaticPowerSum {α : Type*} (color : ℕ → α) (k : ℕ) : Prop :=
  ∃ x y z : ℕ,
    0 < x ∧ 0 < y ∧ x ≠ y ∧ color x = color y ∧ x + y = z ^ k

/-- The positive resolution of the `k`th-power version of Problem 439. -/
def PowerResolution (k : ℕ) : Prop :=
  ∀ (α : Type*) [Finite α] (color : ℕ → α),
    HasMonochromaticPowerSum color k

/-- The literal integer-domain version asked in Problem 439. -/
def IntegerPowerResolution (k : ℕ) : Prop :=
  ∀ (α : Type*) [Finite α] (color : ℤ → α),
    ∃ x y z : ℤ, x ≠ y ∧ color x = color y ∧ x + y = z ^ k

/-- Positive solutions immediately give the integer-domain statement. -/
theorem integerPowerResolution_of_powerResolution.{u} {k : ℕ}
    (h : @PowerResolution.{u} k) : @IntegerPowerResolution.{u} k := by
  intro α _ color
  obtain ⟨x, y, z, hx, hy, hxy, hc, hsum⟩ :=
    h _ (fun n ↦ color n)
  refine ⟨x, y, z, ?_, hc, ?_⟩
  · exact_mod_cast hxy
  · exact_mod_cast hsum

/-- A colouring contains a non-diagonal monochromatic representation of a
value of the integer polynomial `P`.  The polynomial variable is allowed to be
an integer; the two coloured summands remain positive natural numbers. -/
def HasMonochromaticPolynomialSum {α : Type*} (color : ℕ → α)
    (P : ℤ[X]) : Prop :=
  ∃ x y : ℕ, ∃ z : ℤ,
    0 < x ∧ 0 < y ∧ x ≠ y ∧ color x = color y ∧
      (x + y : ℤ) = P.eval z

/-- The positive-domain, positive-leading-coefficient normalization used by
the analytic proof. -/
def PositivePolynomialResolution : Prop :=
  ∀ (P : ℤ[X]), 0 < P.natDegree → 0 < P.leadingCoeff →
    (∃ b : ℤ, Even (P.eval b)) →
    ∀ (α : Type*) [Finite α] (color : ℕ → α),
      HasMonochromaticPolynomialSum color P

/-- The exact integer-domain conclusion of Khalfalah--Szemerédi. -/
def HasMonochromaticIntegerPolynomialSum {α : Type*} (color : ℤ → α)
    (P : ℤ[X]) : Prop :=
  ∃ x y z : ℤ, x ≠ y ∧ color x = color y ∧ x + y = P.eval z

/-- The established general resolution: every nonconstant integer polynomial
which assumes an even value gives a monochromatic non-diagonal sum in every
finite colouring of the integers. -/
def PolynomialResolution : Prop :=
  ∀ (P : ℤ[X]), 0 < P.natDegree →
    (∃ b : ℤ, Even (P.eval b)) →
    ∀ (α : Type*) [Finite α] (color : ℤ → α),
      HasMonochromaticIntegerPolynomialSum color P

/-- Removing the positive-leading normalization uses reflection of the
integer colouring. -/
theorem polynomialResolution_of_positivePolynomialResolution.{u}
    (h : @PositivePolynomialResolution.{u}) : @PolynomialResolution.{u} := by
  intro P hdegree heven α _ color
  have hP : P ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  rcases lt_or_gt_of_ne hlead with hleadNeg | hleadPos
  · have hnegDegree : 0 < (-P).natDegree := by simpa using hdegree
    have hnegLead : 0 < (-P).leadingCoeff := by
      rw [Polynomial.leadingCoeff_neg]
      exact neg_pos.mpr hleadNeg
    have hnegEven : ∃ b : ℤ, Even ((-P).eval b) := by
      obtain ⟨b, hb⟩ := heven
      exact ⟨b, by simpa using hb.neg⟩
    obtain ⟨x, y, z, hx, hy, hxy, hc, hsum⟩ :=
      h (-P) hnegDegree hnegLead hnegEven α
        (fun n ↦ color (-(n : ℤ)))
    refine ⟨-(x : ℤ), -(y : ℤ), z, ?_, hc, ?_⟩
    · intro heq
      apply hxy
      exact_mod_cast neg_injective heq
    · simp only [Polynomial.eval_neg] at hsum
      omega
  · obtain ⟨x, y, z, hx, hy, hxy, hc, hsum⟩ :=
      h P hdegree hleadPos heven α (fun n ↦ color (n : ℤ))
    refine ⟨(x : ℤ), (y : ℤ), z, ?_, hc, ?_⟩
    · exact_mod_cast hxy
    · exact hsum

lemma hasMonochromaticPowerSum_comm {α : Type*} {color : ℕ → α} {k : ℕ}
    (h : HasMonochromaticPowerSum color k) :
    ∃ x y z : ℕ,
      0 < x ∧ 0 < y ∧ y ≠ x ∧ color y = color x ∧ y + x = z ^ k := by
  obtain ⟨x, y, z, hx, hy, hxy, hc, hs⟩ := h
  exact ⟨x, y, z, hx, hy, hxy.symm, hc.symm, by simpa [Nat.add_comm] using hs⟩

/-! ## The exact `W`-tricked power polynomial

For a fixed positive exponent put `D = k * 2^(k-1)` and `W = D * L`.
Expanding `(W*n + 2)^k` and dividing the nonconstant part by `D*W`
gives an integer polynomial.  Its linear coefficient is one and every higher
coefficient is divisible by `L`.  Thus the normalized polynomial is congruent
to the identity modulo every divisor of `L`; this is the local cancellation
which the analytic argument needs at small denominators.
-/

/-- The derivative of `X^k` at the even base point `2`. -/
def powerDerivative (k : ℕ) : ℕ := k * 2 ^ (k - 1)

/-- The step in the original power variable used by the `W`-trick. -/
def powerModulus (k L : ℕ) : ℕ := powerDerivative k * L

/-- The affine step in the two coloured summands. -/
def powerStep (k L : ℕ) : ℕ := powerDerivative k * powerModulus k L

/-- The integral normalization of `(W*n+2)^k-2^k`, written coefficientwise
so no divisibility or polynomial division is hidden in the definition. -/
def normalizedPower (k L n : ℕ) : ℕ :=
  n + ∑ j ∈ Finset.Icc 2 k,
    k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
      L ^ (j - 1) * n ^ j

private theorem sum_range_eq_zero_add_one_add_Icc {M : Type*}
    [AddCommMonoid M] (f : ℕ → M) {k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (k + 1), f j =
      f 0 + f 1 + ∑ j ∈ Finset.Icc 2 k, f j := by
  have hrange : Finset.range (k + 1) =
      insert 0 (insert 1 (Finset.Icc 2 k)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange]
  simp [hk, add_assoc]

private theorem pow_eq_sq_mul_pow_sub_two (a j : ℕ) (hj : 2 ≤ j) :
    a ^ j = a ^ 2 * a ^ (j - 2) := by
  rw [← pow_add]
  congr
  omega

private theorem pow_eq_mul_pow_sub_one (a j : ℕ) (hj : 1 ≤ j) :
    a ^ j = a * a ^ (j - 1) := by
  conv_lhs => rw [show j = 1 + (j - 1) by omega]
  rw [pow_add, pow_one]

/-- Exact support identity for the normalized power polynomial. -/
theorem powerStep_mul_normalizedPower_add (k L n : ℕ) (hk : 1 ≤ k) :
    powerStep k L * normalizedPower k L n + 2 ^ k =
      (powerModulus k L * n + 2) ^ k := by
  rw [add_pow, sum_range_eq_zero_add_one_add_Icc _ hk]
  simp only [pow_zero, one_mul, Nat.choose_zero_right, mul_one,
    Nat.choose_one_right, Nat.cast_one, Nat.cast_id]
  have hkSub : k - 0 = k := Nat.sub_zero k
  rw [hkSub]
  have hlinear :
      (powerModulus k L * n) ^ 1 * 2 ^ (k - 1) * k =
        powerStep k L * n := by
    simp only [pow_one, powerStep, powerModulus, powerDerivative]
    ring
  rw [hlinear]
  have hterm : ∀ j ∈ Finset.Icc 2 k,
      (powerModulus k L * n) ^ j * 2 ^ (k - j) * k.choose j =
        powerStep k L *
          (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) * n ^ j) := by
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj1 : 1 ≤ j := hj2.trans' (by omega)
    rw [mul_pow]
    simp only [powerModulus, powerStep]
    rw [mul_pow]
    rw [pow_eq_sq_mul_pow_sub_two (powerDerivative k) j hj2]
    rw [pow_eq_mul_pow_sub_one L j hj1]
    ring
  have hsum :
      (∑ j ∈ Finset.Icc 2 k,
        (powerModulus k L * n) ^ j * 2 ^ (k - j) * k.choose j) =
      ∑ j ∈ Finset.Icc 2 k,
        powerStep k L *
          (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) * n ^ j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm j hj
  rw [hsum, normalizedPower, mul_add, Finset.mul_sum]
  ring

/-- The normalized power polynomial is the identity modulo `L`. -/
theorem normalizedPower_mod (k L n : ℕ) :
    normalizedPower k L n % L = n % L := by
  let S := ∑ j ∈ Finset.Icc 2 k,
    k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
      L ^ (j - 1) * n ^ j
  have hdiv : L ∣ S := by
    apply Finset.dvd_sum
    intro j hj
    have hj1 : j - 1 ≠ 0 := by
      have := (Finset.mem_Icc.mp hj).1
      omega
    apply dvd_mul_of_dvd_left
    apply dvd_mul_of_dvd_right
    exact dvd_pow_self L hj1
  have hmod : S % L = 0 := Nat.mod_eq_zero_of_dvd hdiv
  simp only [normalizedPower]
  change (n + S) % L = n % L
  rw [Nat.add_mod, hmod, add_zero, Nat.mod_mod]

/-- The nonlinear tail after factoring one copy of the local modulus from
`normalizedPower`. -/
def normalizedPowerTail (k L n : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 2 k,
    k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
      L ^ (j - 2) * n ^ j

theorem normalizedPower_eq_add_mul_tail (k L n : ℕ) :
    normalizedPower k L n = n + L * normalizedPowerTail k L n := by
  unfold normalizedPower normalizedPowerTail
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
  rw [show j - 1 = (j - 2) + 1 by omega, pow_succ']
  ring

theorem normalizedPowerTail_mono {k L x y : ℕ} (hxy : x ≤ y) :
    normalizedPowerTail k L x ≤ normalizedPowerTail k L y := by
  unfold normalizedPowerTail
  apply Finset.sum_le_sum
  intro j hj
  gcongr

theorem normalizedPowerTail_modEq (k L x y m : ℕ)
    (hxy : x ≡ y [MOD m]) :
    normalizedPowerTail k L x ≡ normalizedPowerTail k L y [MOD m] := by
  unfold normalizedPowerTail
  apply Nat.ModEq.sum
  intro j hj
  exact (hxy.pow j).mul_left _

theorem sub_dvd_normalizedPowerTail_sub {k L x y : ℕ} (hyx : y ≤ x) :
    x - y ∣ normalizedPowerTail k L x - normalizedPowerTail k L y := by
  have hxy : x ≡ y [MOD x - y] :=
    ((Nat.modEq_iff_dvd' hyx).2 dvd_rfl).symm
  exact (Nat.modEq_iff_dvd'
      (normalizedPowerTail_mono (k := k) (L := L) hyx)).1
    (normalizedPowerTail_modEq k L x y (x - y) hxy).symm

/-- A number supported on primes of `L` is coprime to every integer
congruent to one modulo `L`. -/
theorem coprime_one_add_mul_of_prime_dvd (q L C : ℕ)
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ L) :
    q.Coprime (1 + L * C) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd hne
  have hpq : p ∣ q := hpgcd.trans (Nat.gcd_dvd_left q (1 + L * C))
  have hpsum : p ∣ 1 + L * C :=
    hpgcd.trans (Nat.gcd_dvd_right q (1 + L * C))
  have hpLC : p ∣ L * C := dvd_mul_of_dvd_left (hsupport p hp hpq) C
  have hpone : p ∣ 1 := by
    simpa using Nat.dvd_sub hpsum hpLC
  exact hp.not_dvd_one hpone

@[simp] theorem normalizedPower_zero (k L : ℕ) :
    normalizedPower k L 0 = 0 := by
  simp only [normalizedPower, zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  have hj0 : j ≠ 0 := by
    have := (Finset.mem_Icc.mp hj).1
    omega
  simp [zero_pow hj0]

/-- The normalized polynomial is strictly increasing; the explicit linear
term is what makes this independent of all higher coefficients. -/
theorem normalizedPower_strictMono (k L : ℕ) :
    StrictMono (normalizedPower k L) := by
  intro a b hab
  unfold normalizedPower
  apply Nat.add_lt_add_of_lt_of_le hab
  apply Finset.sum_le_sum
  intro j hj
  gcongr

/-- Consecutive gaps of the normalized power polynomial, viewed as real
weights. -/
noncomputable def normalizedPowerGap (k L n : ℕ) : ℝ :=
  (normalizedPower k L (n + 1) : ℝ) - (normalizedPower k L n : ℝ)

theorem normalizedPowerGap_pos (k L n : ℕ) :
    0 < normalizedPowerGap k L n := by
  unfold normalizedPowerGap
  apply sub_pos.mpr
  exact_mod_cast normalizedPower_strictMono k L (Nat.lt_succ_self n)

/-- Consecutive gaps of a natural power are nondecreasing.  This is the
one-dimensional convexity input needed for summation by parts. -/
private theorem pow_gap_mono_real (n j : ℕ) :
    (((n + 1 : ℕ) : ℝ) ^ j - (n : ℝ) ^ j) ≤
      (((n + 2 : ℕ) : ℝ) ^ j - ((n + 1 : ℕ) : ℝ) ^ j) := by
  have h :=
    (convexOn_pow j : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ ↦ x ^ j)).slope_mono_adjacent
      (x := (n : ℝ)) (y := ((n + 1 : ℕ) : ℝ))
      (z := ((n + 2 : ℕ) : ℝ))
      (by exact Set.mem_Ici.mpr (by positivity))
      (by exact Set.mem_Ici.mpr (by positivity)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- The explicit normalized power polynomial has nondecreasing consecutive
gaps. -/
theorem normalizedPowerGap_mono (k L n : ℕ) :
    normalizedPowerGap k L n ≤ normalizedPowerGap k L (n + 1) := by
  have hrepr : ∀ m : ℕ, normalizedPowerGap k L m =
      1 + ∑ j ∈ Finset.Icc 2 k,
        (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
          L ^ (j - 1) : ℝ) *
          ((((m + 1 : ℕ) : ℝ) ^ j) - (m : ℝ) ^ j) := by
    intro m
    unfold normalizedPowerGap normalizedPower
    push_cast
    calc
      ((m : ℝ) + 1 + ∑ j ∈ Finset.Icc 2 k,
          (k.choose j : ℝ) * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) * ((m : ℝ) + 1) ^ j) -
          ((m : ℝ) + ∑ j ∈ Finset.Icc 2 k,
            (k.choose j : ℝ) * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) * (m : ℝ) ^ j) =
        1 + ((∑ j ∈ Finset.Icc 2 k,
          (k.choose j : ℝ) * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) * ((m : ℝ) + 1) ^ j) -
          ∑ j ∈ Finset.Icc 2 k,
            (k.choose j : ℝ) * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
              L ^ (j - 1) * (m : ℝ) ^ j) := by ring
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply congrArg (fun x : ℝ ↦ 1 + x)
        apply Finset.sum_congr rfl
        intro j hj
        ring
  rw [hrepr n, hrepr (n + 1)]
  suffices (∑ j ∈ Finset.Icc 2 k,
      (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
        L ^ (j - 1) : ℝ) *
        ((((n + 1 : ℕ) : ℝ) ^ j) - (n : ℝ) ^ j)) ≤
      ∑ j ∈ Finset.Icc 2 k,
        (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
          L ^ (j - 1) : ℝ) *
          ((((n + 2 : ℕ) : ℝ) ^ j) - ((n + 1 : ℕ) : ℝ) ^ j) by
    have hright :
        (∑ j ∈ Finset.Icc 2 k,
          (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) : ℝ) *
            ((((n + 2 : ℕ) : ℝ) ^ j) - ((n + 1 : ℕ) : ℝ) ^ j)) =
        ∑ j ∈ Finset.Icc 2 k,
          (k.choose j * 2 ^ (k - j) * powerDerivative k ^ (j - 2) *
            L ^ (j - 1) : ℝ) *
            ((((n + 1 + 1 : ℕ) : ℝ) ^ j) - ((n + 1 : ℕ) : ℝ) ^ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 3
    rw [← hright]
    simpa [add_comm] using add_le_add_left this 1
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left
  · simpa [Nat.add_assoc] using pow_gap_mono_real n j
  · positivity

@[simp] theorem normalizedPower_two (L n : ℕ) :
    normalizedPower 2 L n = n + L * n ^ 2 := by
  simp [normalizedPower, powerDerivative]

@[simp] theorem normalizedPowerGap_two (L n : ℕ) :
    normalizedPowerGap 2 L n = 1 + L * (2 * n + 1) := by
  unfold normalizedPowerGap
  rw [normalizedPower_two, normalizedPower_two]
  push_cast
  ring

/-- The gap-weighted probability measure on the normalized power values below
`normalizedPower k L N`.  Placing the length of each image gap at its left
endpoint is the discrete Stieltjes measure used in the Fourier argument. -/
noncomputable def normalizedPowerWeight (k L N s : ℕ) : ℝ :=
  (normalizedPower k L N : ℝ)⁻¹ *
    ∑ n ∈ Finset.range N,
      if normalizedPower k L n = s then normalizedPowerGap k L n else 0

theorem normalizedPowerWeight_nonneg (k L N s : ℕ) :
    0 ≤ normalizedPowerWeight k L N s := by
  unfold normalizedPowerWeight
  apply mul_nonneg (inv_nonneg.mpr (by positivity))
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact (normalizedPowerGap_pos k L n).le
  · exact le_rfl

theorem normalizedPowerWeight_mass (k L N : ℕ) (hN : 0 < N) :
    ∑ s ∈ Finset.range (normalizedPower k L N),
      normalizedPowerWeight k L N s = 1 := by
  have hTpos : 0 < normalizedPower k L N := by
    simpa only [normalizedPower_zero] using
      normalizedPower_strictMono k L hN
  have hpoint : ∀ n ∈ Finset.range N,
      (∑ s ∈ Finset.range (normalizedPower k L N),
        if normalizedPower k L n = s then normalizedPowerGap k L n else 0) =
          normalizedPowerGap k L n := by
    intro n hn
    rw [Finset.sum_eq_single (normalizedPower k L n)]
    · simp
    · intro s hs hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr
        (normalizedPower_strictMono k L (Finset.mem_range.mp hn)))).elim
  unfold normalizedPowerWeight
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hdouble :
      (∑ n ∈ Finset.range N,
        ∑ s ∈ Finset.range (normalizedPower k L N),
          if normalizedPower k L n = s then normalizedPowerGap k L n else 0) =
        ∑ n ∈ Finset.range N, normalizedPowerGap k L n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hpoint n hn
  rw [hdouble]
  have htel :
      (∑ n ∈ Finset.range N, normalizedPowerGap k L n) =
        (normalizedPower k L N : ℝ) := by
    unfold normalizedPowerGap
    simpa using Finset.sum_range_sub
      (fun n => (normalizedPower k L n : ℝ)) N
  rw [htel]
  exact inv_mul_cancel₀ (by exact_mod_cast hTpos.ne')

/-- Positive mass can occur only at a normalized power value from the defining
range. -/
theorem normalizedPowerWeight_support (k L N s : ℕ)
    (hs : 0 < normalizedPowerWeight k L N s) :
    ∃ n ∈ Finset.range N, normalizedPower k L n = s := by
  by_contra! hnone
  have hsumzero :
      (∑ n ∈ Finset.range N,
        if normalizedPower k L n = s then normalizedPowerGap k L n else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [hnone n hn]
  have hzero : normalizedPowerWeight k L N s = 0 := by
    simp [normalizedPowerWeight, hsumzero]
  rw [hzero] at hs
  exact lt_irrefl 0 hs

/-! ## The canonical weighted phase sum

Unfolding the value-fibre definition of `normalizedPowerWeight` turns its
Fourier transform into the expected gap-weighted polynomial exponential sum.
This identity is the entry point for both the low-frequency Stieltjes estimate
and the Weyl-differencing estimate. -/

namespace PowerDecay

open Erdos438.Fourier

/-- Formal forward difference by an integer shift. -/
noncomputable def polynomialShiftDifference (s : ℤ) (P : ℤ[X]) : ℤ[X] :=
  P.comp (Polynomial.X + Polynomial.C s) - P

@[simp] theorem eval_polynomialShiftDifference (s : ℤ) (P : ℤ[X])
    (x : ℤ) :
    (polynomialShiftDifference s P).eval x = P.eval (x + s) - P.eval x := by
  simp [polynomialShiftDifference]

/-- A nonconstant polynomial loses at least one degree under a forward
difference. -/
theorem natDegree_polynomialShiftDifference_lt (s : ℤ) (P : ℤ[X])
    (hP : P ≠ 0) (hdegree : 0 < P.natDegree) :
    (polynomialShiftDifference s P).natDegree < P.natDegree := by
  let Q : ℤ[X] := P.comp (Polynomial.X + Polynomial.C s)
  have hinner : (Polynomial.X + Polynomial.C s : ℤ[X]).natDegree = 1 :=
    Polynomial.natDegree_X_add_C s
  have hQlead : Q.leadingCoeff = P.leadingCoeff := by
    rw [show Q = P.comp (Polynomial.X + Polynomial.C s) by rfl,
      Polynomial.leadingCoeff_comp (by omega),
      Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
  have hQ : Q ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [hQlead]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP
  have hQdegree : Q.degree = P.degree := by
    rw [Polynomial.degree_eq_natDegree hQ, Polynomial.degree_eq_natDegree hP]
    congr 1
    rw [show Q = P.comp (Polynomial.X + Polynomial.C s) by rfl,
      Polynomial.natDegree_comp, hinner, Nat.mul_one]
  have hdegreeDrop : (Q - P).degree < P.degree := by
    calc
      (Q - P).degree < Q.degree :=
        Polynomial.degree_sub_lt_left hQdegree hQ hQlead
      _ = P.degree := hQdegree
  by_cases hzero : Q - P = 0
  · change (Q - P).natDegree < P.natDegree
    rw [hzero]
    simpa using hdegree
  · change (Q - P).natDegree < P.natDegree
    rw [Polynomial.degree_eq_natDegree hzero,
      Polynomial.degree_eq_natDegree hP] at hdegreeDrop
    exact_mod_cast hdegreeDrop

/-- The top surviving coefficient after a nontrivial shift difference is
the leading coefficient times the degree and the shift. -/
theorem coeff_pred_polynomialShiftDifference (s : ℤ) (P : ℤ[X])
    (hdegree : 0 < P.natDegree) :
    (polynomialShiftDifference s P).coeff (P.natDegree - 1) =
      P.leadingCoeff * (P.natDegree : ℤ) * s := by
  let d := P.natDegree
  have hd : d - 1 + 1 = d := Nat.sub_add_cancel hdegree
  have hhasseDegree :
      (P.hasseDeriv (d - 1)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_hasseDeriv_le P (d - 1)).trans ?_
    omega
  have hrepr := Polynomial.eq_X_add_C_of_natDegree_le_one hhasseDegree
  unfold polynomialShiftDifference
  rw [show P.comp (Polynomial.X + Polynomial.C s) = P.taylor s by
    exact (Polynomial.taylor_apply s P).symm]
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff]
  rw [hrepr]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.hasseDeriv_coeff]
  have hchoose : d.choose (d - 1) = d := by
    calc
      d.choose (d - 1) = ((d - 1) + 1).choose (d - 1) := by rw [hd]
      _ = ((d - 1) + 1).choose 1 := Nat.choose_symm_add
      _ = d := by rw [Nat.choose_one_right, hd]
  have hone : 1 + (d - 1) = d := by omega
  simp only [zero_add, Nat.choose_self, Nat.cast_one, one_mul] at *
  rw [hone, hchoose]
  change (d : ℤ) * P.coeff d * s + P.coeff (d - 1) -
      P.coeff (d - 1) = P.leadingCoeff * (d : ℤ) * s
  rw [show P.coeff d = P.leadingCoeff by rfl]
  ring

/-- Over the integers, a positive shift lowers every nonconstant
polynomial's degree by exactly one. -/
theorem natDegree_polynomialShiftDifference (s : ℤ) (P : ℤ[X])
    (hdegree : 0 < P.natDegree) (hs : s ≠ 0) :
    (polynomialShiftDifference s P).natDegree = P.natDegree - 1 := by
  have hP : P ≠ 0 := by
    intro hzero
    rw [hzero] at hdegree
    simp at hdegree
  have hle : (polynomialShiftDifference s P).natDegree ≤ P.natDegree - 1 := by
    have hlt := natDegree_polynomialShiftDifference_lt s P hP hdegree
    omega
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hle
  rw [coeff_pred_polynomialShiftDifference s P hdegree]
  have hdegreeCast : (P.natDegree : ℤ) ≠ 0 := by exact_mod_cast hdegree.ne'
  exact mul_ne_zero (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP)
    hdegreeCast) hs

theorem leadingCoeff_polynomialShiftDifference (s : ℤ) (P : ℤ[X])
    (hdegree : 0 < P.natDegree) (hs : s ≠ 0) :
    (polynomialShiftDifference s P).leadingCoeff =
      P.leadingCoeff * (P.natDegree : ℤ) * s := by
  rw [Polynomial.leadingCoeff,
    natDegree_polynomialShiftDifference s P hdegree hs,
    coeff_pred_polynomialShiftDifference s P hdegree]

/-- The formal integer polynomial whose natural evaluations are
`normalizedPower`. -/
noncomputable def normalizedPowerPolynomial (k L : ℕ) : ℤ[X] :=
  (Polynomial.X : ℤ[X]) + ∑ j ∈ Finset.Icc 2 k,
    Polynomial.C ((k.choose j * 2 ^ (k - j) *
      powerDerivative k ^ (j - 2) * L ^ (j - 1) : ℕ) : ℤ) *
        (Polynomial.X : ℤ[X]) ^ j

@[simp] theorem eval_normalizedPowerPolynomial (k L n : ℕ) :
    (normalizedPowerPolynomial k L).eval (n : ℤ) =
      (normalizedPower k L n : ℤ) := by
  simp only [normalizedPowerPolynomial, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow]
  unfold normalizedPower
  push_cast
  rfl

/-- The top coefficient of the normalized power polynomial. -/
theorem coeff_normalizedPowerPolynomial_top (k L : ℕ) (hk : 2 ≤ k) :
    (normalizedPowerPolynomial k L).coeff k =
      (powerDerivative k ^ (k - 2) * L ^ (k - 1) : ℕ) := by
  rw [normalizedPowerPolynomial, Polynomial.coeff_add]
  simp only [Polynomial.finsetSum_coeff]
  have hkMem : k ∈ Finset.Icc 2 k := Finset.mem_Icc.mpr ⟨hk, le_rfl⟩
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self]
    simp [Polynomial.coeff_X, show (1 : ℕ) ≠ k by omega, powerDerivative]
  · intro j hj hjk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hjk.symm]
    simp
  · exact fun hnot ↦ (hnot hkMem).elim

/-- With a positive local modulus, the formal normalized power polynomial
has exactly the advertised degree. -/
theorem natDegree_normalizedPowerPolynomial (k L : ℕ) (hk : 2 ≤ k)
    (hL : 0 < L) :
    (normalizedPowerPolynomial k L).natDegree = k := by
  have hsum :
      (∑ j ∈ Finset.Icc 2 k,
        Polynomial.C ((k.choose j * 2 ^ (k - j) *
          powerDerivative k ^ (j - 2) * L ^ (j - 1) : ℕ) : ℤ) *
            (Polynomial.X : ℤ[X]) ^ j).natDegree ≤ k := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_X_pow_le _ j).trans
      (Finset.mem_Icc.mp hj).2
  have hupper : (normalizedPowerPolynomial k L).natDegree ≤ k := by
    unfold normalizedPowerPolynomial
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ hsum)
    rw [Polynomial.natDegree_X]
    omega
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hupper
  rw [coeff_normalizedPowerPolynomial_top k L hk]
  have hD : 0 < powerDerivative k := by
    unfold powerDerivative
    positivity
  exact_mod_cast (Nat.mul_pos (pow_pos hD _) (pow_pos hL _)).ne'

/-- Formal iterate of the same positive-shift difference operation used in
`iteratedPowerDifference`. -/
noncomputable def iteratedPolynomialDifference (P : ℤ[X]) :
    List ℕ → ℤ[X]
  | [] => P
  | h :: hs => polynomialShiftDifference (h + 1) (iteratedPolynomialDifference P hs)

/-- A list of fewer positive differences lowers the degree by exactly the
length of the list. -/
theorem natDegree_iteratedPolynomialDifference (P : ℤ[X]) (hs : List ℕ)
    (hlen : hs.length < P.natDegree) :
    (iteratedPolynomialDifference P hs).natDegree =
      P.natDegree - hs.length := by
  induction hs generalizing P with
  | nil => simp [iteratedPolynomialDifference]
  | cons h hs ih =>
      have htail : hs.length < P.natDegree := by
        simp only [List.length_cons] at hlen
        omega
      have htailDegree := ih P htail
      have hpositive :
          0 < (iteratedPolynomialDifference P hs).natDegree := by
        rw [htailDegree]
        omega
      have hshift : (h : ℤ) + 1 ≠ 0 := by positivity
      rw [iteratedPolynomialDifference,
        natDegree_polynomialShiftDifference _ _ hpositive hshift,
        htailDegree]
      simp only [List.length_cons]
      omega

/-- Exact leading coefficient after an arbitrary list of positive shift
differences. -/
theorem leadingCoeff_iteratedPolynomialDifference (P : ℤ[X]) (hs : List ℕ)
    (hlen : hs.length < P.natDegree) :
    (iteratedPolynomialDifference P hs).leadingCoeff =
      P.leadingCoeff * (P.natDegree.descFactorial hs.length : ℤ) *
        (hs.map fun h ↦ ((h + 1 : ℕ) : ℤ)).prod := by
  induction hs generalizing P with
  | nil => simp [iteratedPolynomialDifference]
  | cons h hs ih =>
      have htail : hs.length < P.natDegree := by
        simp only [List.length_cons] at hlen
        omega
      have htailDegree := natDegree_iteratedPolynomialDifference P hs htail
      have hpositive :
          0 < (iteratedPolynomialDifference P hs).natDegree := by
        rw [htailDegree]
        omega
      have hshift : (h : ℤ) + 1 ≠ 0 := by positivity
      rw [iteratedPolynomialDifference,
        leadingCoeff_polynomialShiftDifference _ _ hpositive hshift,
        ih P htail, htailDegree]
      simp only [List.length_cons, List.map_cons, List.prod_cons,
        Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub htail.le]
      push_cast
      ring

/-- The ordinary unit-circle sequence underlying the weighted power measure. -/
noncomputable def powerPhaseSequence (k L N t n : ℕ) : ℂ :=
  phase (normalizedPower k L N) (-(t : ℤ))
    (normalizedPower k L n : ℤ)

/-- A prefix of the ordinary normalized-power phase sequence. -/
noncomputable def powerPhasePrefix (k L N t m : ℕ) : ℂ :=
  ∑ n ∈ Finset.range m, powerPhaseSequence k L N t n

theorem norm_powerPhaseSequence (k L N t n : ℕ) :
    ‖powerPhaseSequence k L N t n‖ = 1 := by
  exact norm_phase _ _ _

/-- One exact Weyl-differencing step for every prefix of the power phase. -/
theorem norm_powerPhasePrefix_sq_le (k L N t m : ℕ) :
    ‖powerPhasePrefix k L N t m‖ ^ 2 ≤
      m + 2 * ∑ h ∈ Finset.range m,
        ‖∑ n ∈ Finset.range (m - h - 1),
          Erdos387.InverseWeyl.positiveShiftCorrelation
            (powerPhaseSequence k L N t) h n‖ := by
  unfold powerPhasePrefix
  exact Erdos387.FiniteWeyl.norm_sum_range_sq_le_sum_positiveShift
    (powerPhaseSequence k L N t) m
      (fun n _hn ↦ norm_powerPhaseSequence k L N t n)

/-- A positive-shift correlation is the character of the corresponding
finite difference of the normalized polynomial. -/
theorem positiveShiftCorrelation_powerPhaseSequence
    (k L N t h n : ℕ) :
    Erdos387.InverseWeyl.positiveShiftCorrelation
        (powerPhaseSequence k L N t) h n =
      phase (normalizedPower k L N) (-(t : ℤ))
        ((normalizedPower k L (n + h + 1) : ℤ) -
          normalizedPower k L n) := by
  unfold Erdos387.InverseWeyl.positiveShiftCorrelation powerPhaseSequence
  rw [conj_phase, ← phase_add_right]
  congr 2

/-- The integer phase obtained by repeatedly taking positive finite
differences.  The list uses the same zero-based shift convention as the
generic Weyl library. -/
def iteratedPowerDifference (k L : ℕ) : List ℕ → ℕ → ℤ
  | [], n => normalizedPower k L n
  | h :: hs, n =>
      iteratedPowerDifference k L hs (n + h + 1) -
        iteratedPowerDifference k L hs n

theorem iteratedPowerDifference_two_singleton (L h n : ℕ) :
    iteratedPowerDifference 2 L [h] n =
      (h + 1 : ℕ) + (L : ℤ) *
        (2 * (h + 1 : ℕ) * n + (h + 1 : ℕ) ^ 2) := by
  simp only [iteratedPowerDifference, normalizedPower_two]
  push_cast
  ring

theorem iteratedPowerDifference_two_pair (L g h n : ℕ) :
    iteratedPowerDifference 2 L [g, h] n =
      2 * (L : ℤ) * (g + 1 : ℕ) * (h + 1 : ℕ) := by
  unfold iteratedPowerDifference
  rw [iteratedPowerDifference_two_singleton,
    iteratedPowerDifference_two_singleton]
  push_cast
  ring

@[simp] theorem eval_iteratedPolynomialDifference_normalizedPower
    (k L : ℕ) (hs : List ℕ) (n : ℕ) :
    (iteratedPolynomialDifference (normalizedPowerPolynomial k L) hs).eval (n : ℤ) =
      iteratedPowerDifference k L hs n := by
  induction hs generalizing n with
  | nil => simp [iteratedPolynomialDifference, iteratedPowerDifference]
  | cons h hs ih =>
      simp only [iteratedPolynomialDifference, eval_polynomialShiftDifference,
        iteratedPowerDifference]
      rw [ih]
      have hcast : (n : ℤ) + ((h : ℤ) + 1) = ((n + h + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [hcast, ih]

/-- Every iterated correlation of the power phase is exactly the character
of the corresponding iterated polynomial difference. -/
theorem iteratedPositiveShiftCorrelation_powerPhaseSequence
    (k L N t : ℕ) (hs : List ℕ) (n : ℕ) :
    Erdos387.InverseWeyl.iteratedPositiveShiftCorrelation
        (powerPhaseSequence k L N t) hs n =
      phase (normalizedPower k L N) (-(t : ℤ))
        (iteratedPowerDifference k L hs n) := by
  induction hs generalizing n with
  | nil => rfl
  | cons h hs ih =>
      unfold Erdos387.InverseWeyl.iteratedPositiveShiftCorrelation
        Erdos387.InverseWeyl.positiveShiftCorrelation iteratedPowerDifference
      rw [ih, ih, conj_phase, ← phase_add_right]
      congr 2

/-- The generic finite Weyl inequality specialized after an arbitrary list
of finite differences of the normalized power phase. -/
theorem norm_sum_iteratedPowerDifference_sq_le
    (k L N t : ℕ) (hs : List ℕ) (m : ℕ) :
    ‖∑ n ∈ Finset.range m,
        phase (normalizedPower k L N) (-(t : ℤ))
          (iteratedPowerDifference k L hs n)‖ ^ 2 ≤
      m + 2 * ∑ h ∈ Finset.range m,
        ‖∑ n ∈ Finset.range (m - h - 1),
          phase (normalizedPower k L N) (-(t : ℤ))
            (iteratedPowerDifference k L (h :: hs) n)‖ := by
  have h := Erdos387.FiniteWeyl.norm_sum_iteratedCorrelation_sq_le
    (powerPhaseSequence k L N t)
    (fun n ↦ norm_powerPhaseSequence k L N t n) hs m
  simpa only [iteratedPositiveShiftCorrelation_powerPhaseSequence] using h

/-- The elementary envelope obtained by iterating the finite Weyl
difference inequality. -/
noncomputable def finiteWeylEnvelope (N : ℕ) (R : ℝ) : ℕ → ℝ
  | 0 => R
  | d + 1 => Real.sqrt
      ((N : ℝ) + 2 * (N : ℝ) * finiteWeylEnvelope N R d)

theorem finiteWeylEnvelope_nonneg (N : ℕ) {R : ℝ} (hR : 0 ≤ R) (d : ℕ) :
    0 ≤ finiteWeylEnvelope N R d := by
  cases d with
  | zero => simpa [finiteWeylEnvelope] using hR
  | succ d => simp [finiteWeylEnvelope]

/-- If all depth-`d` terminal polynomial correlations have prefix norm at
most `R`, repeated finite Weyl differencing bounds the starting prefix by
`finiteWeylEnvelope`. -/
theorem norm_sum_iteratedPowerDifference_le_envelope
    (k L T t N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hs : List ℕ) (m d : ℕ) (hm : m ≤ N)
    (hterminal : ∀ extra : List ℕ, extra.length = d →
      ∀ q ≤ N,
        ‖∑ n ∈ Finset.range q,
          phase (normalizedPower k L T) (-(t : ℤ))
            (iteratedPowerDifference k L (extra ++ hs) n)‖ ≤ R) :
    ‖∑ n ∈ Finset.range m,
      phase (normalizedPower k L T) (-(t : ℤ))
        (iteratedPowerDifference k L hs n)‖ ≤
        finiteWeylEnvelope N R d := by
  induction d generalizing hs m with
  | zero =>
      simpa [finiteWeylEnvelope] using hterminal [] rfl m hm
  | succ d ih =>
      have hchild : ∀ h ∈ Finset.range m,
          ‖∑ n ∈ Finset.range (m - h - 1),
            phase (normalizedPower k L T) (-(t : ℤ))
              (iteratedPowerDifference k L (h :: hs) n)‖ ≤
            finiteWeylEnvelope N R d := by
        intro h hh
        apply ih (h :: hs) (m - h - 1) (by omega)
        intro extra hextra q hq
        have hlen : (extra ++ [h]).length = d + 1 := by
          simp [hextra]
        simpa [List.append_assoc] using
          hterminal (extra ++ [h]) hlen q hq
      have hsq := norm_sum_iteratedPowerDifference_sq_le
        k L T t hs m
      have hsum :
          (∑ h ∈ Finset.range m,
            ‖∑ n ∈ Finset.range (m - h - 1),
              phase (normalizedPower k L T) (-(t : ℤ))
                (iteratedPowerDifference k L (h :: hs) n)‖) ≤
            (m : ℝ) * finiteWeylEnvelope N R d := by
        calc
          _ ≤ ∑ _h ∈ Finset.range m, finiteWeylEnvelope N R d := by
            apply Finset.sum_le_sum
            intro h hh
            exact hchild h hh
          _ = (m : ℝ) * finiteWeylEnvelope N R d := by simp
      rw [finiteWeylEnvelope]
      apply Real.le_sqrt_of_sq_le
      calc
        ‖∑ n ∈ Finset.range m,
            phase (normalizedPower k L T) (-(t : ℤ))
              (iteratedPowerDifference k L hs n)‖ ^ 2 ≤
            (m : ℝ) + 2 *
              ∑ h ∈ Finset.range m,
                ‖∑ n ∈ Finset.range (m - h - 1),
                  phase (normalizedPower k L T) (-(t : ℤ))
                    (iteratedPowerDifference k L (h :: hs) n)‖ := by
          exact_mod_cast hsq
        _ ≤ (m : ℝ) + 2 * ((m : ℝ) * finiteWeylEnvelope N R d) := by
          gcongr
        _ ≤ (N : ℝ) + 2 * (N : ℝ) * finiteWeylEnvelope N R d := by
          have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
          have henv := finiteWeylEnvelope_nonneg N hR d
          nlinarith

/-- For each fixed differencing depth, sufficiently small terminal sums give
an arbitrarily small starting sum once the ambient interval is long.  This
is the quantitative induction hidden in the usual qualitative Weyl lemma. -/
theorem exists_terminal_ratio_for_finiteWeylEnvelope (d : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ B : ℕ, ∀ N ≥ B, ∀ R : ℝ,
      0 ≤ R → R ≤ δ * N →
        finiteWeylEnvelope N R d ≤ ε * N := by
  induction d generalizing ε with
  | zero =>
      refine ⟨ε, hε, 0, ?_⟩
      intro N hN R hR hbound
      simpa [finiteWeylEnvelope] using hbound
  | succ d ih =>
      have hquarter : 0 < ε ^ 2 / 4 := by positivity
      obtain ⟨δ, hδ, B, hB⟩ := ih (ε ^ 2 / 4) hquarter
      obtain ⟨B₀, hB₀⟩ := exists_nat_gt (4 / ε ^ 2)
      refine ⟨δ, hδ, max B B₀, ?_⟩
      intro N hN R hR hbound
      have hNB : B ≤ N := le_trans (Nat.le_max_left _ _) hN
      have hNB₀ : B₀ ≤ N := le_trans (Nat.le_max_right _ _) hN
      have hind : finiteWeylEnvelope N R d ≤ (ε ^ 2 / 4) * N :=
        hB N hNB R hR hbound
      have hB₀R : (4 : ℝ) / ε ^ 2 < N :=
        lt_of_lt_of_le hB₀ (by exact_mod_cast hNB₀)
      have hfour : (4 : ℝ) < ε ^ 2 * N := by
        simpa [mul_comm] using
          (div_lt_iff₀ (sq_pos_of_pos hε)).mp hB₀R
      rw [finiteWeylEnvelope, Real.sqrt_le_iff]
      constructor
      · positivity
      · have hNnonneg : (0 : ℝ) ≤ N := by positivity
        calc
          (N : ℝ) + 2 * (N : ℝ) * finiteWeylEnvelope N R d ≤
              (N : ℝ) + 2 * (N : ℝ) * ((ε ^ 2 / 4) * N) := by
            gcongr
          _ ≤ (ε * N) ^ 2 := by nlinarith

/-- A character evaluated on an integral natural multiple is a power of the
character at the multiplier. -/
theorem phase_mul_right_nat (T : ℕ) (t c : ℤ) (n : ℕ) :
    phase T t (c * n) = phase T t c ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, mul_add, phase_add_right, ih, pow_succ]
      simp

/-- A degree-at-most-one formal polynomial phase is a constant times an
ordinary geometric progression. -/
theorem sum_phase_linearPolynomial (T : ℕ) (t : ℤ) (P : ℤ[X])
    (hdegree : P.natDegree ≤ 1) (m : ℕ) :
    (∑ n ∈ Finset.range m, phase T t (P.eval n)) =
      phase T t (P.coeff 0) *
        ∑ n ∈ Finset.range m, phase T t (P.coeff 1) ^ n := by
  have hrepr := Polynomial.eq_X_add_C_of_natDegree_le_one hdegree
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have heval : P.eval (n : ℤ) = P.coeff 1 * n + P.coeff 0 := by
    calc
      P.eval (n : ℤ) =
          (Polynomial.C (P.coeff 1) * Polynomial.X +
            Polynomial.C (P.coeff 0)).eval (n : ℤ) :=
        congrArg (fun Q : ℤ[X] ↦ Q.eval (n : ℤ)) hrepr
      _ = P.coeff 1 * n + P.coeff 0 := by simp
  rw [heval, phase_add_right, phase_mul_right_nat]
  ring

/-- Geometric-series bound in a normed field, specialized to unit-modulus
ratios. -/
theorem norm_geom_sum_le_two_div (r : ℂ) (hrnorm : ‖r‖ = 1)
    (hr : r ≠ 1) (m : ℕ) :
    ‖∑ n ∈ Finset.range m, r ^ n‖ ≤ 2 / ‖1 - r‖ := by
  have hdenom : 0 < ‖1 - r‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hr.symm)
  apply (le_div_iff₀ hdenom).2
  rw [← norm_mul]
  rw [geom_sum_mul_neg]
  calc
    ‖1 - r ^ m‖ ≤ ‖(1 : ℂ)‖ + ‖r ^ m‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_one, norm_pow, hrnorm, one_pow]; norm_num

/-- Linear polynomial phases inherit the geometric-series bound; their
constant term has norm one. -/
theorem norm_sum_phase_linearPolynomial_le (T : ℕ) (t : ℤ) (P : ℤ[X])
    (hdegree : P.natDegree ≤ 1)
    (hr : phase T t (P.coeff 1) ≠ 1) (m : ℕ) :
    ‖∑ n ∈ Finset.range m, phase T t (P.eval n)‖ ≤
      2 / ‖1 - phase T t (P.coeff 1)‖ := by
  rw [sum_phase_linearPolynomial T t P hdegree m, norm_mul,
    norm_phase, one_mul]
  exact norm_geom_sum_le_two_div _ (norm_phase T t (P.coeff 1)) hr m

/-! ### The aggregate Weyl tree

The maximum-over-histories envelope above is useful when every leaf has the
same bound.  Polynomial Weyl sums instead require retaining the average over
shift products.  The following recursive aggregates formalize that tree. -/

noncomputable def powerWeylAggregate
    (k L T t : ℕ) (hs : List ℕ) (m : ℕ) : ℕ → ℝ
  | 0 => ‖∑ n ∈ Finset.range m,
      phase (normalizedPower k L T) (-(t : ℤ))
        (iteratedPowerDifference k L hs n)‖
  | d + 1 => ∑ h ∈ Finset.range m,
      powerWeylAggregate k L T t (h :: hs) (m - h - 1) d

noncomputable def powerWeylSquareAggregate
    (k L T t : ℕ) (hs : List ℕ) (m : ℕ) : ℕ → ℝ
  | 0 => ‖∑ n ∈ Finset.range m,
      phase (normalizedPower k L T) (-(t : ℤ))
        (iteratedPowerDifference k L hs n)‖ ^ 2
  | d + 1 => ∑ h ∈ Finset.range m,
      powerWeylSquareAggregate k L T t (h :: hs) (m - h - 1) d

noncomputable def powerWeylLengthAggregate (m : ℕ) : ℕ → ℝ
  | 0 => m
  | d + 1 => ∑ h ∈ Finset.range m,
      powerWeylLengthAggregate (m - h - 1) d

theorem powerWeylAggregate_nonneg
    (k L T t : ℕ) (hs : List ℕ) (m d : ℕ) :
    0 ≤ powerWeylAggregate k L T t hs m d := by
  induction d generalizing hs m with
  | zero => simp [powerWeylAggregate]
  | succ d ih =>
      simp only [powerWeylAggregate]
      exact Finset.sum_nonneg fun h hh ↦ ih (h :: hs) (m - h - 1)

theorem powerWeylSquareAggregate_nonneg
    (k L T t : ℕ) (hs : List ℕ) (m d : ℕ) :
    0 ≤ powerWeylSquareAggregate k L T t hs m d := by
  induction d generalizing hs m with
  | zero => simp [powerWeylSquareAggregate]
  | succ d ih =>
      simp only [powerWeylSquareAggregate]
      exact Finset.sum_nonneg fun h hh ↦ ih (h :: hs) (m - h - 1)

/-- Cauchy--Schwarz on all valid histories at a fixed depth. -/
theorem powerWeylAggregate_sq_le
    (k L T t : ℕ) (hs : List ℕ) (m d : ℕ) :
    powerWeylAggregate k L T t hs m d ^ 2 ≤
      (m : ℝ) ^ d * powerWeylSquareAggregate k L T t hs m d := by
  induction d generalizing hs m with
  | zero => simp [powerWeylAggregate, powerWeylSquareAggregate]
  | succ d ih =>
      have hcauchy := sq_sum_le_card_mul_sum_sq
        (s := Finset.range m)
        (f := fun h ↦ powerWeylAggregate k L T t
          (h :: hs) (m - h - 1) d)
      have hterm :
          (∑ h ∈ Finset.range m,
            powerWeylAggregate k L T t (h :: hs) (m - h - 1) d ^ 2) ≤
          (m : ℝ) ^ d *
            ∑ h ∈ Finset.range m,
              powerWeylSquareAggregate k L T t
                (h :: hs) (m - h - 1) d := by
        calc
          _ ≤ ∑ h ∈ Finset.range m,
              ((m - h - 1 : ℕ) : ℝ) ^ d *
                powerWeylSquareAggregate k L T t
                  (h :: hs) (m - h - 1) d := by
            apply Finset.sum_le_sum
            intro h hh
            exact ih (h :: hs) (m - h - 1)
          _ ≤ ∑ h ∈ Finset.range m,
              (m : ℝ) ^ d *
                powerWeylSquareAggregate k L T t
                  (h :: hs) (m - h - 1) d := by
            apply Finset.sum_le_sum
            intro h hh
            apply mul_le_mul_of_nonneg_right
            · gcongr
              exact_mod_cast Nat.sub_le m (h + 1)
            · exact powerWeylSquareAggregate_nonneg k L T t
                (h :: hs) (m - h - 1) d
          _ = (m : ℝ) ^ d *
              ∑ h ∈ Finset.range m,
                powerWeylSquareAggregate k L T t
                  (h :: hs) (m - h - 1) d := by
            rw [Finset.mul_sum]
      simp only [powerWeylAggregate, powerWeylSquareAggregate]
      calc
        (∑ h ∈ Finset.range m,
            powerWeylAggregate k L T t (h :: hs) (m - h - 1) d) ^ 2 ≤
            (m : ℝ) *
              ∑ h ∈ Finset.range m,
                powerWeylAggregate k L T t
                  (h :: hs) (m - h - 1) d ^ 2 := by
          simpa using hcauchy
        _ ≤ (m : ℝ) * ((m : ℝ) ^ d *
              ∑ h ∈ Finset.range m,
                powerWeylSquareAggregate k L T t
                  (h :: hs) (m - h - 1) d) := by
          gcongr
        _ = (m : ℝ) ^ (d + 1) *
              ∑ h ∈ Finset.range m,
                powerWeylSquareAggregate k L T t
                  (h :: hs) (m - h - 1) d := by
          rw [pow_succ']
          ring

/-- Summing the one-step Weyl inequality over every node at a fixed depth. -/
theorem powerWeylSquareAggregate_le
    (k L T t : ℕ) (hs : List ℕ) (m d : ℕ) :
    powerWeylSquareAggregate k L T t hs m d ≤
      powerWeylLengthAggregate m d +
        2 * powerWeylAggregate k L T t hs m (d + 1) := by
  induction d generalizing hs m with
  | zero =>
      simpa [powerWeylSquareAggregate, powerWeylLengthAggregate,
        powerWeylAggregate] using
          norm_sum_iteratedPowerDifference_sq_le k L T t hs m
  | succ d ih =>
      simp only [powerWeylSquareAggregate, powerWeylLengthAggregate,
        powerWeylAggregate]
      calc
        (∑ h ∈ Finset.range m,
            powerWeylSquareAggregate k L T t
              (h :: hs) (m - h - 1) d) ≤
            ∑ h ∈ Finset.range m,
              (powerWeylLengthAggregate (m - h - 1) d +
                2 * powerWeylAggregate k L T t
                  (h :: hs) (m - h - 1) (d + 1)) := by
          apply Finset.sum_le_sum
          intro h hh
          exact ih (h :: hs) (m - h - 1)
        _ = (∑ h ∈ Finset.range m,
              powerWeylLengthAggregate (m - h - 1) d) +
            2 * ∑ h ∈ Finset.range m,
              powerWeylAggregate k L T t
                (h :: hs) (m - h - 1) (d + 1) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The total remaining interval length at depth `d` has the crude but
uniform bound `m^(d+1)`. -/
theorem powerWeylLengthAggregate_le (m d : ℕ) :
    powerWeylLengthAggregate m d ≤ (m : ℝ) ^ (d + 1) := by
  induction d generalizing m with
  | zero => simp [powerWeylLengthAggregate]
  | succ d ih =>
      simp only [powerWeylLengthAggregate]
      calc
        (∑ h ∈ Finset.range m,
            powerWeylLengthAggregate (m - h - 1) d) ≤
            ∑ _h ∈ Finset.range m, (m : ℝ) ^ (d + 1) := by
          apply Finset.sum_le_sum
          intro h hh
          exact (ih (m - h - 1)).trans (by
            gcongr
            exact_mod_cast Nat.sub_le m (h + 1))
        _ = (m : ℝ) * (m : ℝ) ^ (d + 1) := by simp
        _ = (m : ℝ) ^ (d + 1 + 1) := by rw [pow_succ']; ring

/-- The standard aggregate Weyl recurrence at depth `d`. -/
theorem powerWeylAggregate_sq_le_next
    (k L T t : ℕ) (hs : List ℕ) (m d : ℕ) :
    powerWeylAggregate k L T t hs m d ^ 2 ≤
      (m : ℝ) ^ d *
        ((m : ℝ) ^ (d + 1) +
          2 * powerWeylAggregate k L T t hs m (d + 1)) := by
  exact (powerWeylAggregate_sq_le k L T t hs m d).trans
    (mul_le_mul_of_nonneg_left
      ((powerWeylSquareAggregate_le k L T t hs m d).trans
        (add_le_add (powerWeylLengthAggregate_le m d) le_rfl))
      (by positivity))

/-- If the depth-`j+r` aggregate is at most `N^(j+r) R`, then the
depth-`j` aggregate is controlled by the ordinary Weyl envelope, with the
expected factor `N^j`. -/
theorem powerWeylAggregate_le_scaledEnvelope
    (k L T t N : ℕ) (hs : List ℕ) (m j r : ℕ) (R : ℝ)
    (hm : m ≤ N) (hR : 0 ≤ R)
    (hterminal : powerWeylAggregate k L T t hs m (j + r) ≤
      (N : ℝ) ^ (j + r) * R) :
    powerWeylAggregate k L T t hs m j ≤
      (N : ℝ) ^ j * finiteWeylEnvelope N R r := by
  induction r generalizing j with
  | zero =>
      simpa [finiteWeylEnvelope] using hterminal
  | succ r ih =>
      have hnext : powerWeylAggregate k L T t hs m (j + 1) ≤
          (N : ℝ) ^ (j + 1) * finiteWeylEnvelope N R r := by
        apply ih (j + 1)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hterminal
      have hsq := powerWeylAggregate_sq_le_next k L T t hs m j
      have henv : 0 ≤ finiteWeylEnvelope N R r :=
        finiteWeylEnvelope_nonneg N hR r
      have hsqrt :
          Real.sqrt ((N : ℝ) + 2 * N * finiteWeylEnvelope N R r) ^ 2 =
            (N : ℝ) + 2 * N * finiteWeylEnvelope N R r :=
        Real.sq_sqrt (by positivity)
      rw [finiteWeylEnvelope]
      have hsq' : powerWeylAggregate k L T t hs m j ^ 2 ≤
          ((N : ℝ) ^ j *
            Real.sqrt ((N : ℝ) +
              2 * N * finiteWeylEnvelope N R r)) ^ 2 := by
        calc
          powerWeylAggregate k L T t hs m j ^ 2 ≤
              (m : ℝ) ^ j *
                ((m : ℝ) ^ (j + 1) +
                  2 * powerWeylAggregate k L T t hs m (j + 1)) := hsq
          _ ≤ (N : ℝ) ^ j *
                ((N : ℝ) ^ (j + 1) +
                  2 * ((N : ℝ) ^ (j + 1) *
                    finiteWeylEnvelope N R r)) := by
            have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
            have hagg : 0 ≤ powerWeylAggregate k L T t hs m (j + 1) :=
              powerWeylAggregate_nonneg k L T t hs m (j + 1)
            gcongr
          _ = ((N : ℝ) ^ j *
              Real.sqrt ((N : ℝ) +
                2 * N * finiteWeylEnvelope N R r)) ^ 2 := by
            rw [mul_pow, hsqrt]
            ring
      have hnonneg := powerWeylAggregate_nonneg k L T t hs m j
      have hright : 0 ≤ (N : ℝ) ^ j *
          Real.sqrt ((N : ℝ) + 2 * N * finiteWeylEnvelope N R r) := by
        positivity
      nlinarith

/-! ### Linear leaves of the power Weyl tree -/

/-- After `k-1` positive differences, a degree-`k` normalized power is
exactly linear. -/
theorem natDegree_iteratedNormalizedPower_eq_one
    (k L : ℕ) (hk : 2 ≤ k) (hL : 0 < L) (hs : List ℕ)
    (hlen : hs.length = k - 1) :
    (iteratedPolynomialDifference (normalizedPowerPolynomial k L) hs).natDegree = 1 := by
  have hshort : hs.length <
      (normalizedPowerPolynomial k L).natDegree := by
    rw [natDegree_normalizedPowerPolynomial k L hk hL, hlen]
    omega
  rw [natDegree_iteratedPolynomialDifference _ hs hshort,
    natDegree_normalizedPowerPolynomial k L hk hL, hlen]
  omega

/-- Exact linear coefficient at a terminal power-polynomial leaf. -/
theorem leadingCoeff_iteratedNormalizedPower
    (k L : ℕ) (hk : 2 ≤ k) (hL : 0 < L) (hs : List ℕ)
    (hlen : hs.length = k - 1) :
    (iteratedPolynomialDifference
        (normalizedPowerPolynomial k L) hs).leadingCoeff =
      (powerDerivative k ^ (k - 2) * L ^ (k - 1) : ℕ) *
        (k.descFactorial (k - 1) : ℕ) *
          (hs.map fun h ↦ ((h + 1 : ℕ) : ℤ)).prod := by
  have hdegree := natDegree_normalizedPowerPolynomial k L hk hL
  have hshort : hs.length <
      (normalizedPowerPolynomial k L).natDegree := by
    rw [hdegree, hlen]
    omega
  have hlead : (normalizedPowerPolynomial k L).leadingCoeff =
      (powerDerivative k ^ (k - 2) * L ^ (k - 1) : ℕ) := by
    rw [Polynomial.leadingCoeff, hdegree,
      coeff_normalizedPowerPolynomial_top k L hk]
  rw [leadingCoeff_iteratedPolynomialDifference _ hs hshort,
    hlead, hdegree, hlen]

/-- A safe majorant for every prefix of a unit-modulus geometric
progression.  The exceptional ratio `1` is handled by the trivial bound. -/
noncomputable def unitGeomMajorant (N : ℕ) (r : ℂ) : ℝ :=
  if r = 1 then N else min N (2 / ‖1 - r‖)

theorem unitGeomMajorant_nonneg (N : ℕ) (r : ℂ) :
    0 ≤ unitGeomMajorant N r := by
  unfold unitGeomMajorant
  split_ifs
  · positivity
  · exact le_min (by positivity) (by positivity)

/-! The real-frequency form of the terminal geometric majorant.  It is
convenient for Dirichlet approximation because its denominator is the
distance to the nearest integer. -/

/-- Distance from a real number to the nearest integer. -/
noncomputable def nearestIntegerDistance (x : ℝ) : ℝ :=
  |x - (round x : ℝ)|

theorem nearestIntegerDistance_nonneg (x : ℝ) :
    0 ≤ nearestIntegerDistance x := abs_nonneg _

theorem nearestIntegerDistance_eq_circleNorm (x : ℝ) :
    nearestIntegerDistance x = ‖(x : AddCircle (1 : ℝ))‖ := by
  rw [AddCircle.norm_eq]
  simp [nearestIntegerDistance]

theorem nearestIntegerDistance_neg (x : ℝ) :
    nearestIntegerDistance (-x) = nearestIntegerDistance x := by
  rw [nearestIntegerDistance_eq_circleNorm,
    nearestIntegerDistance_eq_circleNorm]
  change ‖-(x : AddCircle (1 : ℝ))‖ = ‖(x : AddCircle (1 : ℝ))‖
  exact norm_neg _

/-- The chord of the circle character controls distance to the nearest
integer. -/
theorem four_mul_nearestIntegerDistance_le_chord (x : ℝ) :
    4 * nearestIntegerDistance x ≤
      ‖((Real.fourierChar x : Circle) : ℂ) - 1‖ := by
  let y := x - (round x : ℝ)
  have hy : |y| ≤ 1 / 2 := by
    simpa [y] using (abs_sub_round x)
  have harg : |Real.pi * y| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin harg
  have hscale : 2 / Real.pi * |Real.pi * y| = 2 * |y| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp [Real.pi_ne_zero]
  have hreal : 4 * |y| ≤ 2 * |Real.sin (Real.pi * y)| := by
    rw [hscale] at hsin
    nlinarith
  have hchar :
      ((Real.fourierChar y : Circle) : ℂ) =
        ((Real.fourierChar x : Circle) : ℂ) := by
    rw [show y = x - (round x : ℝ) by rfl,
      AddChar.map_sub_eq_div, Circle.coe_div]
    have hr : ((Real.fourierChar (round x : ℝ) : Circle) : ℂ) = 1 := by
      rw [Real.fourierChar_apply]
      rw [show (↑(2 * Real.pi * (round x : ℝ)) : ℂ) * Complex.I =
          ((round x : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        push_cast
        ring]
      exact Complex.exp_int_mul_two_pi_mul_I (round x)
    rw [hr, div_one]
  rw [← hchar]
  change 4 * |y| ≤ ‖((Real.fourierChar y : Circle) : ℂ) - 1‖
  rw [Real.fourierChar_apply]
  rw [show (↑(2 * Real.pi * y) : ℂ) * Complex.I =
      Complex.I * (2 * Real.pi * y : ℝ) by
    push_cast
    ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  norm_num [abs_mul]
  simpa [mul_assoc] using hreal

/-- The zero-safe real-frequency version of the geometric majorant. -/
noncomputable def realGeomMajorant (N : ℕ) (x : ℝ) : ℝ :=
  if nearestIntegerDistance x = 0 then N
  else min N (1 / (2 * nearestIntegerDistance x))

theorem realGeomMajorant_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ realGeomMajorant N x := by
  unfold realGeomMajorant
  split_ifs with h
  · positivity
  · have hdist : 0 < nearestIntegerDistance x :=
      (nearestIntegerDistance_nonneg x).lt_of_ne' h
    exact le_min (by positivity) (by positivity)

theorem realGeomMajorant_neg (N : ℕ) (x : ℝ) :
    realGeomMajorant N (-x) = realGeomMajorant N x := by
  simp only [realGeomMajorant, nearestIntegerDistance_neg]

/-- The finite character used above is the ordinary real circle character
at the corresponding rational frequency. -/
theorem phase_eq_realFourier (T t : ℕ) (c : ℤ) (hT : 0 < T) :
    phase T (-(t : ℤ)) c =
      ((Real.fourierChar (-(t : ℝ) * (c : ℝ) / T) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply]
  unfold phase
  congr 1
  push_cast
  field_simp

/-- The complex-ratio majorant is bounded by the nearest-integer form. -/
theorem unitGeomMajorant_le_realGeomMajorant
    (T t N : ℕ) (c : ℤ) (hT : 0 < T) :
    unitGeomMajorant N (phase T (-(t : ℤ)) c) ≤
      realGeomMajorant N (-(t : ℝ) * (c : ℝ) / T) := by
  let x : ℝ := -(t : ℝ) * (c : ℝ) / T
  have hphase : phase T (-(t : ℤ)) c =
      ((Real.fourierChar x : Circle) : ℂ) := by
    simpa only [x] using phase_eq_realFourier T t c hT
  by_cases hx : nearestIntegerDistance x = 0
  · rw [realGeomMajorant, if_pos hx]
    unfold unitGeomMajorant
    split_ifs
    · exact le_rfl
    · exact (min_le_left _ _)
  · rw [realGeomMajorant, if_neg hx, unitGeomMajorant]
    have hdist : 0 < nearestIntegerDistance x :=
      (nearestIntegerDistance_nonneg x).lt_of_ne' hx
    have hchord :
        4 * nearestIntegerDistance x ≤
          ‖1 - phase T (-(t : ℤ)) c‖ := by
      rw [hphase, norm_sub_rev]
      exact four_mul_nearestIntegerDistance_le_chord x
    have hphaseOne : phase T (-(t : ℤ)) c ≠ 1 := by
      intro heq
      rw [heq, sub_self, norm_zero] at hchord
      nlinarith
    rw [if_neg hphaseOne]
    apply min_le_min le_rfl
    have hchordPos : 0 < ‖1 - phase T (-(t : ℤ)) c‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hphaseOne.symm)
    rw [div_le_div_iff₀ hchordPos (by positivity :
      0 < 2 * nearestIntegerDistance x)]
    nlinarith

theorem nearestIntegerDistance_le_add_abs_sub (x y : ℝ) :
    nearestIntegerDistance x ≤ |x - y| + nearestIntegerDistance y := by
  have htri :
      ‖(x : AddCircle (1 : ℝ))‖ ≤
        ‖((x - y : ℝ) : AddCircle (1 : ℝ))‖ +
          ‖(y : AddCircle (1 : ℝ))‖ := by
    convert norm_add_le (((x - y : ℝ) : AddCircle (1 : ℝ)))
      ((y : ℝ) : AddCircle (1 : ℝ)) using 1 <;> simp
  rw [show nearestIntegerDistance x = ‖(x : AddCircle (1 : ℝ))‖ by
      rw [AddCircle.norm_eq]
      simp [nearestIntegerDistance],
    show nearestIntegerDistance y = ‖(y : AddCircle (1 : ℝ))‖ by
      rw [AddCircle.norm_eq]
      simp [nearestIntegerDistance]]
  refine htri.trans (add_le_add ?_ le_rfl)
  rw [AddCircle.norm_eq]
  simpa using (round_le (x - y) 0)

/-- Exact nearest-integer distance of a rational number with natural
numerator and positive denominator. -/
theorem nearestIntegerDistance_nat_div (m b : ℕ) :
    nearestIntegerDistance ((m : ℝ) / b) =
      (min (m % b) (b - m % b) : ℕ) / (b : ℝ) := by
  simpa [nearestIntegerDistance] using
    (abs_sub_round_div_natCast_eq (α := ℝ) (m := m) (n := b))

/-- Dirichlet approximation with a reduced numerator and denominator. -/
theorem dirichletApproximationReduced (θ : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ (a : ℤ) (b : ℕ),
      1 ≤ b ∧ b ≤ Q ∧ Nat.Coprime a.natAbs b ∧
        |θ - (a : ℝ) / (b : ℝ)| ≤ 1 / ((b : ℝ) * (Q : ℝ)) := by
  obtain ⟨q, happrox, hden⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le θ (by omega : 0 < Q)
  refine ⟨q.num, q.den, q.den_pos, hden, q.reduced, ?_⟩
  have hcast : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
    exact_mod_cast q.num_div_den.symm
  rw [hcast] at happrox
  refine happrox.trans ?_
  have hb : (0 : ℝ) < q.den := by positivity
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  apply one_div_le_one_div_of_le (mul_pos hb hQr)
  nlinarith

/-- At a nonnegative frequency and cutoff at least two, the reduced
Dirichlet numerator is nonnegative. -/
theorem dirichletApproximationReducedNat (θ : ℝ) (Q : ℕ)
    (hθ : 0 ≤ θ) (hQ : 2 ≤ Q) :
    ∃ (a b : ℕ), 1 ≤ b ∧ b ≤ Q ∧ a.Coprime b ∧
      |θ - (a : ℝ) / (b : ℝ)| ≤ 1 / ((b : ℝ) * (Q : ℝ)) := by
  obtain ⟨a, b, hb1, hbQ, hab, happ⟩ :=
    dirichletApproximationReduced θ Q (by omega)
  have ha0 : 0 ≤ a := by
    by_contra hneg
    have ha1 : a ≤ -1 := by omega
    have hbR : (0 : ℝ) < b := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb1)
    have hQR : (1 : ℝ) < Q := by exact_mod_cast hQ
    have haR : (a : ℝ) ≤ -1 := by exact_mod_cast ha1
    have hdiff : 1 / (b : ℝ) ≤ θ - (a : ℝ) / b := by
      have hle : (a : ℝ) / b ≤ -1 / b :=
        (div_le_div_iff_of_pos_right hbR).2 haR
      have hnegdiv : 1 / (b : ℝ) ≤ -((a : ℝ) / b) := by
        calc
          1 / (b : ℝ) = -(-1 / b) := by ring
          _ ≤ -((a : ℝ) / b) := neg_le_neg hle
      calc
        1 / (b : ℝ) ≤ θ + 1 / b := le_add_of_nonneg_left hθ
        _ ≤ θ - (a : ℝ) / b := by
          rw [sub_eq_add_neg]
          simpa only [add_comm] using add_le_add_left hnegdiv θ
    have hdiff0 : 0 ≤ θ - (a : ℝ) / b :=
      le_trans (by positivity) hdiff
    have habs : 1 / (b : ℝ) ≤ |θ - (a : ℝ) / b| := by
      rwa [abs_of_nonneg hdiff0]
    have hstrict : 1 / ((b : ℝ) * Q) < 1 / b := by
      rw [one_div_lt_one_div (mul_pos hbR (by positivity)) hbR]
      nlinarith
    exact (not_lt_of_ge (habs.trans happ)) hstrict
  refine ⟨a.natAbs, b, hb1, hbQ, hab, ?_⟩
  have hcast : ((a.natAbs : ℕ) : ℝ) = (a : ℝ) := by
    rw [← Int.cast_natCast]
    exact_mod_cast Int.natAbs_of_nonneg ha0
  rwa [hcast]

/-- Least unsigned residue of `a*m` modulo `b`. -/
def rationalResidueDistance (a b m : ℕ) : ℕ :=
  min ((a * m) % b) (b - (a * m) % b)

/-- Rational-grid majorant corresponding to `realGeomMajorant`. -/
noncomputable def rationalGeomMajorant
    (a b N m : ℕ) : ℝ :=
  if rationalResidueDistance a b m = 0 then N
  else (b : ℝ) / rationalResidueDistance a b m

theorem rationalGeomMajorant_nonneg (a b N m : ℕ) :
    0 ≤ rationalGeomMajorant a b N m := by
  unfold rationalGeomMajorant
  split_ifs <;> positivity

/-- A subset of `[1,X]` in one residue class modulo `h` has at most
`X / h + 1` elements. -/
theorem card_le_div_add_one_of_pairwise_modEq {s : Finset ℕ} {X h : ℕ}
    (hsX : s ⊆ Finset.Icc 1 X) (_hh : 0 < h)
    (hmod : ∀ a ∈ s, ∀ b ∈ s, a ≡ b [MOD h]) :
    s.card ≤ X / h + 1 := by
  let f : ℕ → ℕ := fun a ↦ a / h
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    have hrem : a % h = b % h := hmod a ha b hb
    have hda : h * (a / h) + a % h = a := Nat.div_add_mod a h
    have hdb : h * (b / h) + b % h = b := Nat.div_add_mod b h
    dsimp [f] at hab
    calc
      a = h * (a / h) + a % h := hda.symm
      _ = h * (b / h) + b % h := by rw [hab, hrem]
      _ = b := hdb
  have himage : s.image f ⊆ Finset.range (X / h + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range]
    have haX : a ≤ X := (Finset.mem_Icc.mp (hsX ha)).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right haX)
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (X / h + 1)).card := Finset.card_le_card himage
    _ = X / h + 1 := Finset.card_range _

/-- Fibre of a fixed twisted residue in the positive interval. -/
def rationalResidueFiber (a b X r : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun m => (a * m) % b = r

theorem card_rationalResidueFiber_le (a b X r : ℕ) (hb : 0 < b)
    (ha : a.Coprime b) :
    (rationalResidueFiber a b X r).card ≤ X / b + 1 := by
  apply card_le_div_add_one_of_pairwise_modEq
    (fun m hm => Finset.filter_subset _ _ hm) hb
  intro x hx y hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hmod : a * x ≡ a * y [MOD b] := hx'.trans hy'.symm
  have hba : b.gcd a = 1 := by
    simpa [Nat.gcd_comm] using ha.gcd_eq_one
  exact Nat.ModEq.cancel_left_of_coprime hba hmod

/-- Fibre of a fixed unsigned rational residue distance. -/
def rationalDistanceFiber (a b X d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun m => rationalResidueDistance a b m = d

theorem rationalDistanceFiber_zero_subset (a b X : ℕ) (hb : 0 < b) :
    rationalDistanceFiber a b X 0 ⊆ rationalResidueFiber a b X 0 := by
  intro m hm
  have hm' := Finset.mem_filter.mp hm
  apply Finset.mem_filter.mpr
  refine ⟨hm'.1, ?_⟩
  have hrlt : (a * m) % b < b := Nat.mod_lt _ hb
  dsimp [rationalResidueDistance] at hm'
  omega

theorem rationalDistanceFiber_subset_union (a b X d : ℕ) (hb : 0 < b) :
    rationalDistanceFiber a b X d ⊆
      rationalResidueFiber a b X d ∪
        rationalResidueFiber a b X (b - d) := by
  intro m hm
  have hm' := Finset.mem_filter.mp hm
  have hd := hm'.2
  let r := (a * m) % b
  change min r (b - r) = d at hd
  by_cases hle : r ≤ b - r
  · have hre : r = d := by simpa [min_eq_left hle] using hd
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hm'.1, hre⟩
  · have hre : r = b - d := by
      have hd' : b - r = d := by
        simpa [min_eq_right (Nat.le_of_not_ge hle)] using hd
      have hrle : r ≤ b := Nat.le_of_lt (Nat.mod_lt _ hb)
      omega
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hm'.1, hre⟩

theorem card_rationalDistanceFiber_zero_le (a b X : ℕ) (hb : 0 < b)
    (ha : a.Coprime b) :
    (rationalDistanceFiber a b X 0).card ≤ X / b + 1 := by
  exact (Finset.card_le_card
    (rationalDistanceFiber_zero_subset a b X hb)).trans
      (card_rationalResidueFiber_le a b X 0 hb ha)

theorem card_rationalDistanceFiber_le (a b X d : ℕ) (hb : 0 < b)
    (ha : a.Coprime b) :
    (rationalDistanceFiber a b X d).card ≤ 2 * (X / b + 1) := by
  calc
    (rationalDistanceFiber a b X d).card ≤
        (rationalResidueFiber a b X d ∪
          rationalResidueFiber a b X (b - d)).card :=
      Finset.card_le_card (rationalDistanceFiber_subset_union a b X d hb)
    _ ≤ (rationalResidueFiber a b X d).card +
        (rationalResidueFiber a b X (b - d)).card := Finset.card_union_le _ _
    _ ≤ (X / b + 1) + (X / b + 1) :=
      Nat.add_le_add (card_rationalResidueFiber_le a b X d hb ha)
        (card_rationalResidueFiber_le a b X (b - d) hb ha)
    _ = 2 * (X / b + 1) := by ring

theorem rationalResidueDistance_le (a b m : ℕ) (hb : 0 < b) :
    rationalResidueDistance a b m ≤ b := by
  have hr := Nat.mod_lt (a * m) hb
  simp only [rationalResidueDistance]
  omega

/-- Exact grouping of the rational majorants by unsigned residue distance. -/
theorem sum_rationalGeomMajorant_eq_fibers (a b N X : ℕ) (hb : 0 < b) :
    (∑ m ∈ Finset.Icc 1 X, rationalGeomMajorant a b N m) =
      ((rationalDistanceFiber a b X 0).card : ℝ) * N +
        ∑ d ∈ Finset.Icc 1 b,
          ((rationalDistanceFiber a b X d).card : ℝ) * ((b : ℝ) / d) := by
  let s := Finset.Icc 1 X
  let s0 := s.filter fun m => rationalResidueDistance a b m = 0
  let s1 := s.filter fun m => rationalResidueDistance a b m ≠ 0
  have hmaps : ∀ m ∈ s1,
      rationalResidueDistance a b m ∈ Finset.Icc 1 b := by
    intro m hm
    have hm' := Finset.mem_filter.mp hm
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm'.2,
      rationalResidueDistance_le a b m hb⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun m => rationalGeomMajorant a b N m)
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun m => rationalResidueDistance a b m = 0)
    (fun m => rationalGeomMajorant a b N m)
  calc
    (∑ m ∈ Finset.Icc 1 X, rationalGeomMajorant a b N m) =
        (∑ m ∈ s0, rationalGeomMajorant a b N m) +
          ∑ m ∈ s1, rationalGeomMajorant a b N m := by
      simpa [s, s0, s1] using hsplit.symm
    _ = ((s0.card : ℕ) : ℝ) * N +
          ∑ m ∈ s1, rationalGeomMajorant a b N m := by
      congr 1
      calc
        (∑ m ∈ s0, rationalGeomMajorant a b N m) =
            ∑ _m ∈ s0, (N : ℝ) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [rationalGeomMajorant,
            if_pos (Finset.mem_filter.mp hm).2]
        _ = ((s0.card : ℕ) : ℝ) * N := by simp
    _ = ((s0.card : ℕ) : ℝ) * N +
          ∑ d ∈ Finset.Icc 1 b,
            ∑ m ∈ s1 with rationalResidueDistance a b m = d,
              rationalGeomMajorant a b N m := by
      congr 1
      exact hfiber.symm
    _ = ((rationalDistanceFiber a b X 0).card : ℝ) * N +
          ∑ d ∈ Finset.Icc 1 b,
            ((rationalDistanceFiber a b X d).card : ℝ) *
              ((b : ℝ) / d) := by
      have hs0 : s0 = rationalDistanceFiber a b X 0 := by rfl
      rw [hs0]
      apply congrArg (fun z : ℝ =>
        ((rationalDistanceFiber a b X 0).card : ℝ) * N + z)
      apply Finset.sum_congr rfl
      intro d hd
      have hd0 : d ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hd).1
      have hset :
          (s1.filter fun m => rationalResidueDistance a b m = d) =
            rationalDistanceFiber a b X d := by
        ext m
        simp only [s1, s, rationalDistanceFiber, Finset.mem_filter,
          Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hI, hn0⟩, heq⟩
          exact ⟨hI, heq⟩
        · rintro ⟨hI, heq⟩
          refine ⟨⟨hI, ?_⟩, heq⟩
          intro hz
          apply hd0
          exact heq.symm.trans hz
      rw [hset]
      calc
        (∑ m ∈ rationalDistanceFiber a b X d,
            rationalGeomMajorant a b N m) =
            ∑ _m ∈ rationalDistanceFiber a b X d,
              ((b : ℝ) / d) := by
          apply Finset.sum_congr rfl
          intro m hm
          have heq := (Finset.mem_filter.mp hm).2
          rw [rationalGeomMajorant, if_neg]
          · rw [heq]
          · intro hz
            exact hd0 (heq.symm.trans hz)
        _ = ((rationalDistanceFiber a b X d).card : ℝ) *
              ((b : ℝ) / d) := by simp

theorem sum_Icc_inv_natCast_le_one_add_log (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, ((d : ℝ)⁻¹)) ≤ 1 + Real.log n := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using harmonic_le_one_add_log n

theorem sum_Icc_natCast_div_le (q n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, (q : ℝ) / d) ≤
      q * (1 + Real.log n) := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_Icc_inv_natCast_le_one_add_log n)
    (Nat.cast_nonneg q)

/-- Harmonic aggregation of a complete rational grid. -/
theorem sum_rationalGeomMajorant_le (a b N X : ℕ) (hb : 0 < b)
    (ha : a.Coprime b) :
    (∑ m ∈ Finset.Icc 1 X, rationalGeomMajorant a b N m) ≤
      ((X : ℝ) / b + 1) * N +
        2 * (X + b) * (1 + Real.log b) := by
  rw [sum_rationalGeomMajorant_eq_fibers a b N X hb]
  have hzero : ((rationalDistanceFiber a b X 0).card : ℝ) ≤
      (X : ℝ) / b + 1 := by
    calc
      ((rationalDistanceFiber a b X 0).card : ℝ) ≤
          (X / b + 1 : ℕ) := by
        exact_mod_cast card_rationalDistanceFiber_zero_le a b X hb ha
      _ ≤ (X : ℝ) / b + 1 := by
        push_cast
        gcongr
        exact Nat.cast_div_le
  have hnonzero :
      (∑ d ∈ Finset.Icc 1 b,
          ((rationalDistanceFiber a b X d).card : ℝ) *
            ((b : ℝ) / d)) ≤
        2 * (X + b) * (1 + Real.log b) := by
    calc
      (∑ d ∈ Finset.Icc 1 b,
          ((rationalDistanceFiber a b X d).card : ℝ) *
            ((b : ℝ) / d)) ≤
          ∑ d ∈ Finset.Icc 1 b,
            (2 * (X / b + 1) : ℕ) * ((b : ℝ) / d) := by
        apply Finset.sum_le_sum
        intro d hd
        gcongr
        exact_mod_cast card_rationalDistanceFiber_le a b X d hb ha
      _ = (2 * (X / b + 1) : ℕ) *
          ∑ d ∈ Finset.Icc 1 b, ((b : ℝ) / d) := by
        rw [Finset.mul_sum]
      _ ≤ (2 * (X / b + 1) : ℕ) *
          (b * (1 + Real.log b)) := by
        gcongr
        exact sum_Icc_natCast_div_le b b
      _ ≤ 2 * (X + b) * (1 + Real.log b) := by
        have hlog : 0 ≤ 1 + Real.log (b : ℝ) := by
          have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
          linarith [Real.log_nonneg hb1]
        push_cast
        have hdiv : (X / b) * b ≤ X := Nat.div_mul_le_self X b
        have hdivR : ((X / b : ℕ) : ℝ) * b ≤ X := by
          exact_mod_cast hdiv
        nlinarith
  exact add_le_add
    (mul_le_mul_of_nonneg_right hzero (Nat.cast_nonneg N)) hnonzero

theorem realGeomMajorant_le_length (N : ℕ) (x : ℝ) :
    realGeomMajorant N x ≤ N := by
  unfold realGeomMajorant
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- A `1/(bQ)` rational approximation controls one terminal frequency when
the product multiplier is at most half of `Q`. -/
theorem approximation_error_mul
    (θ : ℝ) (a b Q v : ℕ) (hb : 0 < b)
    (hvpos : 0 < v)
    (hv : 2 * v ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    |θ * v - ((a * v : ℕ) : ℝ) / b| ≤ 1 / (2 * b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hQ : 0 < Q := lt_of_lt_of_le (by omega : 0 < 2 * v) hv
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hvR : (2 : ℝ) * v ≤ Q := by exact_mod_cast hv
  have hid :
      θ * (v : ℝ) - ((a * v : ℕ) : ℝ) / b =
        (v : ℝ) * (θ - (a : ℝ) / b) := by
    push_cast
    field_simp
  rw [hid, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ v)]
  calc
    (v : ℝ) * |θ - (a : ℝ) / b| ≤
        (v : ℝ) * (1 / ((b : ℝ) * Q)) := by gcongr
    _ ≤ 1 / (2 * b) := by
      rw [show (v : ℝ) * (1 / ((b : ℝ) * Q)) =
          (v : ℝ) / ((b : ℝ) * Q) by ring]
      rw [div_le_div_iff₀ (mul_pos hbR hQR)
        (by positivity : (0 : ℝ) < 2 * b)]
      nlinarith

/-- Stability of the geometric majorant under the preceding rational
approximation. -/
theorem realGeomMajorant_le_rationalGeomMajorant
    (θ : ℝ) (a b Q N v : ℕ) (hb : 0 < b)
    (hvpos : 0 < v)
    (hv : 2 * v ≤ Q)
    (happrox : |θ - (a : ℝ) / b| ≤ 1 / ((b : ℝ) * Q)) :
    realGeomMajorant N (θ * v) ≤ rationalGeomMajorant a b N v := by
  by_cases hd0 : rationalResidueDistance a b v = 0
  · rw [rationalGeomMajorant, if_pos hd0]
    exact realGeomMajorant_le_length N (θ * v)
  · rw [rationalGeomMajorant, if_neg hd0]
    let d := rationalResidueDistance a b v
    let x : ℝ := θ * v
    let y : ℝ := ((a * v : ℕ) : ℝ) / b
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have herr : |x - y| ≤ 1 / (2 * b) := by
      exact approximation_error_mul θ a b Q v hb hvpos hv happrox
    have hydist : nearestIntegerDistance y = (d : ℝ) / b := by
      dsimp only [y, d, rationalResidueDistance]
      exact nearestIntegerDistance_nat_div (a * v) b
    have hlip : nearestIntegerDistance y ≤
        |x - y| + nearestIntegerDistance x := by
      calc
        nearestIntegerDistance y ≤
            |y - x| + nearestIntegerDistance x :=
          nearestIntegerDistance_le_add_abs_sub y x
        _ = |x - y| + nearestIntegerDistance x := by
          rw [abs_sub_comm]
    rw [hydist] at hlip
    have herr' : |x - y| ≤ (d : ℝ) / (2 * b) := by
      calc
        |x - y| ≤ 1 / (2 * b) := herr
        _ ≤ (d : ℝ) / (2 * b) := by
          gcongr
          exact_mod_cast hdpos
    have hdist : (d : ℝ) / (2 * b) ≤ nearestIntegerDistance x := by
      have hratio : (d : ℝ) / b = 2 * ((d : ℝ) / (2 * b)) := by
        field_simp
      rw [hratio] at hlip
      nlinarith
    have hdistpos : 0 < nearestIntegerDistance x :=
      lt_of_lt_of_le (div_pos hdR (by positivity)) hdist
    rw [realGeomMajorant, if_neg hdistpos.ne']
    refine (min_le_right _ _).trans ?_
    rw [div_le_div_iff₀ (by positivity :
      0 < 2 * nearestIntegerDistance x) hdR]
    have hm := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * b)).mp hdist
    nlinarith

/-! Rectangular products created by the terminal Weyl tree are now grouped
by their integer product.  The fibre over `n` injects into the `d`-fold
divisor box of `n`, which is where the subpower divisor estimate enters. -/

/-- A nested sum over `d` positive factors from a fixed finite set. -/
noncomputable def recursiveProductSum
    (A : Finset ℕ) (F : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, p => F p
  | d + 1, p => ∑ h ∈ A, recursiveProductSum A F d (p * h)

/-- The nested product sum is the literal sum over ordered `d`-tuples. -/
theorem recursiveProductSum_eq_tupleSum
    (A : Finset ℕ) (F : ℕ → ℝ) (d p : ℕ) :
    recursiveProductSum A F d p =
      ∑ a ∈ Erdos444.orderedTuples A d,
        F (p * Erdos444.tupleProduct a) := by
  induction d generalizing p with
  | zero =>
      simp [recursiveProductSum, Erdos444.orderedTuples,
        Erdos444.tupleProduct]
  | succ d ih =>
      simp only [recursiveProductSum, ih]
      rw [← Finset.sum_product A (Erdos444.orderedTuples A d)
        (fun x => F (p * x.1 * Erdos444.tupleProduct x.2))]
      apply Finset.sum_bij (fun x _ => Fin.cons x.1 x.2)
      · intro x hx
        rw [Erdos444.mem_orderedTuples_iff]
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact (Finset.mem_product.mp hx).1
        · exact Erdos444.mem_orderedTuples_iff.mp
            (Finset.mem_product.mp hx).2 j
      · intro x₁ hx₁ x₂ hx₂ heq
        apply Prod.ext
        · exact congrFun heq 0
        · funext i
          exact congrFun heq i.succ
      · intro a ha
        refine ⟨(a 0, Fin.tail a), ?_, ?_⟩
        · rw [Finset.mem_product]
          constructor
          · exact Erdos444.mem_orderedTuples_iff.mp ha 0
          · rw [Erdos444.mem_orderedTuples_iff]
            intro i
            exact Erdos444.mem_orderedTuples_iff.mp ha i.succ
        · exact Fin.cons_self_tail a
      · intro x hx
        simp [Erdos444.tupleProduct, Fin.prod_univ_succ, mul_assoc]

/-- Grouping ordered products by their value costs at most the `d`th power
of the divisor count. -/
theorem tupleSum_le_divisorWeightedSum
    (N d K : ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∑ a ∈ Erdos444.orderedTuples (Finset.Icc 1 N) d,
        F (K * Erdos444.tupleProduct a)) ≤
      ∑ n ∈ Finset.Icc 1 (N ^ d),
        ((n.divisors.card : ℕ) : ℝ) ^ d * F (K * n) := by
  classical
  let A := Finset.Icc 1 N
  let S := Erdos444.orderedTuples A d
  have hmaps : ∀ a ∈ S,
      Erdos444.tupleProduct a ∈ Finset.Icc 1 (N ^ d) := by
    intro a ha
    exact Finset.mem_Icc.mpr ⟨
      Erdos444.tupleProduct_pos ha
        (fun m hm => (Finset.mem_Icc.mp hm).1),
      Erdos444.tupleProduct_le_pow ha
        (fun m hm => (Finset.mem_Icc.mp hm).2)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun a => F (K * Erdos444.tupleProduct a))]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hcard :
      (S.filter fun a => Erdos444.tupleProduct a = n).card ≤
        n.divisors.card ^ d := by
    calc
      (S.filter fun a => Erdos444.tupleProduct a = n).card ≤
          Erdos444.representationCount A d n := by
        apply Finset.card_le_card
        intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨ha.1, ha.2.symm ▸ dvd_rfl⟩
      _ ≤ Erdos444.divisorCount (Set.univ : Set ℕ) n ^ d :=
        Erdos444.representationCount_le_divisorCount_pow
          (fun m hm => Set.mem_univ m) hn0
      _ ≤ n.divisors.card ^ d := by
        exact Nat.pow_le_pow_left
          (Erdos444.divisorCount_le_card_divisors Set.univ n) d
  calc
    (∑ a ∈ S with Erdos444.tupleProduct a = n,
        F (K * Erdos444.tupleProduct a)) =
        ((S.filter fun a => Erdos444.tupleProduct a = n).card : ℕ) *
          F (K * n) := by
      rw [Finset.sum_filter]
      calc
        (∑ a ∈ S, if Erdos444.tupleProduct a = n then
            F (K * Erdos444.tupleProduct a) else 0) =
            ∑ a ∈ S, if Erdos444.tupleProduct a = n then
              F (K * n) else 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          split_ifs with h
          · rw [h]
          · rfl
        _ = ((S.filter fun a => Erdos444.tupleProduct a = n).card : ℕ) *
            F (K * n) := by
          rw [← Finset.sum_filter]
          simp
    _ ≤ ((n.divisors.card : ℕ) : ℝ) ^ d * F (K * n) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hF (K * n))

/-- The exponent in the explicit divisor estimate tends to zero. -/
theorem divisorExponent_tendsto :
    Tendsto (fun n : ℕ =>
      2 * Real.log 2 / Real.log (Real.log n)) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))

theorem eventual_divisor_exponent_le (d : ℕ) (hd : 0 < d) :
    ∃ M : ℕ, ∀ n ≥ M,
      2 * Real.log 2 / Real.log (Real.log n) ≤
        1 / (8 * (d : ℝ) ^ 2) := by
  have hev : ∀ᶠ n : ℕ in atTop,
      2 * Real.log 2 / Real.log (Real.log n) <
        1 / (8 * (d : ℝ) ^ 2) :=
    divisorExponent_tendsto.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 / (8 * (d : ℝ) ^ 2) by
        positivity))
  obtain ⟨M, hM⟩ := eventually_atTop.1 hev
  exact ⟨M, fun n hn => (hM n hn).le⟩

/-- The fixed `N^(1/8)` envelope used to absorb product multiplicities. -/
noncomputable def divisorSubpowerEnvelope (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 / 8 : ℝ)

theorem divisor_power_le_subpower_of_exponent
    (d n N : ℕ) (hd : 0 < d) (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hnN : n ≤ N ^ d) (e : ℝ)
    (he : e ≤ 1 / (8 * (d : ℝ) ^ 2))
    (hdiv : (n.divisors.card : ℝ) ≤ (n : ℝ) ^ e) :
    (n.divisors.card : ℝ) ^ d ≤ divisorSubpowerEnvelope N := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (n.divisors.card : ℝ) ^ d ≤ ((n : ℝ) ^ e) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv d
    _ = (n : ℝ) ^ (e * d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    _ ≤ (n : ℝ) ^ (1 / (8 * (d : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le hnR ?_
      calc
        e * (d : ℝ) ≤ (1 / (8 * (d : ℝ) ^ 2)) * d := by gcongr
        _ = 1 / (8 * d) := by
          have hdR : (0 : ℝ) < d := by exact_mod_cast hd
          field_simp
    _ ≤ ((N ^ d : ℕ) : ℝ) ^ (1 / (8 * (d : ℝ))) := by
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnN)
        (by positivity)
    _ = (((N : ℝ) ^ d) ^ (1 / (8 * (d : ℝ))) : ℝ) := by
      rw [Nat.cast_pow]
    _ = (N : ℝ) ^ ((d : ℝ) * (1 / (8 * (d : ℝ)))) := by
      rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
    _ = (N : ℝ) ^ (1 / 8 : ℝ) := by
      congr 1
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      field_simp
    _ = divisorSubpowerEnvelope N := rfl

/-- Uniform subpower bound for every divisor fibre in the product box. -/
theorem exists_uniform_divisor_power_le_subpower (d : ℕ) (hd : 0 < d) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n ∈ Finset.Icc 1 (N ^ d),
      (n.divisors.card : ℝ) ^ d ≤ divisorSubpowerEnvelope N := by
  obtain ⟨M₁, hM₁⟩ := Erdos443.divisor_bound 1 (by norm_num)
  obtain ⟨M₂, hM₂⟩ := eventual_divisor_exponent_le d hd
  let M := max M₁ M₂
  have htend : Tendsto divisorSubpowerEnvelope atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨M₃, hM₃⟩ := eventually_atTop.1
    ((tendsto_atTop.1 htend) ((M : ℝ) ^ d))
  refine ⟨max 1 M₃, ?_⟩
  intro N hN n hn
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N ^ d := (Finset.mem_Icc.mp hn).2
  by_cases hnM : M ≤ n
  · have hdiv := hM₁ n (le_trans (le_max_left M₁ M₂) hnM)
    have hexp := hM₂ n (le_trans (le_max_right M₁ M₂) hnM)
    apply divisor_power_le_subpower_of_exponent d n N hd hn1 hN1 hnN
      (2 * Real.log 2 / Real.log (Real.log n)) hexp
    simpa only [one_add_one_eq_two] using hdiv.le
  · have hnlt : n < M := Nat.lt_of_not_ge hnM
    have hcard : n.divisors.card < M :=
      lt_of_le_of_lt (Nat.card_divisors_le_self n) hnlt
    have hpow : (n.divisors.card : ℝ) ^ d ≤ (M : ℝ) ^ d := by
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcard.le) d
    exact hpow.trans (hM₃ N (le_trans (le_max_right 1 M₃) hN))

theorem norm_geom_sum_le_unitGeomMajorant (N m : ℕ) (r : ℂ)
    (hm : m ≤ N) (hrnorm : ‖r‖ = 1) :
    ‖∑ n ∈ Finset.range m, r ^ n‖ ≤ unitGeomMajorant N r := by
  by_cases hr : r = 1
  · subst r
    simp [unitGeomMajorant]
    exact_mod_cast hm
  · rw [unitGeomMajorant, if_neg hr]
    apply le_min
    · calc
        ‖∑ n ∈ Finset.range m, r ^ n‖ ≤
            ∑ _n ∈ Finset.range m, (1 : ℝ) := by
          refine (norm_sum_le _ _).trans ?_
          apply Finset.sum_le_sum
          intro n hn
          rw [norm_pow, hrnorm, one_pow]
        _ = m := by simp
        _ ≤ N := by exact_mod_cast hm
    · exact norm_geom_sum_le_two_div r hrnorm hr m

/-- Terminal normalized-power phases are controlled by the geometric
majorant at their exact linear coefficient. -/
theorem norm_terminalPowerPhaseSum_le
    (k L T t N m : ℕ) (hk : 2 ≤ k) (hL : 0 < L)
    (hs : List ℕ) (hlen : hs.length = k - 1) (hm : m ≤ N) :
    ‖∑ n ∈ Finset.range m,
      phase (normalizedPower k L T) (-(t : ℤ))
        (iteratedPowerDifference k L hs n)‖ ≤
      unitGeomMajorant N
        (phase (normalizedPower k L T) (-(t : ℤ))
          ((iteratedPolynomialDifference
            (normalizedPowerPolynomial k L) hs).coeff 1)) := by
  let P := iteratedPolynomialDifference (normalizedPowerPolynomial k L) hs
  have hdegree : P.natDegree = 1 :=
    natDegree_iteratedNormalizedPower_eq_one k L hk hL hs hlen
  have hsum :
      (∑ n ∈ Finset.range m,
        phase (normalizedPower k L T) (-(t : ℤ))
          (iteratedPowerDifference k L hs n)) =
      ∑ n ∈ Finset.range m,
        phase (normalizedPower k L T) (-(t : ℤ)) (P.eval n) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [eval_iteratedPolynomialDifference_normalizedPower]
  rw [hsum, sum_phase_linearPolynomial _ _ P hdegree.le, norm_mul,
    norm_phase, one_mul]
  exact norm_geom_sum_le_unitGeomMajorant N m _ hm (norm_phase _ _ _)

/-- Natural form of the history-independent terminal coefficient. -/
def powerTerminalBaseNat (k L : ℕ) : ℕ :=
  (powerDerivative k ^ (k - 2) * L ^ (k - 1) *
    k.descFactorial (k - 1))

/-- The history-independent factor in the terminal linear coefficient. -/
def powerTerminalBase (k L : ℕ) : ℤ := powerTerminalBaseNat k L

/-- The exact terminal linear coefficient attached to a list of shifts. -/
def powerTerminalCoefficient (k L : ℕ) (hs : List ℕ) : ℤ :=
  powerTerminalBase k L *
    (hs.map fun h ↦ ((h + 1 : ℕ) : ℤ)).prod

theorem coeff_one_iteratedNormalizedPower
    (k L : ℕ) (hk : 2 ≤ k) (hL : 0 < L) (hs : List ℕ)
    (hlen : hs.length = k - 1) :
    (iteratedPolynomialDifference
        (normalizedPowerPolynomial k L) hs).coeff 1 =
      powerTerminalCoefficient k L hs := by
  have hdegree :=
    natDegree_iteratedNormalizedPower_eq_one k L hk hL hs hlen
  rw [show (iteratedPolynomialDifference
      (normalizedPowerPolynomial k L) hs).coeff 1 =
      (iteratedPolynomialDifference
        (normalizedPowerPolynomial k L) hs).leadingCoeff by
        rw [Polynomial.leadingCoeff, hdegree]]
  rw [leadingCoeff_iteratedNormalizedPower k L hk hL hs hlen]
  simp only [powerTerminalCoefficient, powerTerminalBase,
    powerTerminalBaseNat]
  push_cast
  ring

/-- Cartesian over-majorant for all products of `d` additional positive
shifts.  Invalid histories from the triangular Weyl tree are harmlessly
included, making the arithmetic estimate rectangular. -/
noncomputable def powerTerminalProductMajorant
    (k L T t N : ℕ) (p : ℤ) : ℕ → ℝ
  | 0 => unitGeomMajorant N
      (phase (normalizedPower k L T) (-(t : ℤ))
        (powerTerminalBase k L * p))
  | d + 1 => ∑ h ∈ Finset.range N,
      powerTerminalProductMajorant k L T t N
        (p * (h + 1 : ℕ)) d

theorem powerTerminalProductMajorant_nonneg
    (k L T t N : ℕ) (p : ℤ) (d : ℕ) :
    0 ≤ powerTerminalProductMajorant k L T t N p d := by
  induction d generalizing p with
  | zero => exact unitGeomMajorant_nonneg _ _
  | succ d ih =>
      simp only [powerTerminalProductMajorant]
      exact Finset.sum_nonneg fun h hh ↦ ih _

/-- Reindex positive shifts from `[0,N)` to `[1,N]`. -/
theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (N : ℕ) (f : ℕ → M) :
    (∑ h ∈ Finset.range N, f (h + 1)) = ∑ h ∈ Finset.Icc 1 N, f h := by
  apply Finset.sum_bij (fun h _ => h + 1)
  · intro h hh
    exact Finset.mem_Icc.mpr
      ⟨by omega, by simpa using Finset.mem_range.mp hh⟩
  · intro h₁ hh₁ h₂ hh₂ heq
    omega
  · intro h hh
    have hI := Finset.mem_Icc.mp hh
    refine ⟨h - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro h hh
    rfl

/-- Recursive product sum in the exact `h+1` indexing of Weyl histories. -/
noncomputable def shiftedProductSum
    (N : ℕ) (F : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, p => F p
  | d + 1, p => ∑ h ∈ Finset.range N,
      shiftedProductSum N F d (p * (h + 1))

theorem shiftedProductSum_eq_recursiveProductSum
    (N : ℕ) (F : ℕ → ℝ) (d p : ℕ) :
    shiftedProductSum N F d p =
      recursiveProductSum (Finset.Icc 1 N) F d p := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
      simp only [shiftedProductSum, recursiveProductSum]
      calc
        (∑ h ∈ Finset.range N,
            shiftedProductSum N F d (p * (h + 1))) =
            ∑ h ∈ Finset.range N,
              recursiveProductSum (Finset.Icc 1 N) F d (p * (h + 1)) := by
          apply Finset.sum_congr rfl
          intro h hh
          exact ih _
        _ = ∑ h ∈ Finset.Icc 1 N,
              recursiveProductSum (Finset.Icc 1 N) F d (p * h) := by
          exact sum_range_succ_eq_sum_Icc N
            (fun h => recursiveProductSum (Finset.Icc 1 N) F d (p * h))

/-- The complex terminal product majorant is bounded by its positive
real-frequency version. -/
theorem powerTerminalProductMajorant_le_realProductSum
    (k L T t N p d : ℕ) (hT : 0 < normalizedPower k L T) :
    powerTerminalProductMajorant k L T t N (p : ℤ) d ≤
      shiftedProductSum N
        (fun v => realGeomMajorant N
          ((t : ℝ) * powerTerminalBaseNat k L * v /
            normalizedPower k L T)) d p := by
  induction d generalizing p with
  | zero =>
      simp only [powerTerminalProductMajorant, shiftedProductSum]
      have hreal := unitGeomMajorant_le_realGeomMajorant
        (normalizedPower k L T) t N
          (powerTerminalBase k L * (p : ℤ)) hT
      calc
        unitGeomMajorant N
            (phase (normalizedPower k L T) (-(t : ℤ))
              (powerTerminalBase k L * (p : ℤ))) ≤
            realGeomMajorant N
              (-(t : ℝ) *
                ((powerTerminalBase k L * (p : ℤ) : ℤ) : ℝ) /
                  normalizedPower k L T) := hreal
        _ = realGeomMajorant N
              (-((t : ℝ) * powerTerminalBaseNat k L * p /
                normalizedPower k L T)) := by
          congr 1
          simp only [powerTerminalBase]
          push_cast
          ring
        _ = realGeomMajorant N
              ((t : ℝ) * powerTerminalBaseNat k L * p /
                normalizedPower k L T) :=
          realGeomMajorant_neg _ _
  | succ d ih =>
      simp only [powerTerminalProductMajorant, shiftedProductSum]
      apply Finset.sum_le_sum
      intro h hh
      convert ih (p * (h + 1)) using 1 <;> norm_cast

/-- Dirichlet control of every terminal product in the rectangular box. -/
theorem powerTerminalProductMajorant_le_rationalProductSum
    (k L T t N p d a b Q : ℕ)
    (hT : 0 < normalizedPower k L T) (hb : 0 < b) (hp : 0 < p)
    (hKN : 2 * (p * N ^ d) ≤ Q)
    (happrox :
      |((t : ℝ) * powerTerminalBaseNat k L /
          normalizedPower k L T) - (a : ℝ) / b| ≤
        1 / ((b : ℝ) * Q)) :
    powerTerminalProductMajorant k L T t N (p : ℤ) d ≤
      recursiveProductSum (Finset.Icc 1 N)
        (fun v => rationalGeomMajorant a b N v) d p := by
  refine (powerTerminalProductMajorant_le_realProductSum
    k L T t N p d hT).trans ?_
  rw [shiftedProductSum_eq_recursiveProductSum,
    recursiveProductSum_eq_tupleSum,
    recursiveProductSum_eq_tupleSum]
  apply Finset.sum_le_sum
  intro u hu
  let v := p * Erdos444.tupleProduct u
  have hvpos : 0 < v := by
    exact Nat.mul_pos hp (Erdos444.tupleProduct_pos hu
      (fun m hm => (Finset.mem_Icc.mp hm).1))
  have hv : 2 * v ≤ Q := by
    have hprod := Erdos444.tupleProduct_le_pow hu
      (fun m hm => (Finset.mem_Icc.mp hm).2)
    dsimp only [v]
    exact hKN.trans' (by gcongr)
  have hpoint := realGeomMajorant_le_rationalGeomMajorant
    ((t : ℝ) * powerTerminalBaseNat k L /
      normalizedPower k L T) a b Q N v hb hvpos hv happrox
  simpa only [v, Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_comm,
    mul_left_comm] using hpoint

/-- A divisor bound uniform up to `N^d` turns the tuple sum into one
rational harmonic sum. -/
theorem recursiveRationalProductSum_le
    (a b N d : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hdiv : ∀ n ∈ Finset.Icc 1 (N ^ d),
      ((n.divisors.card : ℕ) : ℝ) ^ d ≤ D) :
    recursiveProductSum (Finset.Icc 1 N)
        (fun v => rationalGeomMajorant a b N v) d 1 ≤
      D * ∑ n ∈ Finset.Icc 1 (N ^ d),
        rationalGeomMajorant a b N n := by
  rw [recursiveProductSum_eq_tupleSum]
  refine (tupleSum_le_divisorWeightedSum N d 1
    (fun v => rationalGeomMajorant a b N v)
    (rationalGeomMajorant_nonneg a b N)).trans ?_
  simp only [one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  exact mul_le_mul_of_nonneg_right (hdiv n hn)
    (rationalGeomMajorant_nonneg a b N n)

/-- Explicit terminal aggregate estimate under a reduced rational
approximation and a uniform divisor-fibre bound. -/
theorem powerTerminalProductMajorant_le_explicit
    (k L T t N d a b Q : ℕ) (D : ℝ)
    (hT : 0 < normalizedPower k L T) (hb : 0 < b)
    (ha : a.Coprime b) (hQ : 2 * N ^ d ≤ Q)
    (happrox :
      |((t : ℝ) * powerTerminalBaseNat k L /
          normalizedPower k L T) - (a : ℝ) / b| ≤
        1 / ((b : ℝ) * Q))
    (hD : 0 ≤ D)
    (hdiv : ∀ n ∈ Finset.Icc 1 (N ^ d),
      ((n.divisors.card : ℕ) : ℝ) ^ d ≤ D) :
    powerTerminalProductMajorant k L T t N 1 d ≤
      D * (((N ^ d : ℕ) : ℝ) / b + 1) * N +
        D * (2 * (((N ^ d : ℕ) : ℝ) + b) * (1 + Real.log b)) := by
  refine (powerTerminalProductMajorant_le_rationalProductSum
    k L T t N 1 d a b Q hT hb (by omega) (by simpa using hQ)
      happrox).trans ?_
  refine (recursiveRationalProductSum_le a b N d D hD hdiv).trans ?_
  have hrat := sum_rationalGeomMajorant_le a b N (N ^ d) hb ha
  calc
    D * ∑ n ∈ Finset.Icc 1 (N ^ d),
        rationalGeomMajorant a b N n ≤
        D * ((((N ^ d : ℕ) : ℝ) / b + 1) * N +
          2 * (((N ^ d : ℕ) : ℝ) + b) * (1 + Real.log b)) :=
      mul_le_mul_of_nonneg_left hrat hD
    _ = D * (((N ^ d : ℕ) : ℝ) / b + 1) * N +
        D * (2 * (((N ^ d : ℕ) : ℝ) + b) *
          (1 + Real.log b)) := by ring

/-- The valid aggregate Weyl tree is bounded by the rectangular product
majorant. -/
theorem powerWeylAggregate_le_productMajorant
    (k L T t N : ℕ) (hk : 2 ≤ k) (hL : 0 < L)
    (hs : List ℕ) (m d : ℕ) (hm : m ≤ N)
    (hlen : hs.length + d = k - 1) :
    powerWeylAggregate k L T t hs m d ≤
      powerTerminalProductMajorant k L T t N
        ((hs.map fun h ↦ ((h + 1 : ℕ) : ℤ)).prod) d := by
  induction d generalizing hs m with
  | zero =>
      have hterminalLength : hs.length = k - 1 := by omega
      have hleaf := norm_terminalPowerPhaseSum_le
        k L T t N m hk hL hs hterminalLength hm
      rw [powerWeylAggregate, powerTerminalProductMajorant]
      simpa only [coeff_one_iteratedNormalizedPower k L hk hL hs
        hterminalLength, powerTerminalCoefficient] using hleaf
  | succ d ih =>
      simp only [powerWeylAggregate, powerTerminalProductMajorant]
      calc
        (∑ h ∈ Finset.range m,
            powerWeylAggregate k L T t (h :: hs) (m - h - 1) d) ≤
            ∑ h ∈ Finset.range m,
              powerTerminalProductMajorant k L T t N
                (((((h + 1 : ℕ) : ℤ)) ::
                  (hs.map fun u ↦ ((u + 1 : ℕ) : ℤ))).prod) d := by
          apply Finset.sum_le_sum
          intro h hh
          apply ih (h :: hs) (m - h - 1) (by omega)
          simp only [List.length_cons]
          omega
        _ = ∑ h ∈ Finset.range m,
              powerTerminalProductMajorant k L T t N
                ((hs.map fun u ↦ ((u + 1 : ℕ) : ℤ)).prod *
                  (h + 1 : ℕ)) d := by
          apply Finset.sum_congr rfl
          intro h hh
          apply congrArg (fun p : ℤ ↦
            powerTerminalProductMajorant k L T t N p d)
          simp only [List.prod_cons]
          push_cast
          ring
        _ ≤ ∑ h ∈ Finset.range N,
              powerTerminalProductMajorant k L T t N
                ((hs.map fun u ↦ ((u + 1 : ℕ) : ℤ)).prod *
                  (h + 1 : ℕ)) d := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_mono hm
          · intro h hh hnot
            exact powerTerminalProductMajorant_nonneg _ _ _ _ _ _ d

/-- A finite additive character is Lipschitz in its integer argument, with
the literal constant coming from the exponential convention in `phase`. -/
theorem norm_phase_sub_phase_le (T t a b : ℕ) (hT : 0 < T) (hab : a ≤ b) :
    ‖phase T (-(t : ℤ)) (a : ℤ) - phase T (-(t : ℤ)) (b : ℤ)‖ ≤
      2 * Real.pi * (t : ℝ) * ((b - a : ℕ) : ℝ) / (T : ℝ) := by
  have hb : (b : ℤ) = (a : ℤ) + ((b - a : ℕ) : ℤ) := by
    omega
  have hphaseAdd : phase T (-(t : ℤ)) (b : ℤ) =
      phase T (-(t : ℤ)) (a : ℤ) *
        phase T (-(t : ℤ)) ((b - a : ℕ) : ℤ) := by
    rw [hb, phase_add_right]
  rw [hphaseAdd]
  rw [show phase T (-(t : ℤ)) (a : ℤ) -
      phase T (-(t : ℤ)) (a : ℤ) *
        phase T (-(t : ℤ)) ((b - a : ℕ) : ℤ) =
      phase T (-(t : ℤ)) (a : ℤ) *
        (1 - phase T (-(t : ℤ)) ((b - a : ℕ) : ℤ)) by ring]
  rw [norm_mul, norm_phase, one_mul]
  have hphase :
      phase T (-(t : ℤ)) ((b - a : ℕ) : ℤ) =
        Complex.exp (Complex.I *
          ((-(2 * Real.pi * (t : ℝ) * ((b - a : ℕ) : ℝ) / T) : ℝ) : ℂ)) := by
    unfold phase
    congr 1
    push_cast
    field_simp
  rw [hphase]
  rw [norm_sub_rev]
  calc
    ‖Complex.exp (Complex.I *
          ((-(2 * Real.pi * (t : ℝ) * ((b - a : ℕ) : ℝ) / T) : ℝ) : ℂ)) - 1‖ ≤
        ‖-(2 * Real.pi * (t : ℝ) * ((b - a : ℕ) : ℝ) / T)‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * (t : ℝ) * ((b - a : ℕ) : ℝ) / (T : ℝ) := by
      have hnon : 0 ≤
          2 * Real.pi * (t : ℝ) * ((b - a : ℕ) : ℝ) / (T : ℝ) := by
        positivity
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hnon]

/-- The consecutive value intervals of the normalized polynomial partition
the full interval below its endpoint. -/
theorem sum_valueIntervals (k L N : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.range N,
        ∑ s ∈ Finset.Ico (normalizedPower k L n)
          (normalizedPower k L (n + 1)), f s) =
      ∑ s ∈ Finset.range (normalizedPower k L N), f s := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.range_eq_Ico]
      rw [Finset.sum_Ico_consecutive]
      · rw [Nat.Ico_zero_eq_range]
      · exact Nat.zero_le _
      · exact (normalizedPower_strictMono k L (Nat.lt_succ_self N)).le

/-- A nonzero frequency has zero complete sum when the character is summed in
its argument rather than in its frequency. -/
theorem sum_phase_range_eq_zero (T t : ℕ) (hT : 0 < T) (ht : t < T)
    (ht0 : t ≠ 0) :
    (∑ s ∈ Finset.range T, phase T (-(t : ℤ)) (s : ℤ)) = 0 := by
  letI : NeZero T := ⟨hT.ne'⟩
  have htcast : (t : ZMod T) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact ht0 (Nat.eq_zero_of_dvd_of_lt hdvd ht)
  have hswap :
      (∑ s ∈ Finset.range T, phase T (-(t : ℤ)) (s : ℤ)) =
        ∑ s ∈ Finset.range T, phase T (s : ℤ) (-(t : ℤ)) := by
    apply Finset.sum_congr rfl
    intro s hs
    unfold phase
    congr 1
    ring
  rw [hswap, phase_orthogonality]
  simp [htcast]

/-- The real length of one value gap is the cardinality of its integer
interval; consequently a gap-weighted left endpoint is a constant sum over
that interval. -/
theorem gap_mul_phase_eq_sum_valueInterval (k L n t T : ℕ) :
    (normalizedPowerGap k L n : ℂ) *
        phase T (-(t : ℤ)) (normalizedPower k L n : ℤ) =
      ∑ s ∈ Finset.Ico (normalizedPower k L n)
        (normalizedPower k L (n + 1)),
          phase T (-(t : ℤ)) (normalizedPower k L n : ℤ) := by
  have hmono : normalizedPower k L n ≤ normalizedPower k L (n + 1) :=
    (normalizedPower_strictMono k L (Nat.lt_succ_self n)).le
  have hgap : normalizedPowerGap k L n =
      ((normalizedPower k L (n + 1) - normalizedPower k L n : ℕ) : ℝ) := by
    unfold normalizedPowerGap
    rw [Nat.cast_sub hmono]
  rw [hgap]
  push_cast
  rw [Finset.sum_const, Nat.card_Ico]
  simp

/-- The numerator of the Fourier transform of the canonical gap measure. -/
noncomputable def gapPhaseSum (k L N t : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    (normalizedPowerGap k L n : ℂ) *
      phase (normalizedPower k L N) (-(t : ℤ))
        (normalizedPower k L n : ℤ)

/-- One-dimensional finite summation by parts, retaining the terminal
boundary term. -/
theorem sum_range_mul_eq_boundary_add_differences
    (w f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, w n * f n) =
      w N * (∑ n ∈ Finset.range N, f n) +
        ∑ n ∈ Finset.range N,
          (w n - w (n + 1)) *
            (∑ j ∈ Finset.range (n + 1), f j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have hsum : (∑ n ∈ Finset.range (N + 1), f n) =
          (∑ n ∈ Finset.range N, f n) + f N := by
        rw [Finset.sum_range_succ]
      rw [hsum]
      ring

/-- Exact Abel expansion of the gap-weighted power phase sum. -/
theorem gapPhaseSum_eq_abel (k L N t : ℕ) :
    gapPhaseSum k L N t =
      (normalizedPowerGap k L N : ℂ) *
        (∑ n ∈ Finset.range N,
          phase (normalizedPower k L N) (-(t : ℤ))
            (normalizedPower k L n : ℤ)) +
      ∑ n ∈ Finset.range N,
        ((normalizedPowerGap k L n : ℂ) -
          (normalizedPowerGap k L (n + 1) : ℂ)) *
          (∑ j ∈ Finset.range (n + 1),
            phase (normalizedPower k L N) (-(t : ℤ))
              (normalizedPower k L j : ℤ)) := by
  unfold gapPhaseSum
  exact sum_range_mul_eq_boundary_add_differences _ _ N

/-- The forward variation of the nondecreasing gap sequence telescopes. -/
theorem sum_normalizedPowerGap_differences (k L N : ℕ) :
    (∑ n ∈ Finset.range N,
      (normalizedPowerGap k L (n + 1) - normalizedPowerGap k L n)) =
        normalizedPowerGap k L N - normalizedPowerGap k L 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The complex norm of an Abel coefficient is its nonnegative forward gap
difference. -/
theorem norm_normalizedPowerGap_cast_sub (k L n : ℕ) :
    ‖((normalizedPowerGap k L n : ℂ) -
      (normalizedPowerGap k L (n + 1) : ℂ))‖ =
        normalizedPowerGap k L (n + 1) - normalizedPowerGap k L n := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr (normalizedPowerGap_mono k L n))]
  ring

/-- Abel summation transfers any common bound for the ordinary polynomial
phase prefixes to the gap-weighted phase sum.  Monotonicity makes the total
variation telescope, so the loss is only twice the final gap. -/
theorem norm_gapPhaseSum_le_two_gap_mul_prefix
    (k L N t : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hprefix : ∀ m ≤ N,
      ‖∑ n ∈ Finset.range m,
        phase (normalizedPower k L N) (-(t : ℤ))
          (normalizedPower k L n : ℤ)‖ ≤ M) :
    ‖gapPhaseSum k L N t‖ ≤
      2 * normalizedPowerGap k L N * M := by
  rw [gapPhaseSum_eq_abel]
  calc
    ‖(normalizedPowerGap k L N : ℂ) *
          (∑ n ∈ Finset.range N,
            phase (normalizedPower k L N) (-(t : ℤ))
              (normalizedPower k L n : ℤ)) +
        ∑ n ∈ Finset.range N,
          ((normalizedPowerGap k L n : ℂ) -
            (normalizedPowerGap k L (n + 1) : ℂ)) *
            (∑ j ∈ Finset.range (n + 1),
              phase (normalizedPower k L N) (-(t : ℤ))
                (normalizedPower k L j : ℤ))‖ ≤
        ‖(normalizedPowerGap k L N : ℂ) *
          (∑ n ∈ Finset.range N,
            phase (normalizedPower k L N) (-(t : ℤ))
              (normalizedPower k L n : ℤ))‖ +
        ‖∑ n ∈ Finset.range N,
          ((normalizedPowerGap k L n : ℂ) -
            (normalizedPowerGap k L (n + 1) : ℂ)) *
            (∑ j ∈ Finset.range (n + 1),
              phase (normalizedPower k L N) (-(t : ℤ))
                (normalizedPower k L j : ℤ))‖ := norm_add_le _ _
    _ ≤ normalizedPowerGap k L N * M +
        ∑ n ∈ Finset.range N,
          (normalizedPowerGap k L (n + 1) -
            normalizedPowerGap k L n) * M := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (normalizedPowerGap_pos k L N)]
        exact mul_le_mul_of_nonneg_left (hprefix N le_rfl)
          (normalizedPowerGap_pos k L N).le
      · refine (norm_sum_le _ _).trans ?_
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, norm_normalizedPowerGap_cast_sub]
        exact mul_le_mul_of_nonneg_left
          (hprefix (n + 1) (Finset.mem_range.mp hn))
          (sub_nonneg.mpr (normalizedPowerGap_mono k L n))
    _ = normalizedPowerGap k L N * M +
        (normalizedPowerGap k L N - normalizedPowerGap k L 0) * M := by
      rw [← Finset.sum_mul, sum_normalizedPowerGap_differences]
    _ ≤ 2 * normalizedPowerGap k L N * M := by
      have hgap0 : 0 ≤ normalizedPowerGap k L 0 :=
        (normalizedPowerGap_pos k L 0).le
      nlinarith

/-- Sum of the squared integer gaps.  This is the exact mesh quantity in the
low-frequency Stieltjes estimate. -/
noncomputable def gapSquareSum (k L N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (((normalizedPower k L (n + 1) - normalizedPower k L n : ℕ) : ℝ) ^ 2)

/-- Low-frequency estimate for the unnormalized gap-weighted phase sum. -/
theorem norm_gapPhaseSum_le (k L N t : ℕ) (hN : 0 < N)
    (ht : t < normalizedPower k L N) (ht0 : t ≠ 0) :
    ‖gapPhaseSum k L N t‖ ≤
      (2 * Real.pi * (t : ℝ) / (normalizedPower k L N : ℝ)) *
        gapSquareSum k L N := by
  let T := normalizedPower k L N
  have hT : 0 < T := by
    dsimp only [T]
    simpa only [normalizedPower_zero] using
      normalizedPower_strictMono k L hN
  have hcomplete :
      (∑ s ∈ Finset.range T, phase T (-(t : ℤ)) (s : ℤ)) = 0 :=
    sum_phase_range_eq_zero T t hT ht ht0
  have hrepr : gapPhaseSum k L N t =
      ∑ n ∈ Finset.range N,
        ∑ s ∈ Finset.Ico (normalizedPower k L n)
          (normalizedPower k L (n + 1)),
            (phase T (-(t : ℤ)) (normalizedPower k L n : ℤ) -
              phase T (-(t : ℤ)) (s : ℤ)) := by
    calc
      gapPhaseSum k L N t =
          ∑ n ∈ Finset.range N,
            ∑ s ∈ Finset.Ico (normalizedPower k L n)
              (normalizedPower k L (n + 1)),
                phase T (-(t : ℤ)) (normalizedPower k L n : ℤ) := by
        unfold gapPhaseSum
        apply Finset.sum_congr rfl
        intro n hn
        simpa only [T] using gap_mul_phase_eq_sum_valueInterval k L n t T
      _ = (∑ n ∈ Finset.range N,
            ∑ s ∈ Finset.Ico (normalizedPower k L n)
              (normalizedPower k L (n + 1)),
                phase T (-(t : ℤ)) (normalizedPower k L n : ℤ)) -
          ∑ s ∈ Finset.range T, phase T (-(t : ℤ)) (s : ℤ) := by
        rw [hcomplete, sub_zero]
      _ = (∑ n ∈ Finset.range N,
            ∑ s ∈ Finset.Ico (normalizedPower k L n)
              (normalizedPower k L (n + 1)),
                phase T (-(t : ℤ)) (normalizedPower k L n : ℤ)) -
          ∑ n ∈ Finset.range N,
            ∑ s ∈ Finset.Ico (normalizedPower k L n)
              (normalizedPower k L (n + 1)),
                phase T (-(t : ℤ)) (s : ℤ) := by
        rw [sum_valueIntervals]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        rw [← Finset.sum_sub_distrib]
  rw [hrepr]
  calc
    ‖∑ n ∈ Finset.range N,
        ∑ s ∈ Finset.Ico (normalizedPower k L n)
          (normalizedPower k L (n + 1)),
            (phase T (-(t : ℤ)) (normalizedPower k L n : ℤ) -
              phase T (-(t : ℤ)) (s : ℤ))‖ ≤
        ∑ n ∈ Finset.range N,
          ∑ s ∈ Finset.Ico (normalizedPower k L n)
            (normalizedPower k L (n + 1)),
              ‖phase T (-(t : ℤ)) (normalizedPower k L n : ℤ) -
                phase T (-(t : ℤ)) (s : ℤ)‖ := by
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro n hn
      exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
        (2 * Real.pi * (t : ℝ) / (T : ℝ)) *
          (((normalizedPower k L (n + 1) - normalizedPower k L n : ℕ) : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      let a := normalizedPower k L n
      let b := normalizedPower k L (n + 1)
      have hab : a ≤ b := by
        dsimp only [a, b]
        exact (normalizedPower_strictMono k L (Nat.lt_succ_self n)).le
      calc
        (∑ s ∈ Finset.Ico a b,
            ‖phase T (-(t : ℤ)) (a : ℤ) - phase T (-(t : ℤ)) (s : ℤ)‖) ≤
            ∑ s ∈ Finset.Ico a b,
              2 * Real.pi * (t : ℝ) * ((s - a : ℕ) : ℝ) / (T : ℝ) := by
          apply Finset.sum_le_sum
          intro s hs
          exact norm_phase_sub_phase_le T t a s hT (Finset.mem_Ico.mp hs).1
        _ ≤ ∑ _s ∈ Finset.Ico a b,
              2 * Real.pi * (t : ℝ) * ((b - a : ℕ) : ℝ) / (T : ℝ) := by
          apply Finset.sum_le_sum
          intro s hs
          have hsa : a ≤ s := (Finset.mem_Ico.mp hs).1
          have hsb : s < b := (Finset.mem_Ico.mp hs).2
          gcongr
        _ = (2 * Real.pi * (t : ℝ) / (T : ℝ)) *
              (((b - a : ℕ) : ℝ) ^ 2) := by
          rw [Finset.sum_const, Nat.card_Ico]
          push_cast
          ring
    _ = (2 * Real.pi * (t : ℝ) / (normalizedPower k L N : ℝ)) *
          gapSquareSum k L N := by
      unfold gapSquareSum
      dsimp only [T]
      rw [Finset.mul_sum]

/-- Exact expansion of the canonical Fourier coefficient as a normalized
gap-weighted phase sum. -/
theorem transform_normalizedPowerWeight_eq (k L N t : ℕ) (hN : 0 < N) :
    transform (normalizedPower k L N)
        (fun s => (normalizedPowerWeight k L N s : ℂ)) (-(t : ℤ)) =
      ((normalizedPower k L N : ℝ)⁻¹ : ℂ) * gapPhaseSum k L N t := by
  have hTpos : 0 < normalizedPower k L N := by
    simpa only [normalizedPower_zero] using
      normalizedPower_strictMono k L hN
  unfold transform normalizedPowerWeight gapPhaseSum
  push_cast
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single (normalizedPower k L n)]
  · simp only [if_pos rfl]
    push_cast
    ring
  · intro s hs hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr
      (normalizedPower_strictMono k L (Finset.mem_range.mp hn)))).elim

/-- The corresponding low-frequency estimate for the normalized Fourier
coefficient. -/
theorem norm_transform_normalizedPowerWeight_le_low (k L N t : ℕ)
    (hN : 0 < N) (ht : t < normalizedPower k L N) (ht0 : t ≠ 0) :
    ‖transform (normalizedPower k L N)
        (fun s => (normalizedPowerWeight k L N s : ℂ)) (-(t : ℤ))‖ ≤
      (normalizedPower k L N : ℝ)⁻¹ *
        ((2 * Real.pi * (t : ℝ) / (normalizedPower k L N : ℝ)) *
          gapSquareSum k L N) := by
  rw [transform_normalizedPowerWeight_eq k L N t hN, norm_mul]
  have hT : 0 < (normalizedPower k L N : ℝ) := by
    exact_mod_cast (show 0 < normalizedPower k L N by
      simpa only [normalizedPower_zero] using
        normalizedPower_strictMono k L hN)
  have hinv : ‖((normalizedPower k L N : ℝ) : ℂ)⁻¹‖ =
      (normalizedPower k L N : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  rw [hinv]
  gcongr
  exact norm_gapPhaseSum_le k L N t hN ht ht0

end PowerDecay

/-! ## Finite Fourier counting

The analytic part of the proof supplies a nonnegative probability weight on
polynomial values.  The following exact identity is the finite counting layer
which turns uniform nonzero Fourier coefficients into a monochromatic pair.
-/

namespace FiniteFourier

open Erdos438.Fourier

/-- The weighted number of ordered pairs from `A` whose sum is sampled by
`ν`.  It is complex-valued here so that the Fourier identity is literal. -/
noncomputable def weightedPairCount (A : Finset ℕ) (ν : ℕ → ℂ) : ℂ :=
  ∑ x ∈ A, ∑ y ∈ A, ν (x + y)

/-- Real-valued version of `weightedPairCount`, used for positivity. -/
noncomputable def weightedPairCountReal (A : Finset ℕ) (ν : ℕ → ℝ) : ℝ :=
  ∑ x ∈ A, ∑ y ∈ A, ν (x + y)

theorem ofReal_weightedPairCountReal (A : Finset ℕ) (ν : ℕ → ℝ) :
    ((weightedPairCountReal A ν : ℝ) : ℂ) =
      weightedPairCount A (fun n => (ν n : ℂ)) := by
  unfold weightedPairCountReal weightedPairCount
  push_cast
  rfl

/-- Exact Fourier expansion of a weighted pair count.  The strict source-sum
bound is the no-wrap hypothesis which turns equality modulo `T` into equality
in `ℕ`. -/
theorem weightedPairCount_eq_fourier (T : ℕ) [NeZero T]
    (A : Finset ℕ) (ν : ℕ → ℂ)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x + y < T) :
    (T : ℂ) * weightedPairCount A ν =
      ∑ t ∈ Finset.range T,
        coefficient T A (t : ℤ) * coefficient T A (t : ℤ) *
          transform T ν (-(t : ℤ)) := by
  classical
  symm
  calc
    (∑ t ∈ Finset.range T,
        coefficient T A (t : ℤ) * coefficient T A (t : ℤ) *
          transform T ν (-(t : ℤ))) =
      ∑ t ∈ Finset.range T, ∑ x ∈ A, ∑ y ∈ A,
        ∑ z ∈ Finset.range T,
          (phase T (t : ℤ) (x : ℤ) * phase T (t : ℤ) (y : ℤ)) *
            (ν z * phase T (-(t : ℤ)) (z : ℤ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp only [coefficient, transform, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.range T) (t := A)]
      simp_rw [Finset.sum_comm (s := Finset.range T) (t := A)]
      rw [Finset.sum_comm (s := A) (t := A)]
    _ = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ Finset.range T,
        ν z * ∑ t ∈ Finset.range T,
          phase T (t : ℤ) (((x : ℤ) + y) - z) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [phase_neg_left, ← phase_neg_right]
      rw [← phase_add_right]
      calc
        phase T (t : ℤ) ((x : ℤ) + y) *
              (ν z * phase T (t : ℤ) (-(z : ℤ))) =
            ν z * (phase T (t : ℤ) ((x : ℤ) + y) *
              phase T (t : ℤ) (-(z : ℤ))) := by ring
        _ = ν z * phase T (t : ℤ) (((x : ℤ) + y) - z) := by
          rw [← phase_add_right]
          congr 2
    _ = ∑ x ∈ A, ∑ y ∈ A, ∑ z ∈ Finset.range T,
        ν z * (if x + y = z then (T : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z hz
      rw [phase_orthogonality]
      have hcond :
          (((((x : ℤ) + y) - z : ℤ) : ZMod T) = 0) ↔ x + y = z := by
        push_cast
        rw [sub_eq_zero, ← Nat.cast_add, ZMod.natCast_eq_natCast_iff]
        constructor
        · intro hmod
          exact hmod.eq_of_lt_of_lt (hA x hx y hy)
            (Finset.mem_range.mp hz)
        · rintro rfl
          rfl
      simp only [hcond]
    _ = ∑ x ∈ A, ∑ y ∈ A, (T : ℂ) * ν (x + y) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.sum_eq_single (x + y)]
      · simp
        ring
      · intro z hz hne
        simp [hne.symm]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (hA x hx y hy))).elim
    _ = (T : ℂ) * weightedPairCount A ν := by
      rw [weightedPairCount, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]

/-- If the target weight has total mass one and all its nonzero Fourier
coefficients are at most `η`, then its weighted pair count differs from the
uniform main term by at most `η * T * |A|`. -/
theorem weightedPairCount_deviation_le (T : ℕ) [NeZero T]
    (A : Finset ℕ) (ν : ℕ → ℂ) (η : ℝ)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x + y < T)
    (hmass : ∑ z ∈ Finset.range T, ν z = 1)
    (hη : 0 ≤ η)
    (hfourier : ∀ t ∈ Finset.range T, t ≠ 0 →
      ‖transform T ν (-(t : ℤ))‖ ≤ η) :
    ‖(T : ℂ) * weightedPairCount A ν - (A.card : ℂ) ^ 2‖ ≤
      η * T * A.card := by
  classical
  let U := (Finset.range T).erase 0
  let F : ℕ → ℂ := fun t =>
    coefficient T A (t : ℤ) * coefficient T A (t : ℤ) *
      transform T ν (-(t : ℤ))
  have hTpos : 0 < T := Nat.pos_of_ne_zero (NeZero.ne T)
  have hzero : 0 ∈ Finset.range T := Finset.mem_range.mpr hTpos
  have hFzero : F 0 = (A.card : ℂ) ^ 2 := by
    simp only [F, Int.ofNat_zero, neg_zero, coefficient_zero]
    have htransform : transform T ν 0 = 1 := by
      simpa [transform] using hmass
    rw [htransform]
    ring
  have hidentity :
      (T : ℂ) * weightedPairCount A ν - (A.card : ℂ) ^ 2 =
        ∑ t ∈ U, F t := by
    rw [weightedPairCount_eq_fourier T A ν hA]
    change (∑ t ∈ Finset.range T, F t) - (A.card : ℂ) ^ 2 = _
    rw [← hFzero, ← Finset.add_sum_erase (Finset.range T) F hzero]
    simp only [U]
    ring
  rw [hidentity]
  calc
    ‖∑ t ∈ U, F t‖ ≤ ∑ t ∈ U, ‖F t‖ := norm_sum_le _ _
    _ ≤ ∑ t ∈ U, ‖coefficient T A (t : ℤ)‖ ^ 2 * η := by
      apply Finset.sum_le_sum
      intro t ht
      have htRange : t ∈ Finset.range T :=
        Finset.mem_of_mem_erase ht
      have htNe : t ≠ 0 := (Finset.mem_erase.mp ht).1
      rw [show ‖F t‖ =
          ‖coefficient T A (t : ℤ)‖ ^ 2 *
            ‖transform T ν (-(t : ℤ))‖ by
        simp only [F, norm_mul]
        ring]
      exact mul_le_mul_of_nonneg_left (hfourier t htRange htNe)
        (sq_nonneg _)
    _ ≤ η * ∑ t ∈ Finset.range T,
        ‖coefficient T A (t : ℤ)‖ ^ 2 := by
      rw [Finset.mul_sum]
      calc
        (∑ t ∈ U, ‖coefficient T A (t : ℤ)‖ ^ 2 * η) =
            ∑ t ∈ U, η * ‖coefficient T A (t : ℤ)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          ring
        _ ≤ ∑ t ∈ Finset.range T,
            η * ‖coefficient T A (t : ℤ)‖ ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.erase_subset _ _
          · intro t ht hnot
            positivity
    _ = η * (T * A.card) := by
      rw [parseval_coefficient T A]
      intro x hx
      exact Finset.mem_range.mpr
        (lt_of_le_of_lt (Nat.le_add_right x x) (hA x hx x hx))
    _ = η * T * A.card := by ring

/-- Real lower bound obtained from the complex deviation estimate. -/
theorem weightedPairCountReal_lower (T : ℕ) [NeZero T]
    (A : Finset ℕ) (ν : ℕ → ℝ) (η : ℝ)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x + y < T)
    (hmass : ∑ z ∈ Finset.range T, ν z = 1)
    (hη : 0 ≤ η)
    (hfourier : ∀ t ∈ Finset.range T, t ≠ 0 →
      ‖transform T (fun z => (ν z : ℂ)) (-(t : ℤ))‖ ≤ η) :
    (A.card : ℝ) ^ 2 - η * T * A.card ≤
      T * weightedPairCountReal A ν := by
  have hmassC : ∑ z ∈ Finset.range T, (ν z : ℂ) = 1 := by
    exact_mod_cast hmass
  have hdev := weightedPairCount_deviation_le T A
    (fun z => (ν z : ℂ)) η hA hmassC hη hfourier
  have hdevR :
      |(T : ℝ) * weightedPairCountReal A ν - (A.card : ℝ) ^ 2| ≤
        η * T * A.card := by
    simpa only [← ofReal_weightedPairCountReal, ← Complex.ofReal_natCast,
      ← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using hdev
  linarith [neg_abs_le
    ((T : ℝ) * weightedPairCountReal A ν - (A.card : ℝ) ^ 2)]

/-- A sufficiently large Fourier main term cannot be supported only on the
diagonal.  Consequently there is a distinct pair on which `ν` is positive. -/
theorem exists_offDiagonal_of_fourier_uniform (T : ℕ) [NeZero T]
    (A : Finset ℕ) (ν : ℕ → ℝ) (η : ℝ)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x + y < T)
    (hν : ∀ z ∈ Finset.range T, 0 ≤ ν z)
    (hmass : ∑ z ∈ Finset.range T, ν z = 1)
    (hη : 0 ≤ η)
    (hfourier : ∀ t ∈ Finset.range T, t ≠ 0 →
      ‖transform T (fun z => (ν z : ℂ)) (-(t : ℤ))‖ ≤ η)
    (hlarge : (T : ℝ) + η * T * A.card < (A.card : ℝ) ^ 2) :
    ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ 0 < ν (x + y) := by
  have hlower := weightedPairCountReal_lower T A ν η hA hmass hη hfourier
  have hcount : 1 < weightedPairCountReal A ν := by
    have hTpos : (0 : ℝ) < T := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
    have hscaled : (T : ℝ) < T * weightedPairCountReal A ν := by
      linarith
    nlinarith
  by_contra! hnone
  have hoffzero : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ν (x + y) = 0 := by
    intro x hx y hy hxy
    have hnonneg : 0 ≤ ν (x + y) :=
      hν (x + y) (Finset.mem_range.mpr (hA x hx y hy))
    exact le_antisymm (hnone x hx y hy hxy) hnonneg
  have hdiagEq : weightedPairCountReal A ν = ∑ x ∈ A, ν (x + x) := by
    unfold weightedPairCountReal
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_eq_single x]
    · intro y hy hyx
      exact hoffzero x hx y hy hyx.symm
    · intro h
      exact (h hx).elim
  have hdiagSubset : A.image (fun x => x + x) ⊆ Finset.range T := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_range.mpr (hA x hx x hx)
  have hdiag : (∑ x ∈ A, ν (x + x)) ≤ 1 := by
    calc
      (∑ x ∈ A, ν (x + x)) =
          ∑ z ∈ A.image (fun x => x + x), ν z := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        simp only at hxy ⊢
        omega
      _ ≤ ∑ z ∈ Finset.range T, ν z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hdiagSubset
        intro z hz hnot
        exact hν z hz
      _ = 1 := hmass
  rw [hdiagEq] at hcount
  exact (not_lt_of_ge hdiag) hcount

end FiniteFourier

/-! ## Abstract polynomial-value model and the colouring bridge -/

/-- The usable output of the `W`-tricked exponential-sum argument for the
`k`th powers at modulus `T`.  Its support equation is already in the exact
integer form needed after lifting; no congruence remains in this interface. -/
structure PowerFourierModel (k T : ℕ) (η : ℝ) where
  step : ℕ
  step_pos : 0 < step
  offset : ℕ
  weight : ℕ → ℝ
  weight_nonneg : ∀ s ∈ Finset.range T, 0 ≤ weight s
  weight_mass : ∑ s ∈ Finset.range T, weight s = 1
  fourier_uniform : ∀ t ∈ Finset.range T, t ≠ 0 →
    ‖Erdos438.Fourier.transform T (fun s => (weight s : ℂ)) (-(t : ℤ))‖ ≤ η
  support_power : ∀ s ∈ Finset.range T, 0 < weight s →
    ∃ z : ℕ, step * s + 2 * offset = z ^ k

/-- The remaining analytic assertion, stated directly for the canonical
gap-weighted `W`-tricked power measure.  Besides Fourier decay it records that
the modulus can be made arbitrarily large, which is needed to dominate the
diagonal in the colouring count. -/
def HasNormalizedPowerFourierDecay (k : ℕ) : Prop :=
  ∀ (ε : ℝ), 0 < ε → ∀ B : ℕ,
    ∃ L N : ℕ, 0 < L ∧ 0 < N ∧ B < normalizedPower k L N ∧
      ∀ t ∈ Finset.range (normalizedPower k L N), t ≠ 0 →
        ‖Erdos438.Fourier.transform (normalizedPower k L N)
          (fun s => (normalizedPowerWeight k L N s : ℂ)) (-(t : ℤ))‖ ≤ ε

@[simp] theorem normalizedPower_one (L n : ℕ) :
    normalizedPower 1 L n = n := by
  simp [normalizedPower]

@[simp] theorem normalizedPowerGap_one (L n : ℕ) :
    normalizedPowerGap 1 L n = 1 := by
  simp [normalizedPowerGap]

theorem normalizedPowerWeight_one_of_lt (L N s : ℕ) (hs : s < N) :
    normalizedPowerWeight 1 L N s = (N : ℝ)⁻¹ := by
  unfold normalizedPowerWeight
  simp only [normalizedPower_one, normalizedPowerGap_one]
  rw [Finset.sum_eq_single s]
  · simp
  · intro n hn hne
    simp [hne]
  · exact fun hnot => (hnot (Finset.mem_range.mpr hs)).elim

/-- Exact character orthogonality proves the Fourier-decay statement in
degree one. -/
theorem hasNormalizedPowerFourierDecay_one :
    HasNormalizedPowerFourierDecay 1 := by
  intro ε hε B
  let N := B + 1
  have hN : 0 < N := by simp [N]
  letI : NeZero N := ⟨hN.ne'⟩
  refine ⟨1, N, Nat.zero_lt_one, hN, ?_, ?_⟩
  · simp [N]
  · intro t ht ht0
    simp only [normalizedPower_one] at ht ⊢
    have htN : t < N := Finset.mem_range.mp ht
    have htcast : (t : ZMod N) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact ht0 (Nat.eq_zero_of_dvd_of_lt hdvd htN)
    have hcast : ((-(t : ℤ) : ℤ) : ZMod N) ≠ 0 := by
      rw [Int.cast_neg, neg_ne_zero]
      exact_mod_cast htcast
    unfold Erdos438.Fourier.transform
    have hsum :
        (∑ s ∈ Finset.range N,
          (normalizedPowerWeight 1 1 N s : ℂ) *
            Erdos438.Fourier.phase N (-(t : ℤ)) (s : ℤ)) =
        ∑ s ∈ Finset.range N,
          (((N : ℝ)⁻¹ : ℝ) : ℂ) *
            Erdos438.Fourier.phase N (-(t : ℤ)) (s : ℤ) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [normalizedPowerWeight_one_of_lt 1 N s (Finset.mem_range.mp hs)]
    rw [hsum]
    rw [← Finset.mul_sum]
    have hswap :
        (∑ i ∈ Finset.range N,
          Erdos438.Fourier.phase N (-(t : ℤ)) (i : ℤ)) =
        ∑ i ∈ Finset.range N,
          Erdos438.Fourier.phase N (i : ℤ) (-(t : ℤ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold Erdos438.Fourier.phase
      congr 1
      ring
    rw [hswap, Erdos438.Fourier.phase_orthogonality]
    simp [htcast, hε.le]

/-- The canonical gap measure, together with its Fourier estimate, is a
`PowerFourierModel`. -/
noncomputable def normalizedPowerFourierModel (k L N : ℕ) (η : ℝ)
    (hk : 1 ≤ k) (hL : 0 < L) (hN : 0 < N)
    (hfourier : ∀ t ∈ Finset.range (normalizedPower k L N), t ≠ 0 →
      ‖Erdos438.Fourier.transform (normalizedPower k L N)
        (fun s => (normalizedPowerWeight k L N s : ℂ)) (-(t : ℤ))‖ ≤ η) :
    PowerFourierModel k (normalizedPower k L N) η where
  step := powerStep k L
  step_pos := by
    simp only [powerStep, powerModulus, powerDerivative]
    positivity
  offset := 2 ^ (k - 1)
  weight := normalizedPowerWeight k L N
  weight_nonneg := fun s _hs => normalizedPowerWeight_nonneg k L N s
  weight_mass := normalizedPowerWeight_mass k L N hN
  fourier_uniform := hfourier
  support_power := by
    intro s hsRange hs
    obtain ⟨n, hn, rfl⟩ := normalizedPowerWeight_support k L N s hs
    refine ⟨powerModulus k L * n + 2, ?_⟩
    have htwo : 2 * 2 ^ (k - 1) = 2 ^ k := by
      calc
        2 * 2 ^ (k - 1) = 2 ^ (k - 1) * 2 := Nat.mul_comm _ _
        _ = 2 ^ ((k - 1) + 1) := (pow_succ 2 (k - 1)).symm
        _ = 2 ^ k := by rw [Nat.sub_add_cancel hk]
    rw [htwo]
    exact powerStep_mul_normalizedPower_add k L n hk

/-- Number of positive `u`'s for which any two have sum below `T`. -/
def interiorLength (T : ℕ) : ℕ := (T - 1) / 2

/-- The interval on which the induced colouring is counted. -/
def interior (T : ℕ) : Finset ℕ := Finset.Icc 1 (interiorLength T)

@[simp] theorem card_interior (T : ℕ) : (interior T).card = interiorLength T := by
  simp [interior, interiorLength]

theorem interior_sum_lt {T u v : ℕ} (hu : u ∈ interior T)
    (hv : v ∈ interior T) : u + v < T := by
  have huData := Finset.mem_Icc.mp hu
  have hvData := Finset.mem_Icc.mp hv
  have hu' := huData.2
  have hv' := hvData.2
  unfold interiorLength at hu' hv'
  omega

/-- Exact finite pigeonhole inequality for a colouring of a finset. -/
theorem exists_colorClass_card {α β : Type*} [Fintype β] [Nonempty β]
    [DecidableEq β] (S : Finset α) (color : α → β) :
    ∃ b : β, S.card ≤ Fintype.card β * (S.filter fun x => color x = b).card := by
  classical
  obtain ⟨b, hbmax⟩ := Finite.exists_max (fun b : β =>
    (S.filter fun x => color x = b).card)
  refine ⟨b, ?_⟩
  have hpartition :
      S.card = ∑ a : β, (S.filter fun x => color x = a).card := by
    symm
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    simp
  rw [hpartition]
  calc
    (∑ a : β, (S.filter fun x => color x = a).card) ≤
        ∑ _a : β, (S.filter fun x => color x = b).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact hbmax a
    _ = Fintype.card β * (S.filter fun x => color x = b).card := by
      simp

/-- A Fourier model whose main term beats both its Fourier error and the
diagonal forces a monochromatic non-diagonal power sum. -/
theorem hasMonochromaticPowerSum_of_model {α : Type*} [Fintype α]
    (color : ℕ → α) (k T : ℕ) [NeZero T] (η : ℝ)
    (model : PowerFourierModel k T η)
    (hη : 0 ≤ η)
    (hsize :
      (Fintype.card α : ℝ) ^ 2 *
          ((T : ℝ) + η * T * interiorLength T) <
        (interiorLength T : ℝ) ^ 2) :
    HasMonochromaticPowerSum color k := by
  classical
  let U := interior T
  let induced : ℕ → α := fun u => color (model.step * u + model.offset)
  letI : Nonempty α := ⟨induced 0⟩
  obtain ⟨a, ha⟩ := exists_colorClass_card U induced
  let A := U.filter fun u => induced u = a
  have hAcard : U.card ≤ Fintype.card α * A.card := by
    simpa [A] using ha
  have hAsub : A ⊆ U := Finset.filter_subset _ _
  have hAupper : A.card ≤ U.card := Finset.card_le_card hAsub
  have hAnoWrap : ∀ x ∈ A, ∀ y ∈ A, x + y < T := by
    intro x hx y hy
    exact interior_sum_lt (hAsub hx) (hAsub hy)
  have hpalette : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hTnonneg : (0 : ℝ) ≤ T := by positivity
  have hηT : 0 ≤ η * (T : ℝ) := mul_nonneg hη hTnonneg
  have hlarge :
      (T : ℝ) + η * T * A.card < (A.card : ℝ) ^ 2 := by
    have hAcardR : (interiorLength T : ℝ) ≤
        (Fintype.card α : ℝ) * A.card := by
      exact_mod_cast (by simpa [U] using hAcard)
    have hAupperR : (A.card : ℝ) ≤ interiorLength T := by
      exact_mod_cast (by simpa [U] using hAupper)
    have hleft :
        (T : ℝ) + η * T * A.card ≤
          (T : ℝ) + η * T * interiorLength T := by
      gcongr
    have hsquare : (interiorLength T : ℝ) ^ 2 ≤
        (Fintype.card α : ℝ) ^ 2 * (A.card : ℝ) ^ 2 := by
      nlinarith [sq_nonneg
        ((Fintype.card α : ℝ) * A.card - interiorLength T)]
    nlinarith [sq_pos_of_pos hpalette]
  obtain ⟨u, huA, v, hvA, huv, hweight⟩ :=
    FiniteFourier.exists_offDiagonal_of_fourier_uniform
      T A model.weight η hAnoWrap model.weight_nonneg model.weight_mass hη
        model.fourier_uniform hlarge
  have huU : u ∈ U := hAsub huA
  have hvU : v ∈ U := hAsub hvA
  have hsumRange : u + v ∈ Finset.range T :=
    Finset.mem_range.mpr (interior_sum_lt huU hvU)
  obtain ⟨z, hz⟩ := model.support_power (u + v) hsumRange hweight
  refine ⟨model.step * u + model.offset,
    model.step * v + model.offset, z, ?_, ?_, ?_, ?_, ?_⟩
  · have huPos : 0 < u := (Finset.mem_Icc.mp huU).1
    have : 0 < model.step * u := Nat.mul_pos model.step_pos huPos
    omega
  · have hvPos : 0 < v := (Finset.mem_Icc.mp hvU).1
    have : 0 < model.step * v := Nat.mul_pos model.step_pos hvPos
    omega
  · intro heq
    have hmul : model.step * u = model.step * v := by omega
    exact huv (Nat.eq_of_mul_eq_mul_left model.step_pos hmul)
  · exact (Finset.mem_filter.mp huA).2.trans
      (Finset.mem_filter.mp hvA).2.symm
  · calc
      (model.step * u + model.offset) +
          (model.step * v + model.offset) =
          model.step * (u + v) + 2 * model.offset := by
        rw [Nat.mul_add, two_mul]
        omega
      _ = z ^ k := hz

/-- The precise analytic existence statement left after the finite Fourier
and colouring arguments have been discharged. -/
def HasPowerFourierModels (k : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m →
    ∃ (T : ℕ) (η : ℝ), 0 < T ∧ 0 ≤ η ∧
      ∃ model : PowerFourierModel k T η,
        (m : ℝ) ^ 2 * ((T : ℝ) + η * T * interiorLength T) <
          (interiorLength T : ℝ) ^ 2

/-- Arbitrarily large Fourier-uniform canonical measures supply the numerical
models required by the colouring argument. -/
theorem hasPowerFourierModels_of_decay {k : ℕ} (hk : 1 ≤ k)
    (hdecay : HasNormalizedPowerFourierDecay k) :
    HasPowerFourierModels k := by
  intro m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let η : ℝ := 1 / (8 * (m : ℝ) ^ 2)
  have hη : 0 < η := by
    dsimp only [η]
    positivity
  obtain ⟨L, N, hL, hN, hlargeT, hfourier⟩ :=
    hdecay η hη (16 * m ^ 2 + 11)
  let T := normalizedPower k L N
  have hTpos : 0 < T :=
    lt_of_le_of_lt (Nat.zero_le (16 * m ^ 2 + 11)) hlargeT
  refine ⟨T, η, hTpos, hη.le,
    normalizedPowerFourierModel k L N η hk hL hN hfourier, ?_⟩
  have hTlarge : 16 * (m : ℝ) ^ 2 + 11 < (T : ℝ) := by
    exact_mod_cast hlargeT
  have hTupperNat : T ≤ 2 * interiorLength T + 2 := by
    unfold interiorLength
    omega
  have hTupper : (T : ℝ) ≤ 2 * (interiorLength T : ℝ) + 2 := by
    exact_mod_cast hTupperNat
  have hcancel : (m : ℝ) ^ 2 * η = 1 / 8 := by
    dsimp only [η]
    field_simp
  rw [show (m : ℝ) ^ 2 *
      ((T : ℝ) + η * T * interiorLength T) =
        (m : ℝ) ^ 2 * T + ((m : ℝ) ^ 2 * η) * T * interiorLength T by
      ring,
    hcancel]
  nlinarith [sq_nonneg
    ((interiorLength T : ℝ) - (8 * (m : ℝ) ^ 2 + 4))]

/-- Reduction of the `k`th-power theorem to the explicit weighted polynomial
Fourier model. -/
theorem powerResolution_of_fourierModels {k : ℕ}
    (hmodels : HasPowerFourierModels k) : PowerResolution k := by
  intro α _ color
  letI := Fintype.ofFinite α
  let : Nonempty α := ⟨color 0⟩
  have hm : 0 < Fintype.card α := Fintype.card_pos
  obtain ⟨T, η, hT, hη, model, hsize⟩ :=
    hmodels (Fintype.card α) hm
  letI : NeZero T := ⟨hT.ne'⟩
  exact hasMonochromaticPowerSum_of_model color k T η model hη hsize

/-- The checked analytic-to-combinatorial bridge in its shortest public form. -/
theorem powerResolution_of_normalizedPowerFourierDecay {k : ℕ} (hk : 1 ≤ k)
    (hdecay : HasNormalizedPowerFourierDecay k) : PowerResolution k :=
  powerResolution_of_fourierModels
    (hasPowerFourierModels_of_decay hk hdecay)

/-- The degree-one instance, where the normalized value measure is exactly
uniform and no Weyl estimate is needed. -/
theorem erdos439_power_one : PowerResolution 1 :=
  powerResolution_of_normalizedPowerFourierDecay (by omega)
    hasNormalizedPowerFourierDecay_one

end Erdos439
