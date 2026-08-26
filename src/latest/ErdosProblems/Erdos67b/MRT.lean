import ErdosProblems.Erdos67b.LogElliott
import Mathlib.NumberTheory.SelbergSieve
import PrimeNumberTheoremAnd.Consequences

/-!
# The modulated short-interval input of Matomäki--Radziwiłł--Tao

This file isolates the one deep short-interval estimate used in Tao's proof of the
logarithmically averaged Elliott theorem.  The estimate itself is recorded below as the
proposition `MRTModulatedShortIntervalInput`; it is a proposition to be proved, not an assumed
declaration.  Everything after its statement is unconditional finite infrastructure used in the
published proof: typical-factorisation sets, the corrected Ramaré identity, and its bilinear and
Dirichlet-polynomial expansions.

The correction in the denominator of Ramaré's identity is important.  If `n = p * m`, then the
number of primes from the selected block dividing `n` is

`1_{p ∤ m} + #{q in the block : q ∣ m}`,

not always `1 + #{q : q ∣ m}`.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

/-! ## The exact finite input used by logarithmic Elliott -/

/-- The additive character `e(α n) = exp(2 π i α n)`. -/
def additivePhase (α : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * α * n * Complex.I)

theorem norm_additivePhase (α : ℝ) (n : ℕ) : ‖additivePhase α n‖ = 1 := by
  rw [additivePhase, Complex.norm_exp]
  simp

/-- A length-`H` modulated sum on the translate beginning at `n+1`. -/
def modulatedShortSum (f : ℕ → ℂ) (n H : ℕ) (α : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 H, f (n + j) * additivePhase α j

/-- The finite logarithmically weighted average appearing in Tao's Proposition 2.4. -/
def logAverageModulatedShortSum
    (f : ℕ → ℂ) (X W H : ℕ) (α : ℝ) : ℝ :=
  ∑ n ∈ elliottLogWindow X W,
    ‖modulatedShortSum f n H α‖ / ((H : ℝ) * n)

theorem logAverageModulatedShortSum_nonneg
    (f : ℕ → ℂ) (X W H : ℕ) (α : ℝ) :
    0 ≤ logAverageModulatedShortSum f X W H α := by
  exact Finset.sum_nonneg fun _ _ ↦ div_nonneg (norm_nonneg _) (by positivity)

/-- The logarithmic average is literally harmonic weight times the normalized short sum. -/
theorem logAverageModulatedShortSum_eq
    {H : ℕ} (hH : 0 < H) (f : ℕ → ℂ) (X W : ℕ) (α : ℝ) :
    logAverageModulatedShortSum f X W H α =
      ∑ n ∈ elliottLogWindow X W,
        harmonicWeight n * (‖modulatedShortSum f n H α‖ / H) := by
  unfold logAverageModulatedShortSum
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (mem_elliottLogWindow.mp hn).1)
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  simp only [harmonicWeight]
  field_simp

theorem norm_modulatedShortSum_le
    {f : ℕ → ℂ} {n H : ℕ} {α : ℝ}
    (hf : ∀ j ∈ Finset.Icc 1 H, ‖f (n + j)‖ ≤ 1) :
    ‖modulatedShortSum f n H α‖ ≤ H := by
  calc
    ‖modulatedShortSum f n H α‖ ≤
        ∑ j ∈ Finset.Icc 1 H, ‖f (n + j) * additivePhase α j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_additivePhase, mul_one]
      exact hf j hj
    _ = H := by simp

/-- The trivial estimate: without cancellation the normalized logarithmic average is at most the
harmonic mass of the Elliott window. -/
theorem logAverageModulatedShortSum_le_mass
    {f : ℕ → ℂ} {X W H : ℕ} {α : ℝ} (hH : 0 < H)
    (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) :
    logAverageModulatedShortSum f X W H α ≤ elliottLogMass X W := by
  rw [logAverageModulatedShortSum_eq hH]
  unfold elliottLogMass
  apply Finset.sum_le_sum
  intro n hn
  have hshort : ‖modulatedShortSum f n H α‖ ≤ H := by
    apply norm_modulatedShortSum_le
    intro j hj
    apply hf
    have hnpos := (mem_elliottLogWindow.mp hn).1
    have hjpos := (Finset.mem_Icc.mp hj).1
    omega
  have hweight := harmonicWeight_nonneg n
  have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    harmonicWeight n * (‖modulatedShortSum f n H α‖ / H) ≤
        harmonicWeight n * 1 := by
      gcongr
      exact (div_le_one hHreal).2 (by exact_mod_cast hshort)
    _ = harmonicWeight n := mul_one _

/-- The non-pretentiousness condition used to invoke the MRT short-interval theorem.

This is deliberately the same finite condition as in `UnitCircleLogElliott`: all character
moduli are at most `A`, all twists satisfy `|t| ≤ A X`, and the squared distance is at least `A`.
-/
def MRTNonpretentious (f : ℕ → ℂ) (A X : ℕ) : Prop :=
  ∀ q : ℕ, 0 < q → q ≤ A →
    ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      |t| ≤ (A : ℝ) * X →
        (A : ℝ) ≤ pretentiousDistSqToTwist f χ t X

/-- Nonpretentiousness at a threshold remains valid at every smaller threshold.  This finite
monotonicity is used in the endpoint-range reduction, where the restricted logarithmic window
may force a smaller auxiliary pretentiousness parameter. -/
theorem MRTNonpretentious.mono
    {f : ℕ → ℂ} {A A' X : ℕ} (hAA' : A' ≤ A)
    (h : MRTNonpretentious f A X) : MRTNonpretentious f A' X := by
  intro q hq hqA' χ t ht
  have ht' : |t| ≤ (A : ℝ) * X := by
    exact ht.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hAA') (Nat.cast_nonneg X))
  have hdist := h q hq (hqA'.trans hAA') χ t ht'
  have hAA'R : (A' : ℝ) ≤ A := by exact_mod_cast hAA'
  exact hAA'R.trans hdist

/-- Exact finite short-interval proposition needed in the unit-circle specialization of the
logarithmically averaged Elliott theorem.

The quantifier order is essential.  Proposition 2.4 of arXiv:1509.05422 first chooses the lower
short-interval scale `Hmin`; its conclusion is uniform on each *fixed finite* interval
`Hmin ≤ H ≤ Hmax`, and only after `Hmax` has been fixed is the pretentiousness threshold
`A₀` chosen.  The condition `W * log X ≤ X` is the finite real-valued form of the restricted
range `W ≤ X / log X` used in the proposition after Tao's endpoint reduction.

In particular, one must not swap `∀ Hmax, ∃ A₀` into one threshold uniform in every
unbounded `H`: that stronger assertion is not what the cited theorem proves.
-/
def MRTModulatedShortIntervalInput : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ Hmin : ℕ, 10 ≤ Hmin ∧
      ∀ Hmax : ℕ, Hmin ≤ Hmax →
        ∃ A₀ : ℕ, Hmax ≤ A₀ ∧
          ∀ A X W H : ℕ,
            A₀ ≤ A → A ≤ W → W ≤ X →
              (W : ℝ) * Real.log X ≤ X →
                Hmin ≤ H → H ≤ Hmax →
                  ∀ f : ℕ → ℂ,
                    IsCompletelyMultiplicativeOnPositive f →
                    (∀ n : ℕ, 0 < n → ‖f n‖ = 1) →
                    MRTNonpretentious f A X →
                    ∀ α : ℝ,
                      logAverageModulatedShortSum f X W H α ≤ ε * Real.log W

/-! ## Typical factorisations -/

/-- A closed interval of primes. -/
def primesInBlock (I : ℕ × ℕ) : Finset ℕ :=
  (Finset.Icc I.1 I.2).filter Nat.Prime

@[simp]
theorem mem_primesInBlock {I : ℕ × ℕ} {p : ℕ} :
    p ∈ primesInBlock I ↔ p.Prime ∧ I.1 ≤ p ∧ p ≤ I.2 := by
  simp only [primesInBlock, Finset.mem_filter, Finset.mem_Icc]
  aesop

/-- `n` has at least one prime factor in the block `I`. -/
def HasPrimeFactorInBlock (I : ℕ × ℕ) (n : ℕ) : Prop :=
  ∃ p ∈ primesInBlock I, p ∣ n

/-- `n` has at least one prime factor in every selected prime block. -/
def HasTypicalFactorization (blocks : Finset (ℕ × ℕ)) (n : ℕ) : Prop :=
  ∀ I ∈ blocks, HasPrimeFactorInBlock I n

/-- The finite set of typical integers in `[1,X]`. -/
noncomputable def typicalFactorizationSet
    (blocks : Finset (ℕ × ℕ)) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter (HasTypicalFactorization blocks)

@[simp]
theorem mem_typicalFactorizationSet {blocks : Finset (ℕ × ℕ)} {X n : ℕ} :
    n ∈ typicalFactorizationSet blocks X ↔
      1 ≤ n ∧ n ≤ X ∧ HasTypicalFactorization blocks n := by
  classical
  simp [typicalFactorizationSet, and_assoc]

theorem hasPrimeFactorInBlock_mul_iff_right
    {I : ℕ × ℕ} {d m : ℕ} (hd : 0 < d)
    (hlarge : ∀ p ∈ primesInBlock I, d < p) :
    HasPrimeFactorInBlock I (d * m) ↔ HasPrimeFactorInBlock I m := by
  constructor
  · rintro ⟨p, hp, hpdvd⟩
    rcases (Nat.Prime.dvd_mul (mem_primesInBlock.mp hp).1).mp hpdvd with hpd | hpm
    · exact False.elim ((Nat.not_le_of_gt (hlarge p hp)) (Nat.le_of_dvd hd hpd))
    · exact ⟨p, hp, hpm⟩
  · rintro ⟨p, hp, hpm⟩
    exact ⟨p, hp, dvd_mul_of_dvd_right hpm d⟩

/-- Multiplication by an integer below every prime block does not change typicality.  This is the
finite content of the support identity used when the convolution variable `d` satisfies
`d < P₁`. -/
theorem hasTypicalFactorization_mul_iff_right
    {blocks : Finset (ℕ × ℕ)} {d m : ℕ} (hd : 0 < d)
    (hlarge : ∀ I ∈ blocks, ∀ p ∈ primesInBlock I, d < p) :
    HasTypicalFactorization blocks (d * m) ↔ HasTypicalFactorization blocks m := by
  constructor <;> intro h I hI
  · exact (hasPrimeFactorInBlock_mul_iff_right hd (hlarge I hI)).mp (h I hI)
  · exact (hasPrimeFactorInBlock_mul_iff_right hd (hlarge I hI)).mpr (h I hI)

/-- Exact finite support identity used in the convolution reduction. -/
theorem mem_typicalFactorizationSet_mul_iff
    {blocks : Finset (ℕ × ℕ)} {X d m : ℕ} (hd : 0 < d)
    (hlarge : ∀ I ∈ blocks, ∀ p ∈ primesInBlock I, d < p) :
    d * m ∈ typicalFactorizationSet blocks X ↔
      m ∈ typicalFactorizationSet blocks (X / d) := by
  classical
  rw [mem_typicalFactorizationSet, mem_typicalFactorizationSet]
  constructor
  · rintro ⟨hdm, hle, htyp⟩
    have hm : 1 ≤ m := by
      by_contra hm
      have : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      simp at hdm
    have hmle : m ≤ X / d := (Nat.le_div_iff_mul_le hd).2 (by
      simpa [mul_comm] using hle)
    exact ⟨hm, hmle, (hasTypicalFactorization_mul_iff_right hd hlarge).mp htyp⟩
  · rintro ⟨hm, hmle, htyp⟩
    have hdm : 1 ≤ d * m := Nat.mul_pos hd hm
    have hle : d * m ≤ X := by
      have := (Nat.le_div_iff_mul_le hd).1 hmle
      simpa [mul_comm] using this
    exact ⟨hdm, hle, (hasTypicalFactorization_mul_iff_right hd hlarge).mpr htyp⟩

/-! ## The corrected Ramaré identity -/

/-- The selected primes that divide `n`. -/
def primeDivisorSet (P : Finset ℕ) (n : ℕ) : Finset ℕ :=
  P.filter fun p ↦ p ∣ n

/-- The number of selected primes dividing `n`, without multiplicity. -/
def primeDivisorCount (P : Finset ℕ) (n : ℕ) : ℕ :=
  (primeDivisorSet P n).card

@[simp]
theorem mem_primeDivisorSet {P : Finset ℕ} {n p : ℕ} :
    p ∈ primeDivisorSet P n ↔ p ∈ P ∧ p ∣ n := by
  simp [primeDivisorSet]

theorem primeDivisorCount_pos {P : Finset ℕ} {n : ℕ}
    (h : ∃ p ∈ P, p ∣ n) : 0 < primeDivisorCount P n := by
  obtain ⟨p, hpP, hpn⟩ := h
  exact Finset.card_pos.mpr ⟨p, mem_primeDivisorSet.mpr ⟨hpP, hpn⟩⟩

/-- The corrected denominator in Ramaré's identity for the factorisation `n = p*m`. -/
def ramareDenominator (P : Finset ℕ) (p m : ℕ) : ℕ :=
  (if p ∣ m then 0 else 1) + primeDivisorCount P m

private theorem primeDivisorSet_mul_eq_of_dvd
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) {p m : ℕ}
    (hpP : p ∈ P) (hpm : p ∣ m) :
    primeDivisorSet P (p * m) = primeDivisorSet P m := by
  ext q
  simp only [mem_primeDivisorSet]
  constructor
  · rintro ⟨hqP, hq⟩
    refine ⟨hqP, ?_⟩
    rcases (Nat.Prime.dvd_mul (hP q hqP)).mp hq with hqp | hqm
    · have hqp' : q = p := by
        have hq2 : 2 ≤ q := (hP q hqP).two_le
        exact (Nat.dvd_prime_two_le (hP p hpP) hq2).mp hqp
      simpa [hqp'] using hpm
    · exact hqm
  · rintro ⟨hqP, hqm⟩
    exact ⟨hqP, dvd_mul_of_dvd_right hqm p⟩

private theorem primeDivisorSet_mul_eq_insert_of_not_dvd
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) {p m : ℕ}
    (hpP : p ∈ P) (hpm : ¬p ∣ m) :
    primeDivisorSet P (p * m) = insert p (primeDivisorSet P m) := by
  ext q
  simp only [mem_primeDivisorSet, Finset.mem_insert]
  constructor
  · rintro ⟨hqP, hq⟩
    rcases (Nat.Prime.dvd_mul (hP q hqP)).mp hq with hqp | hqm
    · left
      have hq2 : 2 ≤ q := (hP q hqP).two_le
      exact (Nat.dvd_prime_two_le (hP p hpP) hq2).mp hqp
    · exact Or.inr ⟨hqP, hqm⟩
  · intro hq
    rcases hq with hq | ⟨hqP, hqm⟩
    · subst q
      exact ⟨hpP, dvd_mul_right _ _⟩
    · exact ⟨hqP, dvd_mul_of_dvd_right hqm p⟩

/-- The corrected denominator really is the number of selected prime divisors of `p*m`. -/
theorem ramareDenominator_eq_primeDivisorCount_mul
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) {p m : ℕ} (hpP : p ∈ P) :
    ramareDenominator P p m = primeDivisorCount P (p * m) := by
  unfold ramareDenominator primeDivisorCount
  by_cases hpm : p ∣ m
  · rw [if_pos hpm, zero_add, primeDivisorSet_mul_eq_of_dvd hP hpP hpm]
  · rw [if_neg hpm,
      primeDivisorSet_mul_eq_insert_of_not_dvd hP hpP hpm,
      Finset.card_insert_of_notMem]
    · omega
    · simpa only [mem_primeDivisorSet, not_and, hpP, true_implies] using hpm

theorem ramareDenominator_eq_primeDivisorCount
    {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) {p n : ℕ}
    (hpP : p ∈ P) (hpn : p ∣ n) :
    ramareDenominator P p (n / p) = primeDivisorCount P n := by
  have h := ramareDenominator_eq_primeDivisorCount_mul hP hpP (m := n / p)
  rwa [Nat.mul_div_cancel' hpn] at h

/-- Ramaré's identity, with the corrected denominator from the 2022 revision of MRT. -/
theorem ramare_identity
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {n : ℕ}
    (hn : ∃ p ∈ P, p ∣ n) :
    (∑ p ∈ primeDivisorSet P n,
      ((ramareDenominator P p (n / p) : ℝ)⁻¹)) = 1 := by
  have hcpos : 0 < primeDivisorCount P n := primeDivisorCount_pos hn
  have hden (p : ℕ) (hp : p ∈ primeDivisorSet P n) :
      ramareDenominator P p (n / p) = primeDivisorCount P n :=
    ramareDenominator_eq_primeDivisorCount hP (mem_primeDivisorSet.mp hp).1
      (mem_primeDivisorSet.mp hp).2
  calc
    (∑ p ∈ primeDivisorSet P n,
        ((ramareDenominator P p (n / p) : ℝ)⁻¹)) =
        ∑ _p ∈ primeDivisorSet P n,
          ((primeDivisorCount P n : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hden p hp]
    _ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul, primeDivisorCount]
      have hc : ((primeDivisorSet P n).card : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcpos)
      exact mul_inv_cancel₀ hc

/-- Ramaré's identity with an arbitrary complex coefficient attached to `n`. -/
theorem ramare_identity_smul
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {n : ℕ}
    (hn : ∃ p ∈ P, p ∣ n) (z : ℂ) :
    (∑ p ∈ primeDivisorSet P n,
      z / (ramareDenominator P p (n / p) : ℂ)) = z := by
  have hcpos : 0 < primeDivisorCount P n := primeDivisorCount_pos hn
  have hden (p : ℕ) (hp : p ∈ primeDivisorSet P n) :
      ramareDenominator P p (n / p) = primeDivisorCount P n :=
    ramareDenominator_eq_primeDivisorCount hP (mem_primeDivisorSet.mp hp).1
      (mem_primeDivisorSet.mp hp).2
  calc
    (∑ p ∈ primeDivisorSet P n,
        z / (ramareDenominator P p (n / p) : ℂ)) =
        ∑ _p ∈ primeDivisorSet P n,
          z / (primeDivisorCount P n : ℂ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hden p hp]
    _ = z := by
      rw [← Finset.sum_div, Finset.sum_const, nsmul_eq_mul, primeDivisorCount]
      have hc : ((primeDivisorSet P n).card : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcpos)
      field_simp [hc]

/-- Finite Ramaré expansion of a sum supported on integers having a selected prime divisor. -/
theorem sum_eq_ramare_expansion
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, ∃ p ∈ P, p ∣ n) (F : ℕ → ℂ) :
    (∑ n ∈ S, F n) =
      ∑ n ∈ S, ∑ p ∈ primeDivisorSet P n,
        F n / (ramareDenominator P p (n / p) : ℂ) := by
  apply Finset.sum_congr rfl
  intro n hn
  exact (ramare_identity_smul hP (hS n hn) (F n)).symm

/-- The same expansion with the prime sum moved outside. -/
theorem sum_eq_ramare_expansion_commuted
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, ∃ p ∈ P, p ∣ n) (F : ℕ → ℂ) :
    (∑ n ∈ S, F n) =
      ∑ p ∈ P, ∑ n ∈ S,
        if hpn : p ∣ n then
          F n / (ramareDenominator P p (n / p) : ℂ)
        else 0 := by
  rw [sum_eq_ramare_expansion hP hS]
  simp only [primeDivisorSet, Finset.sum_filter]
  rw [Finset.sum_comm]
  rfl

/-- Ramaré expansion specialized to a typical-factorisation set and one of its prime blocks. -/
theorem sum_typicalFactorizationSet_eq_ramare
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∈ blocks)
    (X : ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ typicalFactorizationSet blocks X, F n) =
      ∑ p ∈ primesInBlock I,
        ∑ n ∈ typicalFactorizationSet blocks X,
          if hpn : p ∣ n then
            F n / (ramareDenominator (primesInBlock I) p (n / p) : ℂ)
          else 0 := by
  classical
  apply sum_eq_ramare_expansion_commuted
  · intro p hp
    exact (mem_primesInBlock.mp hp).1
  · intro n hn
    have htyp := (mem_typicalFactorizationSet.mp hn).2.2
    exact htyp I hI

/-- Complete multiplicativity converts the commuted Ramaré expansion into a bilinear one. -/
theorem completelyMultiplicative_ramare_bilinear
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, ∃ p ∈ P, p ∣ n)
    (hSpos : ∀ n ∈ S, 0 < n)
    (g w : ℕ → ℂ) (hg : IsCompletelyMultiplicativeOnPositive g) :
    (∑ n ∈ S, w n * g n) =
      ∑ p ∈ P, ∑ n ∈ S,
        if hpn : p ∣ n then
          w n * (g p * g (n / p)) /
            (ramareDenominator P p (n / p) : ℂ)
        else 0 := by
  rw [sum_eq_ramare_expansion_commuted hP hS (fun n ↦ w n * g n)]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hpn
  · have hp0 : 0 < p := (hP p hp).pos
    have hn0 : 0 < n := hSpos n hn
    have hquot : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp0
    rw [← hg.2 p (n / p) hp0 hquot, Nat.mul_div_cancel' hpn]
  · rfl

/-! ## Dirichlet-polynomial form -/

/-- A finite Dirichlet polynomial on an arbitrary finite support. -/
def finiteDirichletPolynomial (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))

/-- Ramaré's identity expands a finite Dirichlet polynomial as a prime--cofactor bilinear sum. -/
theorem finiteDirichletPolynomial_eq_ramare
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ n ∈ S, ∃ p ∈ P, p ∣ n)
    (a : ℕ → ℂ) (t : ℝ) :
    finiteDirichletPolynomial S a t =
      ∑ p ∈ P, ∑ n ∈ S,
        if hpn : p ∣ n then
          (a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) /
            (ramareDenominator P p (n / p) : ℂ)
        else 0 := by
  exact sum_eq_ramare_expansion_commuted hP hS
    (fun n ↦ a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ))))

/-! ## Bridges to the existing sieve and PNT libraries -/

/-- Avoiding every prime in `P` is exactly coprimality with their product. -/
theorem no_prime_dvd_iff_coprime_prod
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∀ p ∈ P, ¬p ∣ n) ↔ Nat.Coprime (P.prod id) n := by
  rw [Nat.coprime_prod_left_iff]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  simpa using (hP p hp).coprime_iff_not_dvd.symm

/-- `BoundingSieve.siftedSum` is the weighted complement of the first typical block whenever its
prime product is the product of that block.  This is the direct interface to Mathlib's Selberg
sieve estimates. -/
theorem boundingSieve_siftedSum_eq_missing_block
    (s : BoundingSieve) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hprod : s.prodPrimes = P.prod id) :
    s.siftedSum =
      ∑ n ∈ s.support,
        if ∀ p ∈ P, ¬p ∣ n then s.weights n else 0 := by
  unfold BoundingSieve.siftedSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [hprod]
  have hiff : (∀ p ∈ P, ¬p ∣ n) ↔ Nat.Coprime (P.prod id) n :=
    no_prime_dvd_iff_coprime_prod hP n
  by_cases hc : Nat.Coprime (P.prod id) n
  · have h : ∀ p ∈ P, ¬p ∣ n := hiff.mpr hc
    rw [if_pos hc, if_pos h]
  · have h : ¬∀ p ∈ P, ¬p ∣ n := fun h ↦ hc (hiff.mp h)
    rw [if_neg hc, if_neg h]

/-- Applying any upper Möbius weight from Mathlib's Selberg-sieve API bounds the weighted set
missing a selected prime block. -/
theorem missing_block_sum_le_selberg_bound
    (s : BoundingSieve) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hprod : s.prodPrimes = P.prod id)
    (muPlus : ℕ → ℝ) (hmu : BoundingSieve.IsUpperMoebius muPlus) :
    (∑ n ∈ s.support,
        if ∀ p ∈ P, ¬p ∣ n then s.weights n else 0) ≤
      s.totalMass * s.mainSum muPlus + s.errSum muPlus := by
  rw [← boundingSieve_siftedSum_eq_missing_block s P hP hprod]
  exact BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius muPlus hmu

/-- The local PNT development identifies the finite prime block cardinality with a difference of
the standard prime-counting function. -/
theorem card_primesInBlock {L U : ℕ} (hLU : L ≤ U) :
    (primesInBlock (L, U)).card =
      Nat.primeCounting U - Nat.primeCounting (L - 1) := by
  have hset : primesInBlock (L, U) = Nat.primesLE U \ Nat.primesLE (L - 1) := by
    ext p
    simp only [mem_primesInBlock, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨hp, hLp, hpU⟩
      exact ⟨⟨hpU, hp⟩, fun h ↦ by
        have hpLm := h.1
        have hpPos := hp.pos
        omega⟩
    · rintro ⟨⟨hpU, hp⟩, hnot⟩
      refine ⟨hp, ?_, hpU⟩
      by_contra hLp
      apply hnot
      exact ⟨by omega, hp⟩
  rw [hset, Finset.card_sdiff_of_subset]
  · simp
  · intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (by omega), hp.2⟩

/-- A named bridge to the already proved prime number theorem in `PrimeNumberTheoremAnd`.
Downstream density estimates may use this theorem without introducing a second prime-counting
normalisation. -/
theorem primeCounting_asymptotic_available :
    Asymptotics.IsEquivalent Filter.atTop
      (fun x : ℝ ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ))
      (fun x ↦ x / Real.log x) :=
  pi_alt'

end

end Erdos67b
