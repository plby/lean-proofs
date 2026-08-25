import ErdosProblems.Erdos67.MRHalaszThreeBandEnergy

/-!
# Finite three-band algebra for Halasz's theorem

The complete Euler product is used only for the prime band which supplies
the nonpretentious `L^∞` saving.  The other two bands are cut off at a
finite height.  This file proves that this operation does not alter any
coefficient below that height.  Thus a compactly supported Mellin window
may be estimated using one genuine Euler factor and two genuinely finite
Dirichlet polynomials, without comparing a complete `LSeries` with one of
its tails.
-/

open scoped BigOperators LSeries.notation
open Finset

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Cut an arithmetic coefficient off after `N`. -/
def prefixTruncate (a : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if n ≤ N then a n else 0

@[simp] theorem prefixTruncate_eq_of_le (a : ℕ → ℂ) {N n : ℕ}
    (hn : n ≤ N) :
    prefixTruncate a N n = a n := by
  simp [prefixTruncate, hn]

@[simp] theorem prefixTruncate_eq_zero_of_lt (a : ℕ → ℂ) {N n : ℕ}
    (hn : N < n) :
    prefixTruncate a N n = 0 := by
  simp [prefixTruncate, Nat.not_le.mpr hn]

theorem norm_prefixTruncate_le_one
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    (N : ℕ) {n : ℕ} (hn : 0 < n) :
    ‖prefixTruncate a N n‖ ≤ 1 := by
  unfold prefixTruncate
  split_ifs
  · exact ha n hn
  · simp

/-- Remove the constant coefficient as well as cutting off after `N`.
This is the finite coefficient used for the two sieve-controlled factors:
removing `n = 1` is essential for their square mass to be small. -/
def positivePrefixTruncate (a : ℕ → ℂ) (N n : ℕ) : ℂ :=
  if 1 < n ∧ n ≤ N then a n else 0

@[simp] theorem positivePrefixTruncate_eq_of_lt_le
    (a : ℕ → ℂ) {N n : ℕ} (hn : 1 < n) (hnN : n ≤ N) :
    positivePrefixTruncate a N n = a n := by
  simp [positivePrefixTruncate, hn, hnN]

@[simp] theorem positivePrefixTruncate_one (a : ℕ → ℂ) (N : ℕ) :
    positivePrefixTruncate a N 1 = 0 := by
  simp [positivePrefixTruncate]

@[simp] theorem positivePrefixTruncate_eq_zero_of_le_one
    (a : ℕ → ℂ) {N n : ℕ} (hn : n ≤ 1) :
    positivePrefixTruncate a N n = 0 := by
  simp [positivePrefixTruncate, Nat.not_lt.mpr hn]

@[simp] theorem positivePrefixTruncate_eq_zero_of_lt
    (a : ℕ → ℂ) {N n : ℕ} (hn : N < n) :
    positivePrefixTruncate a N n = 0 := by
  simp [positivePrefixTruncate, Nat.not_le.mpr hn]

theorem norm_positivePrefixTruncate_le_one
    {a : ℕ → ℂ} (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    (N : ℕ) {n : ℕ} (hn : 0 < n) :
    ‖positivePrefixTruncate a N n‖ ≤ 1 := by
  unfold positivePrefixTruncate
  split_ifs
  · exact ha n hn
  · simp

/-- There is a prime factor of `n` belonging to the predicate `P`.  The
finite-set formulation makes the proposition computably decidable. -/
def HasPrimeFactor (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : Prop :=
  n.primeFactors.filter P ≠ ∅

instance decidableHasPrimeFactor
    (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    Decidable (HasPrimeFactor P n) := by
  unfold HasPrimeFactor
  infer_instance

theorem hasPrimeFactor_iff
    (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    HasPrimeFactor P n ↔ ∃ p ∈ n.primeFactors, P p := by
  change n.primeFactors.filter P ≠ ∅ ↔ _
  rw [← Finset.nonempty_iff_ne_empty]
  exact Finset.filter_nonempty_iff

/-- A canonical prime-band part is nontrivial exactly when that band
actually occurs among the prime factors. -/
theorem one_lt_primeBandPart_iff
    (P : ℕ → Prop) [DecidablePred P] {n : ℕ} (hn : n ≠ 0) :
    1 < primeBandPart P n ↔ HasPrimeFactor P n := by
  constructor
  · intro hpart
    obtain ⟨p, hpprime, hpdiv⟩ :=
      Nat.ne_one_iff_exists_prime_dvd.mp hpart.ne'
    have hpPart : p ∈ (primeBandPart P n).primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨hpprime, hpdiv, primeBandPart_ne_zero P n⟩
    apply (hasPrimeFactor_iff P n).2
    exact ⟨p,
      (prime_mem_primeFactors_primeBandPart_iff P n p).mp hpPart |>.1,
      (prime_mem_primeFactors_primeBandPart_iff P n p).mp hpPart |>.2⟩
  · rw [hasPrimeFactor_iff]
    rintro ⟨p, hpn, hpP⟩
    have hpPart : p ∈ (primeBandPart P n).primeFactors :=
      (prime_mem_primeFactors_primeBandPart_iff P n p).mpr ⟨hpn, hpP⟩
    have hpdiv : p ∣ primeBandPart P n :=
      (Nat.mem_primeFactors.mp hpPart).2.1
    have hp_le : p ≤ primeBandPart P n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (primeBandPart_ne_zero P n)) hpdiv
    exact (Nat.prime_of_mem_primeFactors hpn).one_lt.trans_le hp_le

/-- A prefix truncation has an absolutely convergent `LSeries` at every
complex argument, simply because it has finite support. -/
theorem prefixTruncate_LSeriesSummable
    (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeriesSummable (prefixTruncate a N) s := by
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  have hnN : N < n := by
    simp only [Finset.mem_range, Nat.lt_add_one_iff] at hn
    exact Nat.lt_of_not_ge hn
  by_cases hn0 : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn0,
      prefixTruncate_eq_zero_of_lt a hnN, zero_div]

theorem positivePrefixTruncate_LSeriesSummable
    (a : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    LSeriesSummable (positivePrefixTruncate a N) s := by
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  have hnN : N < n := by
    simp only [Finset.mem_range, Nat.lt_add_one_iff] at hn
    exact Nat.lt_of_not_ge hn
  by_cases hn0 : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn0,
      positivePrefixTruncate_eq_zero_of_lt a hnN, zero_div]

/-- Every coordinate of a positive divisor pair is at most its product. -/
theorem divisorsAntidiagonal_fst_le
    {n : ℕ} (hn : 0 < n) {q : ℕ × ℕ}
    (hq : q ∈ n.divisorsAntidiagonal) :
    q.1 ≤ n := by
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hq).1
  have hq2 : 0 < q.2 := by
    exact Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).2
  rw [← hprod]
  exact Nat.le_mul_of_pos_right q.1 hq2

theorem divisorsAntidiagonal_snd_le
    {n : ℕ} (hn : 0 < n) {q : ℕ × ℕ}
    (hq : q ∈ n.divisorsAntidiagonal) :
    q.2 ≤ n := by
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hq).1
  have hq1 : 0 < q.1 := by
    exact Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).1
  rw [← hprod]
  exact Nat.le_mul_of_pos_left q.2 hq1

/-- Truncating both factors after `N` leaves their convolution unchanged
at every positive coefficient `n ≤ N`. -/
theorem convolution_prefixTruncate_apply_eq
    (a b : ℕ → ℂ) {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    LSeries.convolution (prefixTruncate a N) (prefixTruncate b N) n =
      LSeries.convolution a b n := by
  rw [LSeries.convolution_def, LSeries.convolution_def]
  apply Finset.sum_congr rfl
  intro q hq
  rw [prefixTruncate_eq_of_le a
      ((divisorsAntidiagonal_fst_le hn hq).trans hnN),
    prefixTruncate_eq_of_le b
      ((divisorsAntidiagonal_snd_le hn hq).trans hnN)]

/-- Exact effect of deleting the constant terms from two complementary
prime-band factors.  Below the cutoff their convolution is the original
coefficient precisely when both prime bands occur, and is zero otherwise. -/
theorem convolution_positivePrefixTruncate_primeBands_apply
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P : ℕ → Prop) [DecidablePred P]
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    LSeries.convolution
        (positivePrefixTruncate (primeBandCoefficient f P) N)
        (positivePrefixTruncate
          (primeBandCoefficient f (fun p ↦ ¬ P p)) N) n =
      if HasPrimeFactor P n ∧ HasPrimeFactor (fun p ↦ ¬ P p) n then
        f n else 0 := by
  classical
  rw [LSeries.convolution_def]
  change (∑ q ∈ n.divisorsAntidiagonal,
      positivePrefixTruncate (primeBandCoefficient f P) N q.1 *
        positivePrefixTruncate
          (primeBandCoefficient f (fun p ↦ ¬ P p)) N q.2) = _
  let d := primeBandPart P n
  let e := primeBandPart (fun p ↦ ¬ P p) n
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  have hde : d * e = n := primeBandPart_mul_compl P hne
  have hd : PrimeSupported P d := primeSupported_primeBandPart P n
  have he : PrimeSupported (fun p ↦ ¬ P p) e :=
    primeSupported_primeBandPart (fun p ↦ ¬ P p) n
  have hcop : d.Coprime e :=
    coprime_of_complementary_primeSupported P hd he
  have hmem : (d, e) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨hde, hne⟩
  rw [Finset.sum_eq_single (d, e)]
  · by_cases hboth :
        HasPrimeFactor P n ∧ HasPrimeFactor (fun p ↦ ¬ P p) n
    · have hd1 : 1 < d :=
        (one_lt_primeBandPart_iff P hne).2 hboth.1
      have he1 : 1 < e :=
        (one_lt_primeBandPart_iff (fun p ↦ ¬ P p) hne).2 hboth.2
      have hdN : d ≤ N :=
        (divisorsAntidiagonal_fst_le hn hmem).trans hnN
      have heN : e ≤ N :=
        (divisorsAntidiagonal_snd_le hn hmem).trans hnN
      rw [positivePrefixTruncate_eq_of_lt_le _ hd1 hdN,
        positivePrefixTruncate_eq_of_lt_le _ he1 heN,
        primeBandCoefficient_eq_of_supported f P hd,
        primeBandCoefficient_eq_of_supported f (fun p ↦ ¬ P p) he,
        ← hmul.2 d e (Nat.pos_of_ne_zero hd.1)
          (Nat.pos_of_ne_zero he.1) hcop, hde, if_pos hboth]
    · rw [if_neg hboth]
      by_cases hP : HasPrimeFactor P n
      · have hC : ¬ HasPrimeFactor (fun p ↦ ¬ P p) n := by
          intro h
          exact hboth ⟨hP, h⟩
        have he1 : ¬ 1 < e :=
          (one_lt_primeBandPart_iff (fun p ↦ ¬ P p) hne).not.mpr hC
        simp [positivePrefixTruncate, he1]
      · have hd1 : ¬ 1 < d :=
          (one_lt_primeBandPart_iff P hne).not.mpr hP
        simp [positivePrefixTruncate, hd1]
  · intro q hq hqne
    by_cases hqP : PrimeSupported P q.1
    · by_cases hqC : PrimeSupported (fun p ↦ ¬ P p) q.2
      · have hqmul := (Nat.mem_divisorsAntidiagonal.mp hq).1
        have hu := eq_primeBandParts_of_mul_eq P hqmul hqP hqC
        exact (hqne (Prod.ext hu.1 hu.2)).elim
      · simp [positivePrefixTruncate, primeBandCoefficient, hqC]
    · simp [positivePrefixTruncate, primeBandCoefficient, hqP]
  · intro hnot
    exact (hnot hmem).elim

/-- If two right-hand coefficients agree through `N`, convolution by an
arbitrary left factor preserves that agreement through `N`. -/
theorem convolution_right_congr_up_to
    (a b c : ℕ → ℂ) {N : ℕ}
    (hbc : ∀ n, 0 < n → n ≤ N → b n = c n)
    {n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    LSeries.convolution a b n = LSeries.convolution a c n := by
  rw [LSeries.convolution_def, LSeries.convolution_def]
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply hbc q.2
  · exact Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisorsAntidiagonal hq).2
  · exact (divisorsAntidiagonal_snd_le hn hq).trans hnN

/-- The two complementary bands outside `P₁`, subdivided by `P₂`,
convolve back to the full complementary band. -/
theorem convolution_two_outerBands_apply
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {n : ℕ} (hn : 0 < n) :
    LSeries.convolution
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p))
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) n =
      primeBandCoefficient f (fun p ↦ ¬ P₁ p) n := by
  let g : ℕ → ℂ := primeBandCoefficient f (fun p ↦ ¬ P₁ p)
  have hgMul : IsMultiplicativeOnPositiveNat g :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul (fun p ↦ ¬ P₁ p)
  have hbase :=
    primeBandCoefficient_convolution_compl_of_multiplicative
      hgMul P₂ n hn
  have hnested₂ :
      primeBandCoefficient g P₂ =
        primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p) :=
    primeBandCoefficient_nested f (fun p ↦ ¬ P₁ p) P₂
  have hnested₃ :
      primeBandCoefficient g (fun p ↦ ¬ P₂ p) =
        primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) :=
    primeBandCoefficient_nested f (fun p ↦ ¬ P₁ p) (fun p ↦ ¬ P₂ p)
  rw [hnested₂, hnested₃] at hbase
  exact hbase

/-- Direct coefficient-level three-band identity for an ordinary
multiplicative function. -/
theorem convolution_threeBands_apply
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {n : ℕ} (hn : 0 < n) :
    LSeries.convolution
        (primeBandCoefficient f P₁)
        (LSeries.convolution
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p))
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p))) n =
      f n := by
  let g : ℕ → ℂ := primeBandCoefficient f (fun p ↦ ¬ P₁ p)
  have houter :=
    primeBandCoefficient_convolution_compl_of_multiplicative
      hmul P₁ n hn
  calc
    LSeries.convolution
        (primeBandCoefficient f P₁)
        (LSeries.convolution
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p))
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p))) n =
      LSeries.convolution (primeBandCoefficient f P₁) g n := by
        apply convolution_right_congr_up_to
          (primeBandCoefficient f P₁)
          (LSeries.convolution
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p))
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)))
          g (N := n)
        · intro m hm hmN
          exact convolution_two_outerBands_apply hmul P₁ P₂ hm
        · exact hn
        · exact le_rfl
    _ = f n := houter

/-- Keep the selected first band complete, but truncate the other two.
The resulting coefficient is still exactly `f n` below the truncation
height. -/
theorem convolution_oneFull_twoTruncated_apply
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    LSeries.convolution
        (primeBandCoefficient f P₁)
        (LSeries.convolution
          (prefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
          (prefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N)) n =
      f n := by
  let b := primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)
  let c := primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)
  calc
    LSeries.convolution (primeBandCoefficient f P₁)
        (LSeries.convolution (prefixTruncate b N) (prefixTruncate c N)) n =
      LSeries.convolution (primeBandCoefficient f P₁)
        (LSeries.convolution b c) n := by
          apply convolution_right_congr_up_to
            (primeBandCoefficient f P₁)
            (LSeries.convolution (prefixTruncate b N) (prefixTruncate c N))
            (LSeries.convolution b c) (N := N)
          · intro m hm hmN
            exact convolution_prefixTruncate_apply_eq b c hm hmN
          · exact hn
          · exact hnN
    _ = f n := convolution_threeBands_apply hmul P₁ P₂ hn

/-- The exact finite three-band identity with the constant terms removed
from the two sieve-controlled factors.  It is valid on precisely the
integers which contain a prime from each of those two outer bands. -/
theorem convolution_oneFull_twoPositiveTruncated_apply
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (h₂ : HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ P₂ p) n)
    (h₃ : HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n) :
    LSeries.convolution
        (primeBandCoefficient f P₁)
        (LSeries.convolution
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N)) n =
      f n := by
  classical
  let g : ℕ → ℂ := primeBandCoefficient f (fun p ↦ ¬ P₁ p)
  let r : ℕ → ℂ := fun m ↦
    if HasPrimeFactor P₂ m ∧ HasPrimeFactor (fun p ↦ ¬ P₂ p) m then
      g m else 0
  have hgMul : IsMultiplicativeOnPositiveNat g :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul (fun p ↦ ¬ P₁ p)
  have hnested₂ :
      primeBandCoefficient g P₂ =
        primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p) :=
    primeBandCoefficient_nested f (fun p ↦ ¬ P₁ p) P₂
  have hnested₃ :
      primeBandCoefficient g (fun p ↦ ¬ P₂ p) =
        primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) :=
    primeBandCoefficient_nested f (fun p ↦ ¬ P₁ p) (fun p ↦ ¬ P₂ p)
  have hinner : ∀ m, 0 < m → m ≤ N →
      LSeries.convolution
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N) m =
        r m := by
    intro m hm hmN
    rw [← hnested₂, ← hnested₃]
    exact convolution_positivePrefixTruncate_primeBands_apply
      hgMul P₂ hm hmN
  calc
    LSeries.convolution
        (primeBandCoefficient f P₁)
        (LSeries.convolution
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N)) n =
      LSeries.convolution (primeBandCoefficient f P₁) r n := by
        exact convolution_right_congr_up_to
          (primeBandCoefficient f P₁)
          (LSeries.convolution
            (positivePrefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
            (positivePrefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N))
          r hinner hn hnN
    _ = f n := by
      rw [LSeries.convolution_def]
      change (∑ q ∈ n.divisorsAntidiagonal,
        primeBandCoefficient f P₁ q.1 * r q.2) = f n
      let d := primeBandPart P₁ n
      let e := primeBandPart (fun p ↦ ¬ P₁ p) n
      have hne : n ≠ 0 := Nat.ne_of_gt hn
      have hde : d * e = n := primeBandPart_mul_compl P₁ hne
      have hd : PrimeSupported P₁ d := primeSupported_primeBandPart P₁ n
      have he : PrimeSupported (fun p ↦ ¬ P₁ p) e :=
        primeSupported_primeBandPart (fun p ↦ ¬ P₁ p) n
      have hcop : d.Coprime e :=
        coprime_of_complementary_primeSupported P₁ hd he
      have hmem : (d, e) ∈ n.divisorsAntidiagonal :=
        Nat.mem_divisorsAntidiagonal.mpr ⟨hde, hne⟩
      have hP₂e : HasPrimeFactor P₂ e := by
        rw [hasPrimeFactor_iff] at h₂ ⊢
        rcases h₂ with ⟨p, hpn, hp₁, hp₂⟩
        have hpe : p ∈ e.primeFactors :=
          (prime_mem_primeFactors_primeBandPart_iff
            (fun p ↦ ¬ P₁ p) n p).2 ⟨hpn, hp₁⟩
        exact ⟨p, hpe, hp₂⟩
      have hCP₂e : HasPrimeFactor (fun p ↦ ¬ P₂ p) e := by
        rw [hasPrimeFactor_iff] at h₃ ⊢
        rcases h₃ with ⟨p, hpn, hp₁, hp₂⟩
        have hpe : p ∈ e.primeFactors :=
          (prime_mem_primeFactors_primeBandPart_iff
            (fun p ↦ ¬ P₁ p) n p).2 ⟨hpn, hp₁⟩
        exact ⟨p, hpe, hp₂⟩
      rw [Finset.sum_eq_single (d, e)]
      · simp only [primeBandCoefficient_eq_of_supported f P₁ hd]
        rw [show r e = g e by simp [r, hP₂e, hCP₂e],
          show g e = f e by
            exact primeBandCoefficient_eq_of_supported
              f (fun p ↦ ¬ P₁ p) he,
          ← hmul.2 d e (Nat.pos_of_ne_zero hd.1)
            (Nat.pos_of_ne_zero he.1) hcop, hde]
      · intro q hq hqne
        by_cases hqP : PrimeSupported P₁ q.1
        · by_cases hqC : PrimeSupported (fun p ↦ ¬ P₁ p) q.2
          · have hqmul := (Nat.mem_divisorsAntidiagonal.mp hq).1
            have hu := eq_primeBandParts_of_mul_eq P₁ hqmul hqP hqC
            exact (hqne (Prod.ext hu.1 hu.2)).elim
          · simp [r, g, primeBandCoefficient, hqC]
        · simp [primeBandCoefficient, hqP]
      · intro hnot
        exact (hnot hmem).elim

theorem convolution_oneFull_twoPositiveTruncated_eq_zero_of_not_factors
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hnot : ¬ (HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ P₂ p) n ∧
      HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n)) :
    LSeries.convolution
        (primeBandCoefficient f P₁)
        (LSeries.convolution
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N)) n = 0 := by
  classical
  let g : ℕ → ℂ := primeBandCoefficient f (fun p ↦ ¬ P₁ p)
  let r : ℕ → ℂ := fun m ↦
    if HasPrimeFactor P₂ m ∧ HasPrimeFactor (fun p ↦ ¬ P₂ p) m then
      g m else 0
  have hgMul : IsMultiplicativeOnPositiveNat g :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul (fun p ↦ ¬ P₁ p)
  have hnested₂ :
      primeBandCoefficient g P₂ =
        primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p) :=
    primeBandCoefficient_nested f (fun p ↦ ¬ P₁ p) P₂
  have hnested₃ :
      primeBandCoefficient g (fun p ↦ ¬ P₂ p) =
        primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) :=
    primeBandCoefficient_nested f (fun p ↦ ¬ P₁ p) (fun p ↦ ¬ P₂ p)
  have hinner : ∀ m, 0 < m → m ≤ N →
      LSeries.convolution
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N) m =
        r m := by
    intro m hm hmN
    rw [← hnested₂, ← hnested₃]
    exact convolution_positivePrefixTruncate_primeBands_apply
      hgMul P₂ hm hmN
  rw [convolution_right_congr_up_to
    (primeBandCoefficient f P₁)
    (LSeries.convolution
      (positivePrefixTruncate
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
      (positivePrefixTruncate
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N))
    r hinner hn hnN]
  rw [LSeries.convolution_def]
  change (∑ q ∈ n.divisorsAntidiagonal,
    primeBandCoefficient f P₁ q.1 * r q.2) = 0
  let d := primeBandPart P₁ n
  let e := primeBandPart (fun p ↦ ¬ P₁ p) n
  have hne : n ≠ 0 := Nat.ne_of_gt hn
  have hde : d * e = n := primeBandPart_mul_compl P₁ hne
  have hd : PrimeSupported P₁ d := primeSupported_primeBandPart P₁ n
  have he : PrimeSupported (fun p ↦ ¬ P₁ p) e :=
    primeSupported_primeBandPart (fun p ↦ ¬ P₁ p) n
  have hmem : (d, e) ∈ n.divisorsAntidiagonal :=
    Nat.mem_divisorsAntidiagonal.mpr ⟨hde, hne⟩
  have hnotE : ¬ (HasPrimeFactor P₂ e ∧
      HasPrimeFactor (fun p ↦ ¬ P₂ p) e) := by
    rintro ⟨hP₂e, hCP₂e⟩
    apply hnot
    constructor
    · rw [hasPrimeFactor_iff] at hP₂e ⊢
      rcases hP₂e with ⟨p, hpe, hp₂⟩
      have hpdata := (prime_mem_primeFactors_primeBandPart_iff
        (fun p ↦ ¬ P₁ p) n p).1 hpe
      exact ⟨p, hpdata.1, hpdata.2, hp₂⟩
    · rw [hasPrimeFactor_iff] at hCP₂e ⊢
      rcases hCP₂e with ⟨p, hpe, hp₂⟩
      have hpdata := (prime_mem_primeFactors_primeBandPart_iff
        (fun p ↦ ¬ P₁ p) n p).1 hpe
      exact ⟨p, hpdata.1, hpdata.2, hp₂⟩
  rw [Finset.sum_eq_single (d, e)]
  · simp [r, hnotE]
  · intro q hq hqne
    by_cases hqP : PrimeSupported P₁ q.1
    · by_cases hqC : PrimeSupported (fun p ↦ ¬ P₁ p) q.2
      · have hqmul := (Nat.mem_divisorsAntidiagonal.mp hq).1
        have hu := eq_primeBandParts_of_mul_eq P₁ hqmul hqP hqC
        exact (hqne (Prod.ext hu.1 hu.2)).elim
      · simp [r, g, primeBandCoefficient, hqC]
    · simp [primeBandCoefficient, hqP]
  · intro hmissing
    exact (hmissing hmem).elim

/-- Complete coefficient formula for the finite three-band hybrid: it is
`f n` exactly on the two-band typical support and zero off that support. -/
theorem convolution_oneFull_twoPositiveTruncated_apply_ite
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    LSeries.convolution
        (primeBandCoefficient f P₁)
        (LSeries.convolution
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
          (positivePrefixTruncate
            (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N)) n =
      if HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ P₂ p) n ∧
          HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n then
        f n else 0 := by
  classical
  by_cases htyp : HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ P₂ p) n ∧
      HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n
  · rw [if_pos htyp]
    exact convolution_oneFull_twoPositiveTruncated_apply
      hmul P₁ P₂ hn hnN htyp.1 htyp.2
  · rw [if_neg htyp]
    exact convolution_oneFull_twoPositiveTruncated_eq_zero_of_not_factors
      hmul P₁ P₂ hn hnN htyp

/-- Analytic factorization of the one-full/two-truncated coefficient.
Unlike a truncation of a complete Euler product, this is an exact product
identity and contains no tail term. -/
theorem LSeries_convolution_oneFull_twoTruncated
    {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries
        (LSeries.convolution
          (primeBandCoefficient f P₁)
          (LSeries.convolution
            (prefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
            (prefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N))) s =
      LSeries (primeBandCoefficient f P₁) s *
        (LSeries
            (prefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N) s *
          LSeries
            (prefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N) s) := by
  have h₁ := primeBandCoefficient_LSeriesSummable hbound P₁ hs
  have h₂ := prefixTruncate_LSeriesSummable
    (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N s
  have h₃ := prefixTruncate_LSeriesSummable
    (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N s
  rw [LSeries_convolution' h₁ (h₂.convolution h₃),
    LSeries_convolution' h₂ h₃]

/-- Exact analytic product identity for the version with the two constant
terms removed.  Both auxiliary factors are finite Dirichlet polynomials;
only the selected prime band is a complete Euler factor. -/
theorem LSeries_convolution_oneFull_twoPositiveTruncated
    {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries
        (LSeries.convolution
          (primeBandCoefficient f P₁)
          (LSeries.convolution
            (positivePrefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
            (positivePrefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N))) s =
      LSeries (primeBandCoefficient f P₁) s *
        (LSeries
            (positivePrefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N) s *
          LSeries
            (positivePrefixTruncate
              (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N) s) := by
  have h₁ := primeBandCoefficient_LSeriesSummable hbound P₁ hs
  have h₂ := positivePrefixTruncate_LSeriesSummable
    (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N s
  have h₃ := positivePrefixTruncate_LSeriesSummable
    (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N s
  rw [LSeries_convolution' h₁ (h₂.convolution h₃),
    LSeries_convolution' h₂ h₃]

end

end Erdos67.MRHalaszBands
